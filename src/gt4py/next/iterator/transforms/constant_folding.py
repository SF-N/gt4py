# GT4Py - GridTools Framework
#
# Copyright (c) 2014-2024, ETH Zurich
# All rights reserved.
#
# Please, refer to the LICENSE file in the root directory.
# SPDX-License-Identifier: BSD-3-Clause

from gt4py.eve import NodeTranslator, PreserveLocationVisitor
from gt4py.next.iterator import embedded, ir
from gt4py.next.iterator.ir_utils import common_pattern_matcher as cpm, ir_makers as im


class ConstantFolding(PreserveLocationVisitor, NodeTranslator):
    @classmethod
    def apply(cls, node: ir.Node) -> ir.Node:
        return cls().visit(node)

    def visit_FunCall(self, node: ir.FunCall):
        # visit depth-first such that nested constant expressions (e.g. `(1+2)+3`) are properly folded
        new_node = self.generic_visit(node)

        # `minimum(a, a)` -> `a`
        if cpm.is_call_to(new_node, ("minimum", "maximum")):
            if new_node.args[0] == new_node.args[1]:
                new_node = new_node.args[0]
        # `maximum(maximum(__out_size_1, 1), maximum(1, __out_size_1))` -> `maximum(__out_size_1, 1)`
        if cpm.is_call_to(new_node, ("minimum", "maximum")):
            if all(cpm.is_call_to(arg, "maximum") for arg in new_node.args) or all(
                cpm.is_call_to(arg, "minimum") for arg in new_node.args
            ):
                if (
                    new_node.args[0].args[0] == new_node.args[1].args[1]
                    and new_node.args[0].args[1] == new_node.args[1].args[0]
                ):
                    new_node = new_node.args[0]
        # `maximum(maximum(__out_size_1, 1), __out_size_1)` -> `maximum(__out_size_1, 1)`
        if cpm.is_call_to(new_node, ("minimum", "maximum")):
            match = False
            if isinstance(new_node.args[0], ir.FunCall) and isinstance(
                new_node.args[1], (ir.Literal, ir.SymRef)
            ):
                fun_call, sym_lit = new_node.args
                match = True
            elif isinstance(new_node.args[0], (ir.Literal, ir.SymRef)) and isinstance(
                new_node.args[1], ir.FunCall
            ):
                match = True
                sym_lit, fun_call = new_node.args
            if match and cpm.is_call_to(fun_call, ("maximum", "minimum")):
                if isinstance(fun_call.args[0], ir.SymRef) and isinstance(
                    fun_call.args[1], ir.Literal
                ):
                    if sym_lit == fun_call.args[0]:
                        new_node = im.call(fun_call.fun.id)(sym_lit, fun_call.args[1])
                    if sym_lit == fun_call.args[1]:
                        new_node = im.call(fun_call.fun.id)(fun_call.args[0], sym_lit)
                if isinstance(fun_call.args[0], ir.Literal) and isinstance(
                    fun_call.args[1], ir.SymRef
                ):
                    if sym_lit == fun_call.args[0]:
                        new_node = im.call(fun_call.fun.id)(fun_call.args[1], sym_lit)
                    if sym_lit == fun_call.args[1]:
                        new_node = im.call(fun_call.fun.id)(sym_lit, fun_call.args[0])
        # `maximum(plus(__out_size_1, 1), minus(__out_size_1, 1))` -> `plus(__out_size_1, 1)`
        if cpm.is_call_to(new_node, ("minimum", "maximum")):
            if all(cpm.is_call_to(arg, ("plus", "minus")) for arg in new_node.args):
                if new_node.args[0].args[0] == new_node.args[1].args[0]:
                    new_node = im.plus(
                        new_node.args[0].args[0],
                        self.visit(
                            im.call(new_node.fun.id)(
                                im.call(new_node.args[0].fun.id)(0, new_node.args[0].args[1]),
                                im.call(new_node.args[1].fun.id)(0, new_node.args[1].args[1]),
                            )
                        ),
                    )
            # `maximum(plus(__out_size_1, 1), __out_size_1)` -> `plus(__out_size_1, 1)`
            match = False
            if isinstance(new_node.args[0], ir.FunCall) and isinstance(new_node.args[1], ir.SymRef):
                fun_call, sym_ref = new_node.args
                match = True
            elif isinstance(new_node.args[0], ir.SymRef) and isinstance(
                new_node.args[1], ir.FunCall
            ):
                match = True
                sym_ref, fun_call = new_node.args
            if match and fun_call.fun.id in ["plus", "minus"]:
                if fun_call.args[0] == sym_ref:
                    if new_node.fun.id == "minimum":
                        if fun_call.fun.id == "plus":
                            new_node = sym_ref if int(fun_call.args[1].value) >= 0 else fun_call
                        elif fun_call.fun.id == "minus":
                            new_node = fun_call if int(fun_call.args[1].value) > 0 else sym_ref
                    elif new_node.fun.id == "maximum":
                        if fun_call.fun.id == "plus":
                            new_node = fun_call if int(fun_call.args[1].value) > 0 else sym_ref
                        elif fun_call.fun.id == "minus":
                            new_node = sym_ref if int(fun_call.args[1].value) >= 0 else fun_call
        # `if_(True, true_branch, false_branch)` -> `true_branch`
        if cpm.is_call_to(new_node, "if_") and isinstance(new_node.args[0], ir.Literal):
            if new_node.args[0].value == "True":
                new_node = new_node.args[1]
            else:
                new_node = new_node.args[2]
        # `1 + 1` -> `2`
        if (
            isinstance(new_node, ir.FunCall)
            and isinstance(new_node.fun, ir.SymRef)
            and len(new_node.args) > 0
            and all(isinstance(arg, ir.Literal) for arg in new_node.args)
        ):
            try:
                if new_node.fun.id in ir.ARITHMETIC_BUILTINS:
                    fun = getattr(embedded, str(new_node.fun.id))
                    arg_values = [
                        getattr(embedded, str(arg.type))(arg.value)
                        # type: ignore[attr-defined] # arg type already established in if condition
                        for arg in new_node.args
                    ]
                    new_node = im.literal_from_value(fun(*arg_values))
            except ValueError:
                pass  # happens for inf and neginf
        # `__out_size_1 + 1 + 1` -> `__out_size_1 + 2`
        if cpm.is_call_to(new_node, ("plus", "minus")):
            match = False
            if isinstance(new_node.args[0], ir.FunCall) and isinstance(
                new_node.args[1], ir.Literal
            ):
                fun_call, literal = new_node.args
                match = True
            elif isinstance(new_node.args[0], ir.Literal) and isinstance(
                new_node.args[1], ir.FunCall
            ):
                match = True
                literal, fun_call = new_node.args
            if match and cpm.is_call_to(fun_call, ("plus", "minus")):
                fun_call_match = False
                if isinstance(fun_call.args[0], ir.SymRef) and isinstance(
                    fun_call.args[1], ir.Literal
                ):
                    fun_call_sym_ref, fun_call_literal = fun_call.args
                    fun_call_match = True
                elif isinstance(fun_call.args[0], ir.Literal) and isinstance(
                    fun_call.args[1], ir.SymRef
                ):
                    fun_call_literal, fun_call_sym_ref = new_node.args
                    fun_call_match = True
                if fun_call_match:
                    new_node = im.plus(
                        fun_call_sym_ref,
                        self.visit(im.call(new_node.fun.id)(fun_call_literal, literal)),
                    )
        return new_node
