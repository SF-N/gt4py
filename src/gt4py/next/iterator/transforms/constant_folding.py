# GT4Py - GridTools Framework
#
# Copyright (c) 2014-2024, ETH Zurich
# All rights reserved.
#
# Please, refer to the LICENSE file in the root directory.
# SPDX-License-Identifier: BSD-3-Clause

from __future__ import annotations

import dataclasses
import enum
import functools
import operator
from typing import Optional

from gt4py import eve
from gt4py.next.iterator import builtins, embedded, ir
from gt4py.next.iterator.ir_utils import common_pattern_matcher as cpm, ir_makers as im
from gt4py.next.iterator.transforms import fixed_point_transformation


@dataclasses.dataclass(frozen=True, kw_only=True)
class ConstantFolding(
    fixed_point_transformation.FixedPointTransformation, eve.PreserveLocationVisitor
):
    PRESERVED_ANNEX_ATTRS = (
        "type",
        "domain",
    )

    class Transformation(enum.Flag):
        # `literal, symref` -> `symref, literal`, prerequisite for FOLD_FUNCALL_LITERAL, FOLD_NEUTRAL_OP
        # `literal, funcall` -> `funcall, literal`, prerequisite for FOLD_FUNCALL_LITERAL, FOLD_NEUTRAL_OP
        # `funcall, op` -> `op, funcall` for s[0] + (s[0] + 1), prerequisite for FOLD_MIN_MAX_PLUS
        CANONICALIZE_OP_FUNCALL_SYMREF_LITERAL = enum.auto()

        # `a - b` -> `a + (-b)`, prerequisite for FOLD_MIN_MAX_PLUS
        CANONICALIZE_MINUS = enum.auto()

        # `maximum(a, maximum(...))` -> `maximum(maximum(...), a)`, prerequisite for FOLD_MIN_MAX
        CANONICALIZE_MIN_MAX = enum.auto()

        # `(a + 1) + 1` -> `a + (1 + 1)`
        FOLD_FUNCALL_LITERAL = enum.auto()

        # `maximum(maximum(a, 1), a)` -> `maximum(a, 1)`
        # `maximum(maximum(a, 1), 1)` -> `maximum(a, 1)`
        FOLD_MIN_MAX = enum.auto()

        # `maximum(plus(a, 1), a)` -> `plus(a, 1)`
        # `maximum(plus(a, 1), plus(a, -1))` -> `plus(a, maximum(1, -1))`
        FOLD_MIN_MAX_PLUS = enum.auto()

        # `a + 0` -> `a`, `a * 1` -> `a`
        FOLD_NEUTRAL_OP = enum.auto()

        # `1 + 1` -> `2`
        FOLD_ARITHMETIC_BUILTINS = enum.auto()

        # `minimum(a, a)` -> `a`
        FOLD_MIN_MAX_LITERALS = enum.auto()

        # `if_(True, true_branch, false_branch)` -> `true_branch`
        FOLD_IF = enum.auto()

        @classmethod
        def all(self) -> ConstantFolding.Transformation:
            return functools.reduce(operator.or_, self.__members__.values())

    enabled_transformations: Transformation = Transformation.all()  # noqa: RUF009 [function-call-in-dataclass-default-argument]

    @classmethod
    def apply(cls, node: ir.Node) -> ir.Node:
        node = cls().visit(node)
        return node

    def transform_canonicalize_op_funcall_symref_literal(
        self, node: ir.FunCall, **kwargs
    ) -> Optional[ir.Node]:
        # `literal, symref` -> `symref, literal`, prerequisite for FOLD_FUNCALL_LITERAL, FOLD_NEUTRAL_OP
        # `literal, funcall` -> `funcall, literal`, prerequisite for FOLD_FUNCALL_LITERAL, FOLD_NEUTRAL_OP
        # `funcall, op` -> `op, funcall` for s[0] + (s[0] + 1), prerequisite for FOLD_MIN_MAX_PLUS
        if cpm.is_call_to(node, ("plus", "multiplies", "minimum", "maximum")):
            if (
                isinstance(node.args[0], ir.Literal) and not isinstance(node.args[1], ir.Literal)
            ) or (
                (not cpm.is_call_to(node.args[0], ("plus", "multiplies", "minimum", "maximum")))
                and cpm.is_call_to(node.args[1], ("plus", "multiplies", "minimum", "maximum"))
            ):
                return im.call(node.fun)(node.args[1], node.args[0])
        return None

    def transform_canonicalize_minus(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `a - b` -> `a + (-b)`, prerequisite for FOLD_MIN_MAX_PLUS
        if cpm.is_call_to(node, "minus"):
            return im.plus(node.args[0], self.fp_transform(im.call("neg")(node.args[1])))
        return None

    def transform_canonicalize_min_max(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `maximum(a, maximum(...))` -> `maximum(maximum(...), a)`, prerequisite for FOLD_MIN_MAX
        if cpm.is_call_to(node, ("maximum", "minimum")):
            op = node.fun.id  # type: ignore[attr-defined] # assured by if above
            if cpm.is_call_to(node.args[1], op) and not cpm.is_call_to(node.args[0], op):
                return im.call(op)(node.args[1], node.args[0])
        return None

    def transform_fold_funcall_literal(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `(a + 1) + 1` -> `a + (1 + 1)`
        if cpm.is_call_to(node, "plus"):
            if cpm.is_call_to(node.args[0], "plus") and isinstance(node.args[1], ir.Literal):
                fun_call, literal = node.args
                if isinstance(fun_call.args[0], (ir.SymRef, ir.FunCall)) and isinstance(  # type: ignore[attr-defined] # assured by if above
                    fun_call.args[1],  # type: ignore[attr-defined] # assured by if above
                    ir.Literal,
                ):
                    return im.plus(
                        fun_call.args[0],  # type: ignore[attr-defined] # assured by if above
                        self.fp_transform(im.plus(fun_call.args[1], literal)),  # type: ignore[attr-defined] # assured by if above
                    )
        return None

    def transform_fold_min_max(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `maximum(maximum(a, 1), a)` -> `maximum(a, 1)`
        # `maximum(maximum(a, 1), 1)` -> `maximum(a, 1)`
        if cpm.is_call_to(node, ("minimum", "maximum")):
            op = node.fun.id  # type: ignore[attr-defined] # assured by if above
            if cpm.is_call_to(node.args[0], op):
                fun_call, arg1 = node.args
                if arg1 in fun_call.args:  # type: ignore[attr-defined] # assured by if above
                    return fun_call
        return None

    def transform_fold_min_max_plus(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        if (
            isinstance(node, ir.FunCall)
            and isinstance(node.fun, ir.SymRef)
            and cpm.is_call_to(node, ("minimum", "maximum"))
        ):
            arg0, arg1 = node.args
            # `maximum(plus(a, 1), a)` -> `plus(a, 1)`
            if cpm.is_call_to(arg0, "plus"):
                if arg0.args[0] == arg1:
                    return im.plus(
                        arg0.args[0], self.fp_transform(im.call(node.fun.id)(arg0.args[1], 0))
                    )
            # `maximum(plus(a, 1), plus(a, -1))` -> `plus(a, maximum(1, -1))`
            if cpm.is_call_to(arg0, "plus") and cpm.is_call_to(arg1, "plus"):
                if arg0.args[0] == arg1.args[0]:
                    return im.plus(
                        arg0.args[0],
                        self.fp_transform(im.call(node.fun.id)(arg0.args[1], arg1.args[1])),
                    )

        return None

    def transform_fold_neutral_op(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `a + 0` -> `a`, `a * 1` -> `a`
        if (
            cpm.is_call_to(node, "plus")
            and isinstance(node.args[1], ir.Literal)
            and node.args[1].value.isdigit()
            and int(node.args[1].value) == 0
        ) or (
            cpm.is_call_to(node, "multiplies")
            and isinstance(node.args[1], ir.Literal)
            and node.args[1].value.isdigit()
            and int(node.args[1].value) == 1
        ):
            return node.args[0]
        return None

    def transform_fold_arithmetic_builtins(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `1 + 1` -> `2`
        if (
            isinstance(node, ir.FunCall)
            and isinstance(node.fun, ir.SymRef)
            and len(node.args) > 0
            and all(isinstance(arg, ir.Literal) for arg in node.args)
        ):
            try:
                if node.fun.id in builtins.ARITHMETIC_BUILTINS:
                    fun = getattr(embedded, str(node.fun.id))
                    arg_values = [
                        getattr(embedded, str(arg.type))(arg.value)  # type: ignore[attr-defined] # arg type already established in if condition
                        for arg in node.args
                    ]
                    return im.literal_from_value(fun(*arg_values))
            except ValueError:
                pass  # happens for inf and neginf
        return None

    def transform_fold_min_max_literals(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `minimum(a, a)` -> `a`
        if cpm.is_call_to(node, ("minimum", "maximum")):
            if node.args[0] == node.args[1]:
                return node.args[0]
        return None

    def transform_fold_if(self, node: ir.FunCall, **kwargs) -> Optional[ir.Node]:
        # `if_(True, true_branch, false_branch)` -> `true_branch`
        if cpm.is_call_to(node, "if_") and isinstance(node.args[0], ir.Literal):
            if node.args[0].value == "True":
                return node.args[1]
            else:
                return node.args[2]
        return None
