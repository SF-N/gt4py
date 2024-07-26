# GT4Py - GridTools Framework
#
# Copyright (c) 2014-2023, ETH Zurich
# All rights reserved.
#
# This file is part of the GT4Py project and the GridTools framework.
# GT4Py is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the
# Free Software Foundation, either version 3 of the License, or any later
# version. See the LICENSE.txt file at the top-level directory of this
# distribution for a copy of the license or check <https://www.gnu.org/licenses/>.
#
# SPDX-License-Identifier: GPL-3.0-or-later

from gt4py.eve import utils as eve_utils
from gt4py.eve.extended_typing import Dict, Tuple
from gt4py.next.common import Dimension
from gt4py.next.iterator import ir as itir
from gt4py.next.iterator.ir_utils import common_pattern_matcher as cpm, ir_makers as im
from gt4py.next.iterator.transforms.global_tmps import AUTO_DOMAIN, SymbolicDomain, domain_union
from gt4py.next.iterator.transforms.trace_shifts import TraceShifts


def _merge_domains(
    original_domains: Dict[str, SymbolicDomain], additional_domains: Dict[str, SymbolicDomain]
) -> Dict[str, SymbolicDomain]:
    new_domains = {**original_domains}
    for key, value in additional_domains.items():
        if key in original_domains:
            new_domains[key] = domain_union([original_domains[key], value])
        else:
            new_domains[key] = value

    return new_domains


# TODO: until TraceShifts directly supporty stencils we just wrap our expression into a dummy closure in this helper function.
def trace_shifts(stencil: itir.Expr, input_ids: list[str], domain: itir.Expr):
    node = itir.StencilClosure(
        stencil=stencil,
        inputs=[im.ref(id_) for id_ in input_ids],
        output=im.ref("__dummy"),
        domain=domain,
    )
    return TraceShifts.apply(node)


def infer_as_fieldop(
    applied_fieldop: itir.FunCall,
    input_domain: SymbolicDomain | itir.FunCall,
    offset_provider: Dict[str, Dimension],
) -> Tuple[itir.FunCall, Dict[str, SymbolicDomain]]:  # todo: test scan operator
    assert isinstance(applied_fieldop, itir.FunCall)
    assert cpm.is_call_to(applied_fieldop.fun, "as_fieldop")

    stencil, inputs = applied_fieldop.fun.args[0], applied_fieldop.args

    input_ids: list[str] = []
    accessed_domains: Dict[str, SymbolicDomain] = {}

    # Assign ids for all inputs to `as_fieldop`. `SymRef`s stay as is, nested `as_fieldop` get a
    # temporary id.
    tmp_uid_gen = eve_utils.UIDGenerator(prefix="__dom_inf")
    for in_field in inputs:
        if isinstance(in_field, itir.FunCall):
            id_ = tmp_uid_gen.sequential_id()
        else:
            assert isinstance(in_field, itir.SymRef)
            id_ = in_field.id
        input_ids.append(id_)
        accessed_domains[id_] = []

    if isinstance(input_domain, itir.FunCall):
        input_domain = SymbolicDomain.from_expr(input_domain)

    # Extract the shifts and translate the domains accordingly
    shifts_results = trace_shifts(stencil, input_ids, SymbolicDomain.as_expr(input_domain))

    for in_field_id in input_ids:
        shifts_list = shifts_results[in_field_id]

        new_domains = [
            SymbolicDomain.translate(input_domain, shift, offset_provider) for shift in shifts_list
        ]

        accessed_domains[in_field_id] = domain_union(new_domains)

    # Recursively infer domain of inputs and update domain arg of nested `as_fieldops`
    transformed_inputs = []
    for in_field_id, in_field in zip(input_ids, inputs):
        if isinstance(in_field, itir.FunCall):
            transformed_input, accessed_domains_tmp = infer_as_fieldop(
                in_field, accessed_domains[in_field_id], offset_provider
            )
            transformed_inputs.append(transformed_input)

            # Merge accessed_domains and accessed_domains_tmp
            accessed_domains = _merge_domains(accessed_domains, accessed_domains_tmp)
        else:
            assert isinstance(in_field, itir.SymRef)
            transformed_inputs.append(in_field)

    transformed_call = im.as_fieldop(stencil, SymbolicDomain.as_expr(input_domain))(
        *transformed_inputs
    )

    accessed_domains_without_tmp = {
        k: v for k, v in accessed_domains.items() if not k.startswith(tmp_uid_gen.prefix)
    }

    return transformed_call, accessed_domains_without_tmp


def infer_let(  # Todo generaize for nested lets
    applied_let: itir.FunCall,
    input_domain: SymbolicDomain | itir.FunCall,
    offset_provider: Dict[str, Dimension],
) -> Tuple[itir.FunCall, Dict[str, SymbolicDomain]]:
    assert isinstance(applied_let, itir.FunCall) and isinstance(applied_let.fun, itir.Lambda)
    accessed_domains : Dict[str, SymbolicDomain] = {}
    # Recursively infer domain of inputs and update domain arg of nested `let`s
    transformed_calls_expr = []
    if isinstance(applied_let.fun.expr.fun, itir.Lambda): # Todo nested case
        actual_call, actual_domains = infer_let(
            applied_let.fun.expr, input_domain, offset_provider
        )
        transformed_calls_expr.append(actual_call)
    else:
        actual_domain = input_domain
        if cpm.is_call_to(applied_let.fun.expr.fun, "as_fieldop"):
            transformed_calls_expr, accessed_domains_expr = infer_as_fieldop(
                applied_let.fun.expr, actual_domain, offset_provider
            )
        transformed_calls_args: list(itir.FunCall) = []
        for arg in applied_let.args:
            if cpm.is_call_to(arg.fun, "as_fieldop"):
                transformed_calls_arg, accessed_domains_arg = infer_as_fieldop(
                    arg,
                    accessed_domains_expr[applied_let.fun.params[0].id],
                    offset_provider
                )
                transformed_calls_args.append(transformed_calls_arg)
                accessed_domains = _merge_domains(accessed_domains, accessed_domains_arg)
        transformed_call = im.let(*Tuple((str(param.id), call) for param, call in zip(applied_let.fun.params,transformed_calls_args)))(
            transformed_calls_expr
        )

        return transformed_call, accessed_domains

# def infer_let(  # Todo generaize for nested lets
#     applied_let: itir.FunCall,
#     input_domain: SymbolicDomain | itir.FunCall,
#     offset_provider: Dict[str, Dimension],
# ) -> Tuple[itir.FunCall, Dict[str, SymbolicDomain]]:
#     assert isinstance(applied_let, itir.FunCall) and isinstance(applied_let.fun, itir.Lambda)
#     accessed_domains : Dict[str, SymbolicDomain] = {}
#     if isinstance(applied_let.fun.expr.fun, itir.Lambda): # Todo nested case
#         return
#     else:
#         if cpm.is_call_to(applied_let.fun.expr.fun, "as_fieldop"):
#             transformed_calls_expr, accessed_domains_expr = infer_as_fieldop(
#                 applied_let.fun.expr, input_domain, offset_provider
#             )
#         transformed_calls_args: list(itir.FunCall) = []
#         for arg in applied_let.args:
#             if cpm.is_call_to(arg.fun, "as_fieldop"):
#                 transformed_calls_arg, accessed_domains_arg = infer_as_fieldop(
#                     arg,
#                     accessed_domains_expr[applied_let.fun.params[0].id],
#                     offset_provider
#                 )
#                 transformed_calls_args.append(transformed_calls_arg)
#                 accessed_domains = _merge_domains(accessed_domains, accessed_domains_arg)
#         transformed_call = im.let(*Tuple((str(param.id), call) for param, call in zip(applied_let.fun.params,transformed_calls_args)))(
#             transformed_calls_expr
#         )
#
#         return transformed_call, accessed_domains


def _validate_temporary_usage(body: list[itir.SetAt], temporaries: list[str]):
    # TODO: stmt.target can be an expr, e.g. make_tuple
    tmp_assignments = [stmt.target.id for stmt in body if stmt.target.id in temporaries]
    if len(tmp_assignments) != len(set(tmp_assignments)):
        raise ValueError("Temporaries can only be used once within a program.")


def infer_program(
    program: itir.Program,
    offset_provider: Dict[str, Dimension],
) -> itir.Program:
    accessed_domains: dict[str, SymbolicDomain] = {}
    transformed_set_ats: list[itir.SetAt] = []

    temporaries: list[str] = [tmp.id for tmp in program.declarations]

    _validate_temporary_usage(program.body, temporaries)

    for set_at in reversed(program.body):
        assert isinstance(set_at, itir.SetAt)
        assert isinstance(set_at.expr, itir.FunCall)
        assert cpm.is_call_to(set_at.expr.fun, "as_fieldop")

        if set_at.target.id in temporaries:
            # ignore temporaries as their domain is the `AUTO_DOMAIN` placeholder
            assert set_at.domain == AUTO_DOMAIN
        else:
            accessed_domains[set_at.target.id] = SymbolicDomain.from_expr(set_at.domain)

        actual_call, current_accessed_domains = infer_as_fieldop(
            set_at.expr, accessed_domains[set_at.target.id], offset_provider
        )
        transformed_set_ats.insert(
            0,
            itir.SetAt(expr=actual_call, domain=actual_call.fun.args[1], target=set_at.target),
        )

        for field in current_accessed_domains:
            if field in accessed_domains:
                # multiple accesses to the same field -> compute union of accessed domains
                if field in temporaries:
                    accessed_domains[field] = domain_union(
                        [accessed_domains[field], current_accessed_domains[field]]
                    )
                else:
                    # TODO(tehrengruber): if domain_ref is an external field the domain must
                    #  already be larger. This should be checked, but would require additions
                    #  to the IR.
                    pass
            else:
                accessed_domains[field] = current_accessed_domains[field]

    new_declarations = program.declarations
    for temporary in new_declarations:
        temporary.domain = SymbolicDomain.as_expr(accessed_domains[temporary.id])

    return itir.Program(
        id=program.id,
        function_definitions=program.function_definitions,
        params=program.params,
        declarations=new_declarations,
        body=transformed_set_ats,
    )
