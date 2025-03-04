# GT4Py - GridTools Framework
#
# Copyright (c) 2014-2024, ETH Zurich
# All rights reserved.
#
# Please, refer to the LICENSE file in the root directory.
# SPDX-License-Identifier: BSD-3-Clause

from __future__ import annotations

import dataclasses
import functools
import inspect

from gt4py.eve.extended_typing import Callable, Iterable, Optional, Union
from gt4py.next import common
from gt4py.next.ffront import fbuiltins
from gt4py.next.iterator import builtins, ir as itir
from gt4py.next.iterator.transforms import symbol_ref_utils, trace_shifts
from gt4py.next.iterator.type_system import type_specifications as it_ts
from gt4py.next.type_system import type_info, type_specifications as ts
from gt4py.next.utils import tree_map


@dataclasses.dataclass
class TypeSynthesizer:
    """
    Callable that given the type of the arguments to a function derives its return type.

    In case the function is a higher-order function the returned value is not a type, but another
    function type-synthesizer.

    In addition to the derivation of the return type a function type-synthesizer can perform checks
    on the argument types.

    The motivation for this class instead of a simple callable is to allow
     - isinstance checks to determine if an object is actually (meant to be) a type
       synthesizer and not just any callable.
     - writing simple type synthesizers without cluttering the signature with the additional
       offset_provider_type argument that is only needed by some.
    """

    type_synthesizer: Callable[..., TypeOrTypeSynthesizer]

    def __post_init__(self):
        if "offset_provider_type" not in inspect.signature(self.type_synthesizer).parameters:
            synthesizer = self.type_synthesizer
            self.type_synthesizer = lambda *args, offset_provider_type: synthesizer(*args)

    def __call__(
        self, *args: TypeOrTypeSynthesizer, offset_provider_type: common.OffsetProviderType
    ) -> TypeOrTypeSynthesizer:
        return self.type_synthesizer(*args, offset_provider_type=offset_provider_type)


TypeOrTypeSynthesizer = Union[ts.TypeSpec, TypeSynthesizer]

#: dictionary from name of a builtin to its type synthesizer
builtin_type_synthesizers: dict[str, TypeSynthesizer] = {}


def _is_derefable_iterator_type(it_type: it_ts.IteratorType, *, default: bool = True) -> bool:
    # for an iterator with unknown position we can not tell if it is derefable,
    # so we just return the default
    if it_type.position_dims == "unknown":
        return default
    return set(it_type.defined_dims).issubset(set(it_type.position_dims))


def _register_builtin_type_synthesizer(
    synthesizer: Optional[Callable[..., TypeOrTypeSynthesizer]] = None,
    *,
    fun_names: Optional[Iterable[str]] = None,
):
    if synthesizer is None:
        return functools.partial(_register_builtin_type_synthesizer, fun_names=fun_names)

    # store names in function object for better debuggability
    synthesizer.fun_names = fun_names or [synthesizer.__name__]  # type: ignore[attr-defined]
    for f in synthesizer.fun_names:  # type: ignore[attr-defined]
        builtin_type_synthesizers[f] = TypeSynthesizer(type_synthesizer=synthesizer)
    return synthesizer


@_register_builtin_type_synthesizer(
    fun_names=builtins.UNARY_MATH_NUMBER_BUILTINS | builtins.UNARY_MATH_FP_BUILTINS
)
def _(val: ts.ScalarType) -> ts.ScalarType:
    return val


@_register_builtin_type_synthesizer
def power(base: ts.ScalarType, exponent: ts.ScalarType) -> ts.ScalarType:
    return base


@_register_builtin_type_synthesizer(fun_names=builtins.BINARY_MATH_NUMBER_BUILTINS)
def _(lhs: ts.ScalarType, rhs: ts.ScalarType) -> ts.ScalarType:
    if isinstance(lhs, ts.DeferredType):
        return rhs
    if isinstance(rhs, ts.DeferredType):
        return lhs
    assert lhs == rhs
    return lhs


@_register_builtin_type_synthesizer(
    fun_names=builtins.UNARY_MATH_FP_PREDICATE_BUILTINS | builtins.UNARY_LOGICAL_BUILTINS
)
def _(arg: ts.ScalarType) -> ts.ScalarType:
    return ts.ScalarType(kind=ts.ScalarKind.BOOL)


@_register_builtin_type_synthesizer(
    fun_names=builtins.BINARY_MATH_COMPARISON_BUILTINS | builtins.BINARY_LOGICAL_BUILTINS
)
def _(lhs: ts.ScalarType, rhs: ts.ScalarType) -> ts.ScalarType | ts.TupleType:
    return ts.ScalarType(kind=ts.ScalarKind.BOOL)


@_register_builtin_type_synthesizer
def deref(it: it_ts.IteratorType | ts.DeferredType) -> ts.DataType | ts.DeferredType:
    if isinstance(it, ts.DeferredType):
        return ts.DeferredType(constraint=None)
    assert isinstance(it, it_ts.IteratorType)
    assert _is_derefable_iterator_type(it)
    return it.element_type


@_register_builtin_type_synthesizer
def can_deref(it: it_ts.IteratorType | ts.DeferredType) -> ts.ScalarType:
    assert isinstance(it, ts.DeferredType) or isinstance(it, it_ts.IteratorType)
    # note: We don't check if the iterator is derefable here as the iterator only needs to
    # to have a valid position. Consider a nested reduction, e.g.
    #  `reduce(plus, 0)(neighbors(V2Eₒ, (↑(λ(a) → reduce(plus, 0)(neighbors(E2Vₒ, a))))(it))`
    # When written using a `can_deref` we only care if the edge neighbor of the vertex of `it`
    # is valid, i.e. we want `can_deref(shift(V2Eₒ, i)(it))` to return true. But since `it` is an
    # iterator backed by a vertex field, the iterator is not derefable in the sense that
    # its position is a valid position of the backing field.
    # TODO(tehrengruber): Consider renaming can_deref to something that better reflects its
    #  meaning.
    return ts.ScalarType(kind=ts.ScalarKind.BOOL)


@_register_builtin_type_synthesizer
def if_(
    pred: ts.ScalarType | ts.DeferredType, true_branch: ts.DataType, false_branch: ts.DataType
) -> ts.DataType:
    if isinstance(true_branch, ts.TupleType) and isinstance(false_branch, ts.TupleType):
        return tree_map(
            collection_type=ts.TupleType,
            result_collection_constructor=lambda elts: ts.TupleType(types=[*elts]),
        )(functools.partial(if_, pred))(true_branch, false_branch)

    assert not isinstance(true_branch, ts.TupleType) and not isinstance(false_branch, ts.TupleType)
    assert isinstance(pred, ts.DeferredType) or (
        isinstance(pred, ts.ScalarType) and pred.kind == ts.ScalarKind.BOOL
    )
    # TODO(tehrengruber): Enable this or a similar check. In case the true- and false-branch are
    #  iterators defined on different positions this fails. For the GTFN backend we also don't
    #  want this, but for roundtrip it is totally fine.
    # assert true_branch == false_branch  # noqa: ERA001

    return true_branch


@_register_builtin_type_synthesizer
def make_const_list(scalar: ts.ScalarType) -> ts.ListType:
    assert isinstance(scalar, ts.ScalarType)
    return ts.ListType(element_type=scalar)


@_register_builtin_type_synthesizer
def list_get(index: ts.ScalarType | it_ts.OffsetLiteralType, list_: ts.ListType) -> ts.DataType:
    if isinstance(index, it_ts.OffsetLiteralType):
        assert isinstance(index.value, ts.ScalarType)
        index = index.value
    assert isinstance(index, ts.ScalarType) and type_info.is_integral(index)
    assert isinstance(list_, ts.ListType)
    return list_.element_type


@_register_builtin_type_synthesizer
def named_range(
    dim: ts.DimensionType, start: ts.ScalarType, stop: ts.ScalarType
) -> it_ts.NamedRangeType:
    assert isinstance(dim, ts.DimensionType)
    return it_ts.NamedRangeType(dim=dim.dim)


@_register_builtin_type_synthesizer(fun_names=["cartesian_domain", "unstructured_domain"])
def _(*args: it_ts.NamedRangeType) -> it_ts.DomainType:
    assert all(isinstance(arg, it_ts.NamedRangeType) for arg in args)
    return it_ts.DomainType(dims=[arg.dim for arg in args])


@_register_builtin_type_synthesizer
def make_tuple(*args: ts.DataType) -> ts.TupleType:
    return ts.TupleType(types=list(args))


@_register_builtin_type_synthesizer
def index(arg: ts.DimensionType) -> ts.FieldType:
    return ts.FieldType(
        dims=[arg.dim],
        dtype=ts.ScalarType(kind=getattr(ts.ScalarKind, builtins.INTEGER_INDEX_BUILTIN.upper())),
    )


@_register_builtin_type_synthesizer
def neighbors(offset_literal: it_ts.OffsetLiteralType, it: it_ts.IteratorType) -> ts.ListType:
    assert (
        isinstance(offset_literal, it_ts.OffsetLiteralType)
        and isinstance(offset_literal.value, common.Dimension)
        and offset_literal.value.kind == common.DimensionKind.LOCAL
    )
    assert isinstance(it, it_ts.IteratorType)
    return ts.ListType(element_type=it.element_type)


@_register_builtin_type_synthesizer
def lift(stencil: TypeSynthesizer) -> TypeSynthesizer:
    @TypeSynthesizer
    def apply_lift(
        *its: it_ts.IteratorType, offset_provider_type: common.OffsetProviderType
    ) -> it_ts.IteratorType:
        assert all(isinstance(it, it_ts.IteratorType) for it in its)
        stencil_args = [
            it_ts.IteratorType(
                # the positions are only known when we deref
                position_dims="unknown",
                defined_dims=it.defined_dims,
                element_type=it.element_type,
            )
            for it in its
        ]
        stencil_return_type = stencil(*stencil_args, offset_provider_type=offset_provider_type)
        assert isinstance(stencil_return_type, ts.DataType)

        position_dims = its[0].position_dims if its else []
        # we would need to look inside the stencil to find out where the resulting iterator
        # is defined, e.g. using trace shift, instead just use an empty list which means
        # everywhere
        defined_dims: list[common.Dimension] = []
        return it_ts.IteratorType(
            position_dims=position_dims, defined_dims=defined_dims, element_type=stencil_return_type
        )

    return apply_lift


def _collect_and_check_dimensions(input_: ts.TypeSpec) -> list[common.Dimension]:
    """
    Extracts dimensions from non-zero-dimensional field inputs and ensures they match.
    """
    all_input_dims = (
        type_info.primitive_constituents(input_)
        .if_isinstance(ts.FieldType)
        .getattr("dims")
        .filter(lambda dims: len(dims) > 0)
        .to_list()
    )
    if not all_input_dims:
        return []
    else:
        assert all(cur_input_dims == all_input_dims[0] for cur_input_dims in all_input_dims)
        return all_input_dims[0]


def _convert_as_fieldop_input_to_iterator(
    domain: it_ts.DomainType, input_: ts.TypeSpec
) -> it_ts.IteratorType:
    """
    Converts a field operation input into an iterator type, preserving its dimensions and data type.
    """
    input_dims = _collect_and_check_dimensions(input_)
    element_type: ts.DataType = type_info.apply_to_primitive_constituents(
        type_info.extract_dtype, input_
    )

    return it_ts.IteratorType(
        position_dims=domain.dims, defined_dims=input_dims, element_type=element_type
    )


def _handle_sparse_fields(input_: ts.FieldType | ts.TupleType | tuple[ts.FieldType, ts.TupleType]):
    """
    Processes sparse field inputs by removing LOCAL dimensions and converting the data type to ListType.
    """
    if isinstance(input_, (tuple, ts.TupleType)):
        return ts.TupleType(types=[_handle_sparse_fields(field) for field in input_])
    elif isinstance(input_, ts.FieldType):
        input_dims = _collect_and_check_dimensions(input_)
        element_type: ts.DataType = type_info.apply_to_primitive_constituents(
            type_info.extract_dtype, input_
        )

        defined_dims = [dim for dim in input_dims if dim.kind != common.DimensionKind.LOCAL]
        if any(dim.kind == common.DimensionKind.LOCAL for dim in input_dims):
            element_type = ts.ListType(element_type=element_type)

        return ts.FieldType(dims=defined_dims, dtype=element_type)
    elif isinstance(input_, ts.ScalarType):
        return input_
    else:
        raise TypeError(f"Unexpected field type: {type(input_)}")


@_register_builtin_type_synthesizer
def as_fieldop(
    stencil: TypeSynthesizer,
    domain: Optional[it_ts.DomainType] = None,
    *,
    offset_provider_type: common.OffsetProviderType,
) -> TypeSynthesizer:
    def _resolve_shift(
        input_dim: common.Dimension, shift_tuple: tuple[itir.OffsetLiteral, ...]
    ) -> common.Dimension | ts.DeferredType:
        """
        Resolves the final dimension by applying shifts from the given shift tuple.

        Iterates through the shift tuple, updating `input_dim` based on matching offsets.

        Parameters:
        - input_dim (common.Dimension): The initial dimension to resolve.
        - shift_tuple (tuple[itir.OffsetLiteral, ...]): A tuple of offset literals defining the shift.

        Returns:
        - common.Dimension: The resolved dimension or `input_dim` if no shift is applied.
        """

        final_target: common.Dimension = input_dim

        for off_literal in reversed(shift_tuple[::2]):
            offset_type = offset_provider_type[off_literal.value]  # type: ignore [index] # ensured by accessing only every second element
            if isinstance(offset_type, common.Dimension) and input_dim == offset_type:
                return offset_type  # No shift applied
            if isinstance(offset_type, (fbuiltins.FieldOffset, common.NeighborConnectivityType)):
                off_source = offset_type.codomain
                off_targets = offset_type.domain

                if input_dim == off_source:  # Check if input fits to offset
                    final_target = off_targets[0]
                    input_dim = off_targets[0]  # Update input_dim for next iteration
        return final_target

    @TypeSynthesizer
    def applied_as_fieldop(*fields) -> ts.FieldType | ts.DeferredType:
        if any(
            isinstance(el, ts.DeferredType)
            for f in fields
            for el in type_info.primitive_constituents(f)
        ):
            return ts.DeferredType(constraint=None)
        nonlocal domain

        new_fields = _handle_sparse_fields(fields)

        deduced_domain = None
        if offset_provider_type is not None:
            node = None
            if isinstance(stencil.node, itir.Expr):
                node = stencil.node
            elif isinstance(stencil.aliases[0], itir.Expr):
                node = stencil.aliases[0]
            if node is not None:
                referenced_fun_names = symbol_ref_utils.collect_symbol_refs(node)
                if referenced_fun_names:
                    assert domain is not None
                else:
                    output_dims = set()
                    for i, field in enumerate(new_fields):
                        input_dims = common.promote_dims(
                            *[field.dims if isinstance(field, ts.FieldType) else []]
                        )
                        shifts_results = trace_shifts.trace_stencil(
                            node, num_args=len(fields)
                        )  # TODO: access node differently?

                        for shift_tuple in shifts_results[
                            i
                        ]:  # Use shift tuple corresponding to the input field
                            for input_dim in input_dims:
                                output_dims.add(_resolve_shift(input_dim, shift_tuple))
                    output_dims_sorted = common.ordered_dims(output_dims)
                    deduced_domain = it_ts.DomainType(dims=list(output_dims_sorted))

        if deduced_domain:
            if domain:
                # assert list(output_dims_) == domain.dims TODO: add some check to compare with domain
                pass
            else:
                domain = deduced_domain

        if not domain:
            return ts.DeferredType(constraint=None)

        stencil_return = stencil(
            *(_convert_as_fieldop_input_to_iterator(domain, field) for field in new_fields),
            offset_provider_type=offset_provider_type,
        )

        assert isinstance(stencil_return, ts.DataType)

        return type_info.apply_to_primitive_constituents(
            lambda el_type: ts.FieldType(
                dims=domain.dims,
                dtype=el_type,
            ),
            stencil_return,
        )

    return applied_as_fieldop


@_register_builtin_type_synthesizer
def scan(
    scan_pass: TypeSynthesizer, direction: ts.ScalarType, init: ts.ScalarType
) -> TypeSynthesizer:
    assert isinstance(direction, ts.ScalarType) and direction.kind == ts.ScalarKind.BOOL

    @TypeSynthesizer
    def apply_scan(
        *its: it_ts.IteratorType, offset_provider_type: common.OffsetProviderType
    ) -> ts.DataType:
        result = scan_pass(init, *its, offset_provider_type=offset_provider_type)
        assert isinstance(result, ts.DataType)
        return result

    return apply_scan


@_register_builtin_type_synthesizer
def map_(op: TypeSynthesizer) -> TypeSynthesizer:
    @TypeSynthesizer
    def applied_map(
        *args: ts.ListType, offset_provider_type: common.OffsetProviderType
    ) -> ts.ListType:
        assert len(args) > 0
        assert all(isinstance(arg, ts.ListType) for arg in args)
        arg_el_types = [arg.element_type for arg in args]
        el_type = op(*arg_el_types, offset_provider_type=offset_provider_type)
        assert isinstance(el_type, ts.DataType)
        return ts.ListType(element_type=el_type)

    return applied_map


@_register_builtin_type_synthesizer
def reduce(op: TypeSynthesizer, init: ts.TypeSpec) -> TypeSynthesizer:
    @TypeSynthesizer
    def applied_reduce(*args: ts.ListType, offset_provider_type: common.OffsetProviderType):
        assert all(isinstance(arg, ts.ListType) for arg in args)
        return op(
            init, *(arg.element_type for arg in args), offset_provider_type=offset_provider_type
        )

    return applied_reduce


@_register_builtin_type_synthesizer
def shift(*offset_literals, offset_provider_type: common.OffsetProviderType) -> TypeSynthesizer:
    @TypeSynthesizer
    def apply_shift(
        it: it_ts.IteratorType | ts.DeferredType,
    ) -> it_ts.IteratorType | ts.DeferredType:
        if isinstance(it, ts.DeferredType):
            return ts.DeferredType(constraint=None)
        assert isinstance(it, it_ts.IteratorType)
        if it.position_dims == "unknown":  # nothing to do here
            return it
        new_position_dims: list[common.Dimension] | str
        if offset_provider_type:
            new_position_dims = [*it.position_dims]
            assert len(offset_literals) % 2 == 0
            for offset_axis, _ in zip(offset_literals[:-1:2], offset_literals[1::2], strict=True):
                assert isinstance(offset_axis, it_ts.OffsetLiteralType) and isinstance(
                    offset_axis.value, common.Dimension
                )
                type_ = offset_provider_type[offset_axis.value.value]
                if isinstance(type_, common.Dimension):
                    pass
                elif isinstance(type_, common.NeighborConnectivityType):
                    found = False
                    for i, dim in enumerate(new_position_dims):
                        if dim.value == type_.source_dim.value:
                            assert not found
                            new_position_dims[i] = type_.codomain
                            found = True
                    assert found
                else:
                    raise NotImplementedError(f"{type_} is not a supported Connectivity type.")
        else:
            # during re-inference we don't have an offset provider type
            new_position_dims = "unknown"
        return it_ts.IteratorType(
            position_dims=new_position_dims,
            defined_dims=it.defined_dims,
            element_type=it.element_type,
        )

    return apply_shift
