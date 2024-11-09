# GT4Py - GridTools Framework
#
# Copyright (c) 2014-2024, ETH Zurich
# All rights reserved.
#
# Please, refer to the LICENSE file in the root directory.
# SPDX-License-Identifier: BSD-3-Clause

"""Contains definition of test-exclusion matrices, see ADR 15."""

import dataclasses
import enum
import importlib
from typing import Final, Optional, Protocol

import pytest

from gt4py.next import allocators as next_allocators, backend as next_backend


# Skip definitions
XFAIL = pytest.xfail
SKIP = pytest.skip


# Program processors
class _PythonObjectIdMixin:
    # Only useful for classes inheriting from (str, enum.Enum)
    def __str__(self) -> str:
        assert isinstance(self.value, str)
        return self.value

    def load(self) -> object:
        *mods, obj = self.value.split(".")
        globs = {"_m": importlib.import_module(".".join(mods))}
        obj = eval(f"_m.{obj}", globs)
        return obj

    def short_id(self, num_components: int = 2) -> str:
        return ".".join(self.value.split(".")[-num_components:])


class ProgramBackendId(_PythonObjectIdMixin, str, enum.Enum):
    GTFN_CPU = "gt4py.next.program_processors.runners.gtfn.run_gtfn"
    GTFN_CPU_IMPERATIVE = "gt4py.next.program_processors.runners.gtfn.run_gtfn_imperative"
    GTFN_CPU_NO_TRANSFORMS = "gt4py.next.program_processors.runners.gtfn.run_gtfn_no_transforms"
    GTFN_GPU = "gt4py.next.program_processors.runners.gtfn.run_gtfn_gpu"
    ROUNDTRIP = "gt4py.next.program_processors.runners.roundtrip.default"
    ROUNDTRIP_NO_TRANSFORMS = "gt4py.next.program_processors.runners.roundtrip.no_transforms"
    GTIR_EMBEDDED = "gt4py.next.program_processors.runners.roundtrip.gtir"
    ROUNDTRIP_WITH_TEMPORARIES = "gt4py.next.program_processors.runners.roundtrip.with_temporaries"
    DOUBLE_ROUNDTRIP = "gt4py.next.program_processors.runners.double_roundtrip.backend"


@dataclasses.dataclass(frozen=True)
class EmbeddedDummyBackend:
    allocator: next_allocators.FieldBufferAllocatorProtocol


numpy_execution = EmbeddedDummyBackend(next_allocators.StandardCPUFieldBufferAllocator())
cupy_execution = EmbeddedDummyBackend(next_allocators.StandardGPUFieldBufferAllocator())


class EmbeddedIds(_PythonObjectIdMixin, str, enum.Enum):
    NUMPY_EXECUTION = "next_tests.definitions.numpy_execution"
    CUPY_EXECUTION = "next_tests.definitions.cupy_execution"


class OptionalProgramBackendId(_PythonObjectIdMixin, str, enum.Enum):
    DACE_CPU = "gt4py.next.program_processors.runners.dace.itir_cpu"
    DACE_GPU = "gt4py.next.program_processors.runners.dace.itir_gpu"
    GTIR_DACE_CPU = "gt4py.next.program_processors.runners.dace.gtir_cpu"
    GTIR_DACE_GPU = "gt4py.next.program_processors.runners.dace.gtir_gpu"


class ProgramFormatterId(_PythonObjectIdMixin, str, enum.Enum):
    GTFN_CPP_FORMATTER = "gt4py.next.program_processors.formatters.gtfn.format_cpp"
    ITIR_PRETTY_PRINTER = (
        "gt4py.next.program_processors.formatters.pretty_print.format_itir_and_check"
    )
    LISP_FORMATTER = "gt4py.next.program_processors.formatters.lisp.format_lisp"


# Test markers
# Special marker that skips all tests. This is not a regular pytest marker, but handled explicitly
# to avoid needing to mark all tests.
ALL = "all"
REQUIRES_ATLAS = "requires_atlas"
# TODO(havogt): Remove, skipped during refactoring to GTIR
STARTS_FROM_GTIR_PROGRAM = "starts_from_gtir_program"
USES_APPLIED_SHIFTS = "uses_applied_shifts"
USES_CONSTANT_FIELDS = "uses_constant_fields"
USES_DYNAMIC_OFFSETS = "uses_dynamic_offsets"
USES_FLOORDIV = "uses_floordiv"
USES_IF_STMTS = "uses_if_stmts"
USES_IR_IF_STMTS = "uses_ir_if_stmts"
USES_INDEX_FIELDS = "uses_index_fields"
USES_LIFT_EXPRESSIONS = "uses_lift_expressions"
USES_NEGATIVE_MODULO = "uses_negative_modulo"
USES_ORIGIN = "uses_origin"
USES_REDUCTION_OVER_LIFT_EXPRESSIONS = "uses_reduction_over_lift_expressions"
USES_SCAN = "uses_scan"
USES_SCAN_IN_FIELD_OPERATOR = "uses_scan_in_field_operator"
USES_SCAN_WITHOUT_FIELD_ARGS = "uses_scan_without_field_args"
USES_SCAN_NESTED = "uses_scan_nested"
USES_SCAN_REQUIRING_PROJECTOR = "uses_scan_requiring_projector"
USES_SPARSE_FIELDS = "uses_sparse_fields"
USES_SPARSE_FIELDS_AS_OUTPUT = "uses_sparse_fields_as_output"
USES_REDUCTION_WITH_ONLY_SPARSE_FIELDS = "uses_reduction_with_only_sparse_fields"
USES_STRIDED_NEIGHBOR_OFFSET = "uses_strided_neighbor_offset"
USES_TUPLE_ARGS = "uses_tuple_args"
USES_TUPLE_RETURNS = "uses_tuple_returns"
USES_ZERO_DIMENSIONAL_FIELDS = "uses_zero_dimensional_fields"
USES_CARTESIAN_SHIFT = "uses_cartesian_shift"
USES_UNSTRUCTURED_SHIFT = "uses_unstructured_shift"
USES_MAX_OVER = "uses_max_over"
USES_MESH_WITH_SKIP_VALUES = "uses_mesh_with_skip_values"
USES_SCALAR_IN_DOMAIN_AND_FO = "uses_scalar_in_domain_and_fo"
CHECKS_SPECIFIC_ERROR = "checks_specific_error"
USES_HALF_PRECISION = "uses_half_precision"
USES_INDEX_BUILTIN = "uses_index_builtin"

# Skip messages (available format keys: 'marker', 'backend')
UNSUPPORTED_MESSAGE = "'{marker}' tests not supported by '{backend}' backend"
BINDINGS_UNSUPPORTED_MESSAGE = "'{marker}' not supported by '{backend}' bindings"
REDUCTION_WITH_ONLY_SPARSE_FIELDS_MESSAGE = (
    "We cannot unroll a reduction on a sparse field only (not clear if it is legal ITIR)"
)
# Common list of feature markers to skip
COMMON_SKIP_TEST_LIST = [
    (REQUIRES_ATLAS, XFAIL, BINDINGS_UNSUPPORTED_MESSAGE),
    (USES_DYNAMIC_OFFSETS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_APPLIED_SHIFTS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_NEGATIVE_MODULO, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_REDUCTION_WITH_ONLY_SPARSE_FIELDS, XFAIL, REDUCTION_WITH_ONLY_SPARSE_FIELDS_MESSAGE),
    (USES_SPARSE_FIELDS_AS_OUTPUT, XFAIL, UNSUPPORTED_MESSAGE),
]
DACE_SKIP_TEST_LIST = COMMON_SKIP_TEST_LIST + [
    (USES_IR_IF_STMTS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_SCALAR_IN_DOMAIN_AND_FO, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_INDEX_FIELDS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_LIFT_EXPRESSIONS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_ORIGIN, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_STRIDED_NEIGHBOR_OFFSET, XFAIL, BINDINGS_UNSUPPORTED_MESSAGE),
    (USES_TUPLE_ARGS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_TUPLE_RETURNS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_ZERO_DIMENSIONAL_FIELDS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_HALF_PRECISION, XFAIL, UNSUPPORTED_MESSAGE),
]
# Markers to skip because of missing features in the domain inference
DOMAIN_INFERENCE_SKIP_LIST = [
    (USES_DYNAMIC_OFFSETS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_STRIDED_NEIGHBOR_OFFSET, XFAIL, UNSUPPORTED_MESSAGE),
]
DACE_SKIP_TEST_LIST = (
    COMMON_SKIP_TEST_LIST
    + DOMAIN_INFERENCE_SKIP_LIST
    + [
        (USES_IF_STMTS, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_SCAN_IN_FIELD_OPERATOR, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_IR_IF_STMTS, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_SCALAR_IN_DOMAIN_AND_FO, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_INDEX_FIELDS, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_LIFT_EXPRESSIONS, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_ORIGIN, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_STRIDED_NEIGHBOR_OFFSET, XFAIL, BINDINGS_UNSUPPORTED_MESSAGE),
        (USES_TUPLE_ARGS, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_TUPLE_RETURNS, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_ZERO_DIMENSIONAL_FIELDS, XFAIL, UNSUPPORTED_MESSAGE),
        (STARTS_FROM_GTIR_PROGRAM, SKIP, UNSUPPORTED_MESSAGE),
    ]
)
GTIR_DACE_SKIP_TEST_LIST = DOMAIN_INFERENCE_SKIP_LIST + [
    (USES_DYNAMIC_OFFSETS, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_INDEX_BUILTIN, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_NEGATIVE_MODULO, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_SCAN, XFAIL, UNSUPPORTED_MESSAGE),
    (USES_SPARSE_FIELDS_AS_OUTPUT, XFAIL, UNSUPPORTED_MESSAGE),
]
EMBEDDED_SKIP_LIST = [
    (USES_DYNAMIC_OFFSETS, XFAIL, UNSUPPORTED_MESSAGE),
    (CHECKS_SPECIFIC_ERROR, XFAIL, UNSUPPORTED_MESSAGE),
    (
        USES_SCAN_WITHOUT_FIELD_ARGS,
        XFAIL,
        UNSUPPORTED_MESSAGE,
    ),  # we can't extract the field type from scan args
]
ROUNDTRIP_SKIP_LIST = DOMAIN_INFERENCE_SKIP_LIST + [
    (USES_SPARSE_FIELDS_AS_OUTPUT, XFAIL, UNSUPPORTED_MESSAGE),
]
GTFN_SKIP_TEST_LIST = (
    COMMON_SKIP_TEST_LIST
    + DOMAIN_INFERENCE_SKIP_LIST
    + [
        # floordiv not yet supported, see https://github.com/GridTools/gt4py/issues/1136
        (USES_FLOORDIV, XFAIL, BINDINGS_UNSUPPORTED_MESSAGE),
        (USES_STRIDED_NEIGHBOR_OFFSET, XFAIL, BINDINGS_UNSUPPORTED_MESSAGE),
        # max_over broken, see https://github.com/GridTools/gt4py/issues/1289
        (USES_MAX_OVER, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_SCAN_REQUIRING_PROJECTOR, XFAIL, UNSUPPORTED_MESSAGE),
    ]
)

#: Skip matrix, contains for each backend processor a list of tuples with following fields:
#: (<test_marker>, <skip_definition, <skip_message>)
BACKEND_SKIP_TEST_MATRIX = {
    EmbeddedIds.NUMPY_EXECUTION: EMBEDDED_SKIP_LIST,
    EmbeddedIds.CUPY_EXECUTION: EMBEDDED_SKIP_LIST,
    OptionalProgramBackendId.DACE_CPU: DACE_SKIP_TEST_LIST,
    OptionalProgramBackendId.DACE_GPU: DACE_SKIP_TEST_LIST,
    OptionalProgramBackendId.GTIR_DACE_CPU: GTIR_DACE_SKIP_TEST_LIST,
    OptionalProgramBackendId.GTIR_DACE_GPU: GTIR_DACE_SKIP_TEST_LIST
    + [
        # TODO(edopao): Enable when GPU codegen issues related to symbolic domain are fixed.
        (ALL, XFAIL, UNSUPPORTED_MESSAGE),
    ],
    ProgramBackendId.GTFN_CPU: GTFN_SKIP_TEST_LIST
    + [(USES_SCAN_NESTED, XFAIL, UNSUPPORTED_MESSAGE)],
    ProgramBackendId.GTFN_CPU_IMPERATIVE: GTFN_SKIP_TEST_LIST
    + [(USES_SCAN_NESTED, XFAIL, UNSUPPORTED_MESSAGE)],
    ProgramBackendId.GTFN_GPU: GTFN_SKIP_TEST_LIST
    + [(USES_SCAN_NESTED, XFAIL, UNSUPPORTED_MESSAGE)],
    ProgramFormatterId.GTFN_CPP_FORMATTER: DOMAIN_INFERENCE_SKIP_LIST
    + [
        (USES_REDUCTION_WITH_ONLY_SPARSE_FIELDS, XFAIL, REDUCTION_WITH_ONLY_SPARSE_FIELDS_MESSAGE),
    ],
    ProgramFormatterId.LISP_FORMATTER: DOMAIN_INFERENCE_SKIP_LIST,
    ProgramBackendId.ROUNDTRIP: ROUNDTRIP_SKIP_LIST,
    ProgramBackendId.DOUBLE_ROUNDTRIP: ROUNDTRIP_SKIP_LIST,
    ProgramBackendId.ROUNDTRIP_WITH_TEMPORARIES: ROUNDTRIP_SKIP_LIST
    + [
        (ALL, XFAIL, UNSUPPORTED_MESSAGE),
        (USES_STRIDED_NEIGHBOR_OFFSET, XFAIL, UNSUPPORTED_MESSAGE),
    ],
    ProgramBackendId.GTIR_EMBEDDED: ROUNDTRIP_SKIP_LIST,
}
