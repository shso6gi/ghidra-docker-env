# -*- coding: utf-8 -*-
"""型仮説 overlay の datatype 解決と結果可視化の回帰テスト"""

from scripts.function_tracer_pcode.model import (
    FunctionReturnAnalysis,
    FunctionSignature,
    resolve_type_spec,
)
from scripts.function_tracer_pcode.model.analysis import ReturnInfo
from scripts.function_tracer_pcode.model.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixer, TypeFixResult
from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.equivalence.debug_trace import DebugTrace
from scripts.function_tracer_pcode.equivalence.attempts import record_attempt_from_result
from scripts.function_tracer_pcode.smt import ParallelResult


class MockDataType:
    def __init__(self, name, length, is_signed, path=None):
        self._name = name
        self._length = length
        self._is_signed = is_signed
        self._path = path or f"/{name}"

    def getName(self):
        return self._name

    def getLength(self):
        return self._length

    def isSigned(self):
        return self._is_signed

    def getDataTypePath(self):
        return self._path


class MockDataOrganization:
    def __init__(self, *, int_size=4, long_size=4, long_long_size=8, short_size=2, char_size=1, pointer_size=4):
        self._int_size = int_size
        self._long_size = long_size
        self._long_long_size = long_long_size
        self._short_size = short_size
        self._char_size = char_size
        self._pointer_size = pointer_size

    def getIntegerSize(self):
        return self._int_size

    def getLongSize(self):
        return self._long_size

    def getLongLongSize(self):
        return self._long_long_size

    def getShortSize(self):
        return self._short_size

    def getCharSize(self):
        return self._char_size

    def getPointerSize(self):
        return self._pointer_size


class MockDataTypeManager:
    def __init__(self, data_types=None, data_organization=None):
        self._data_types = dict(data_types or {})
        self._data_organization = data_organization or MockDataOrganization()

    def getDataType(self, name):
        return self._data_types.get(name)

    def findDataType(self, name):
        return self._data_types.get(name)

    def getDataOrganization(self):
        return self._data_organization


class MockProgram:
    def __init__(self, data_type_manager):
        self._data_type_manager = data_type_manager

    def getDataTypeManager(self):
        return self._data_type_manager


def _build_analysis():
    return FunctionReturnAnalysis(
        function_name="demo",
        entry_point="0x401000",
        parameters=[
            {
                "name": "arg0",
                "data_type": "ulong",
                "size": 8,
                "is_signed": False,
                "index": 0,
                "storage": {"kind": "register", "size": 8, "size_bits": 64},
            }
        ],
        returns=[
            ReturnInfo(
                address="0x401000",
                conditions=[],
                value=Expression(ExpressionType.CONSTANT, value=1, size=32),
            )
        ],
        return_type="ulong",
    )


def test_resolve_type_spec_prefers_program_datatype():
    dtm = MockDataTypeManager(
        data_types={
            "unsigned int": MockDataType("unsigned int", 4, False, "/builtin/unsigned int"),
        }
    )
    program = MockProgram(dtm)

    resolved = resolve_type_spec(
        "unsigned int",
        program=program,
        fallback_size=8,
        fallback_signed=True,
    )

    assert resolved is not None
    assert resolved.source == "ghidra_datatype"
    assert resolved.size_bytes == 4
    assert resolved.is_signed is False
    assert resolved.data_type_path == "/builtin/unsigned int"


def test_type_fixer_uses_data_organization_for_overlay_widths():
    dtm = MockDataTypeManager(
        data_organization=MockDataOrganization(int_size=4, long_size=4, long_long_size=8)
    )
    program = MockProgram(dtm)
    fixer = TypeFixer(program)
    analysis = _build_analysis()

    updated, return_changed, param_changed = fixer.apply_analysis_signature_fix(
        analysis,
        fix_return_type=False,
        fix_param_types=False,
        override_param_type_names={0: "long"},
        phase_name="P_TEST",
        reason="abi width regression guard",
    )

    assert updated is not None
    assert return_changed is False
    assert param_changed is True
    assert updated.parameters[0]["data_type"] == "long"
    assert updated.parameters[0]["size"] == 4
    assert updated.parameters[0]["storage"]["size"] == 4
    assert updated.parameters[0]["storage"]["size_bits"] == 32
    assert updated.parameters[0]["is_signed"] is True
    assert updated.signature_hypotheses[0]["resolved_parameter_overrides"][0]["source"] == "data_organization"


def test_equivalence_result_surfaces_effective_signatures_and_hypotheses():
    original_sig = FunctionSignature(return_type="unsigned int", parameters=[])
    effective_sig = FunctionSignature(return_type="int", parameters=[])

    result = EquivalenceResult(
        is_equivalent=True,
        function1_name="func1",
        function2_name="func2",
        binary1_name="bin1",
        binary2_name="bin2",
        solver_results=ParallelResult(results=[]),
        type_fix_result=TypeFixResult(),
        function1_signature=original_sig,
        function2_signature=original_sig,
        effective_function1_signature=effective_sig,
        effective_function2_signature=effective_sig,
        function1_signature_hypotheses=[{"phase": "P1_SIGNEDNESS", "return_type_override": "int"}],
        function2_signature_hypotheses=[{"phase": "P1_SIGNEDNESS", "return_type_override": "int"}],
    )

    result_dict = result.to_dict()
    assert result_dict["function1_signature"]["return_type"] == "unsigned int"
    assert result_dict["effective_function1_signature"]["return_type"] == "int"
    assert result_dict["function1_signature_hypotheses"][0]["phase"] == "P1_SIGNEDNESS"

    rendered = result.to_string()
    assert "Original signature: unsigned int func1(void)" in rendered
    assert "Effective signature: int func1(void)" in rendered

    trace = DebugTrace()
    record_attempt_from_result(
        debug_trace=trace,
        attempt_id=0,
        retry_count=1,
        phase="P1_SIGNEDNESS",
        result=result,
        transition_reason="UNSAT",
        type_fix_result=TypeFixResult(),
        strategy_name="pairwise",
    )
    attempt = trace.attempts[0]
    assert attempt.effective_function1_signature["return_type"] == "int"
    assert attempt.function1_signature_hypotheses[0]["phase"] == "P1_SIGNEDNESS"
