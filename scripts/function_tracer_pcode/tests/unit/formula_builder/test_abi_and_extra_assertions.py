# -*- coding: utf-8 -*-
"""FormulaBuilder の ABI・追加 assertion まわりのテスト。"""

import pytest

from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.returns import ReturnWidthMismatchError
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    InputRelationKind,
    build_input_correspondence_set,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_parameter_pairs
from scripts.function_tracer_pcode.proof.formula.params import collect_param_info
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.core import (
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
    StorageInfo,
)


def _analysis(func_name: str, param_name: str, size: int) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=func_name,
        entry_point="0x00401000",
        parameters=[{"name": param_name, "size": size, "index": 0, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name=param_name, size=size),
            )
        ],
    )


def _semantic_analysis(
    func_name: str,
    param_name: str,
    data_type: str,
    value_expr: Expression,
) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=func_name,
        entry_point="0x00401000",
        parameters=[
            {
                "name": param_name,
                "size": 8,
                "index": 0,
                "is_signed": True,
                "data_type": data_type,
            }
        ],
        returns=[ReturnInfo(address="0x00401000", conditions=[], value=value_expr)],
    )


class TestExtraAssertions:
    """extra_assertions 機能のテスト"""

    def test_extra_assertions_placement(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _analysis("func1", "x", 4)
        analysis2 = _analysis("func2", "y", 4)

        extra_assertions = [
            "; Custom constraint section",
            "(assert (bvugt x_1 (_ bv0 32)))",
            "(assert (bvugt y_2 (_ bv0 32)))",
        ]

        result = builder.build_equivalence_formula_extended(
            analysis1,
            analysis2,
            extra_assertions=extra_assertions,input_correspondence=build_input_correspondence_set(analysis1, analysis2),
        )

        lines = result.formula.split("\n")
        check_sat_index = next(i for i, line in enumerate(lines) if "(check-sat)" in line)

        custom_section_found = False
        for i in range(check_sat_index):
            if "Custom constraint section" in lines[i]:
                custom_section_found = True
                assert "(assert (bvugt x_1" in lines[i + 1]
                assert "(assert (bvugt y_2" in lines[i + 2]
                break

        assert custom_section_found

    def test_return_width_mismatch_still_requires_explicit_bridge(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _analysis("func1", "x", 4)
        analysis2 = _analysis("func2", "y", 8)

        with pytest.raises(ReturnWidthMismatchError):
            builder.build_equivalence_formula_extended(analysis1, analysis2, input_correspondence=build_input_correspondence_set(analysis1, analysis2))

    def test_canonical_return_observation_compares_on_proven_observation_width(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _analysis("func1", "x", 4)
        analysis2 = _analysis("func2", "y", 8)

        result = builder.build_equivalence_formula_extended(
            analysis1,
            analysis2,
            canonical_return_observation_width=32,input_correspondence=build_input_correspondence_set(analysis1, analysis2),
        )

        assert "Canonical return observation" in result.formula
        assert "(assert (not (= return_1 ((_ extract 31 0) return_2))))" in result.formula


class TestABIConstraints:
    """ABI制約生成のテスト"""

    def test_parameter_pairs_keep_ordinal_for_type_set_only_order_difference(self):
        params1 = [
            ParameterInfo("param_1", "param_1_1", 32, 0, is_signed=True, type_class="int"),
            ParameterInfo("param_2", "param_2_1", 64, 1, is_signed=True, type_class="fp"),
        ]
        params2 = [
            ParameterInfo("param_1", "param_1_2", 64, 0, is_signed=True, type_class="fp"),
            ParameterInfo("param_2", "param_2_2", 32, 1, is_signed=True, type_class="int"),
        ]

        pairs = build_parameter_pairs(params1, params2)

        assert [(pair.param1.smt_name, pair.param2.smt_name) for pair in pairs] == [
            ("param_1_1", "param_1_2"),
            ("param_2_1", "param_2_2"),
        ]

    def test_parameter_pairs_use_type_role_when_mips64_register_bank_artifact_is_visible(self):
        params1 = collect_param_info(
            [
                {
                    "name": "param_1",
                    "data_type": "int",
                    "size": 4,
                    "index": 0,
                    "is_signed": True,
                    "storage": {"space_name": "register", "register_name": "a0_lo", "size": 4},
                },
                {
                    "name": "param_2",
                    "data_type": "double",
                    "size": 8,
                    "index": 1,
                    "is_signed": True,
                    "storage": {"space_name": "register", "register_name": "f13", "size": 8},
                },
            ],
            "_1",
        )
        params2 = collect_param_info(
            [
                {
                    "name": "param_1",
                    "data_type": "double",
                    "size": 8,
                    "index": 0,
                    "is_signed": True,
                    "storage": {"space_name": "register", "register_name": "d0", "size": 8},
                },
                {
                    "name": "param_2",
                    "data_type": "int",
                    "size": 4,
                    "index": 1,
                    "is_signed": True,
                    "storage": {"space_name": "register", "register_name": "w0", "size": 4},
                },
            ],
            "_2",
        )

        pairs = build_parameter_pairs(params1, params2)

        assert [(pair.param1.smt_name, pair.param2.smt_name) for pair in pairs] == [
            ("param_1_1", "param_2_2"),
            ("param_2_1", "param_1_2"),
        ]

    def test_parameter_pairs_keep_ordinal_for_ambiguous_same_typed_parameters(self):
        params1 = [
            ParameterInfo("param_1", "param_1_1", 32, 0, is_signed=True, type_class="int"),
            ParameterInfo("param_2", "param_2_1", 32, 1, is_signed=True, type_class="int"),
        ]
        params2 = [
            ParameterInfo("param_1", "param_1_2", 32, 0, is_signed=True, type_class="int"),
            ParameterInfo("param_2", "param_2_2", 32, 1, is_signed=True, type_class="int"),
        ]

        pairs = build_parameter_pairs(params1, params2)

        assert [(pair.param1.smt_name, pair.param2.smt_name) for pair in pairs] == [
            ("param_1_1", "param_1_2"),
            ("param_2_1", "param_2_2"),
        ]

    def test_parameter_pairs_do_not_match_pointer_to_scalar_fp_by_type_role(self):
        params1 = collect_param_info(
            [
                {"name": "param_1", "data_type": "double *", "size": 8, "index": 0, "is_signed": False},
                {"name": "param_2", "data_type": "int", "size": 4, "index": 1, "is_signed": True},
            ],
            "_1",
        )
        params2 = collect_param_info(
            [
                {"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True},
                {"name": "param_2", "data_type": "double", "size": 8, "index": 1, "is_signed": True},
            ],
            "_2",
        )

        pairs = build_parameter_pairs(params1, params2)

        assert params1[0].type_class == "pointer"
        assert params2[1].type_class == "fp"
        assert ("param_1_1", "param_2_2") not in [
            (
                pair.param1.smt_name if pair.param1 is not None else None,
                pair.param2.smt_name if pair.param2 is not None else None,
            )
            for pair in pairs
        ]

    def test_parameter_type_class_treats_intptr_typedef_names_as_integral(self):
        params = collect_param_info(
            [
                {"name": "param_1", "data_type": "intptr_t", "size": 8, "index": 0, "is_signed": True},
                {"name": "param_2", "data_type": "uintptr_t", "size": 8, "index": 1, "is_signed": False},
            ],
            "_1",
        )

        assert [param.type_class for param in params] == ["int", "int"]


    def test_same_width_projection_tie_comes_from_raw_closure_not_from_hint(self):
        """両側 ``long x`` を ``SUBPIECE(x)[4]`` でしか読まない。

        修正前は hint（単一 use の射影主張）から下位 32 bit の tie を作っていた。
        修正後も同じ tie になるが、根拠は両側の raw closure at 32（R3）で、
        自己整合制約（``x == sext(low32 x)``）は付かない（Issue #167）。
        """
        builder = FormulaBuilder(debug=False)
        subpiece_value = Expression(
            ExpressionType.BINARY_OP,
            operator="SUBPIECE",
            operands=[
                Expression(ExpressionType.PARAMETER, name="x", value=0, size=8),
                Expression(ExpressionType.CONSTANT, value=0, size=8),
            ],
            size=4,
        )
        analysis1 = _semantic_analysis("func1", "x", "long", subpiece_value)
        analysis2 = _semantic_analysis("func2", "x", "long", subpiece_value)

        correspondence = build_input_correspondence_set(analysis1, analysis2)
        (item,) = correspondence.correspondences
        assert item.kind is InputRelationKind.SEMANTIC_PROJECTION
        assert item.tie_bits == 32
        assert item.entailed == ()

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2, input_correspondence=build_input_correspondence_set(analysis1, analysis2)).formula
        assertions = [line for line in formula.splitlines() if line.startswith("(assert")]
        assert "(assert (= ((_ extract 31 0) x_1) ((_ extract 31 0) x_2)))" in assertions
        assert not any("_extend" in line for line in assertions)

    def test_fragment_does_not_tie_wide_param_to_extended_narrow_value(self):
        """narrow 側の上位 register 断片があっても ``wide == sext(narrow)`` を足さない。

        修正前は fragment の ``is_signed`` ラベルから cross-side の
        ``(= param_1_2 ((_ sign_extend 32) param_1_1))`` を premise に入れていた。
        これは入力 extension 仮定であり、信頼済み IEE が無ければ成り立たない。
        """
        low_storage = StorageInfo(
            is_register=True, space_name="register", offset=0x20, size=4, size_bits=32,
            register_name="a0_lo", base_register_name="a0", base_register_size_bits=64,
            bit_offset_in_base=0,
        )
        high_storage = StorageInfo(
            is_register=True, space_name="register", offset=0x24, size=4, size_bits=32,
            register_name="a0_hi", base_register_name="a0", base_register_size_bits=64,
            bit_offset_in_base=32,
        )
        narrow_param = Expression(
            ExpressionType.PARAMETER, name="param_1", value=0, size=4, storage_info=low_storage,
        )
        high = Expression(ExpressionType.VARIABLE, name="in_a0_hi", size=4, storage_info=high_storage)
        left = FunctionReturnAnalysis(
            function_name="f",
            entry_point="0x00401000",
            parameters=[{
                "name": "param_1", "size": 4, "index": 0, "is_signed": True,
                "storage": {"is_register": True, "space_name": "register", "offset": 0x20,
                            "size": 4, "size_bits": 32, "register_name": "a0_lo",
                            "base_register_name": "a0", "base_register_size_bits": 64,
                            "bit_offset_in_base": 0},
            }],
            returns=[ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.BINARY_OP, operator="PIECE", operands=[high, narrow_param], size=8),
            )],
        )
        right = _analysis("f", "param_1", 8)

        correspondence = build_input_correspondence_set(left, right)
        (item,) = correspondence.correspondences
        assert item.kind is InputRelationKind.WIDTH_OVERLAP
        assert item.entailed == ()
        assert not item.decisive_sufficient
        assert any("register_alias" in ref for ref in item.evidence)

        formula = FormulaBuilder(debug=False).build_equivalence_formula_extended(left, right, input_correspondence=build_input_correspondence_set(left, right)).formula
        assertions = [line for line in formula.splitlines() if line.startswith("(assert")]
        assert not any("sign_extend" in line or "in_a0_hi" in line for line in assertions)
        assert "(assert (= param_1_1 ((_ extract 31 0) param_1_2)))" in assertions


class TestNoRsplit:
    """rsplit削除の検証テスト"""

    def test_no_rsplit_in_builder(self):
        builder = FormulaBuilder(debug=False)

        assert "rsplit" not in builder.build_equivalence_formula_extended.__code__.co_names
