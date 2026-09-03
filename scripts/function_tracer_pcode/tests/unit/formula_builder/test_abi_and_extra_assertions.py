# -*- coding: utf-8 -*-
"""FormulaBuilder の ABI・追加 assertion まわりのテスト。"""

import pytest

from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.returns import ReturnWidthMismatchError
from scripts.function_tracer_pcode.proof.formula.params import (
    build_fragment_backed_parameter_constraint,
    build_parameter_pairs,
    collect_param_info,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo, ParameterPair
from scripts.function_tracer_pcode.proof.formula.variable import (
    ExtensionType,
    ParameterFragmentInfo,
)
from scripts.function_tracer_pcode.core import (
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
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
            extra_assertions=extra_assertions,
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
            builder.build_equivalence_formula_extended(analysis1, analysis2)

    def test_canonical_return_observation_compares_on_proven_observation_width(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _analysis("func1", "x", 4)
        analysis2 = _analysis("func2", "y", 8)

        result = builder.build_equivalence_formula_extended(
            analysis1,
            analysis2,
            canonical_return_observation_width=32,
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

    def test_abi_constraint_generation(self):
        builder = FormulaBuilder(debug=False)
        abi_constraints = {
            "param0_1": ("signed", 32),
            "param1_2": ("unsigned", 32),
        }

        constraint_lines = builder.build_abi_constraints(abi_constraints, "_1", "_2")
        constraints_text = "\n".join(constraint_lines)

        assert "param0_1" in constraints_text
        assert "sign_extend" in constraints_text
        assert "param0_2" in constraints_text
        assert "(= param0_1 ((_ sign_extend 32) ((_ extract 31 0) param0_2)))" in constraints_text
        assert "param1_2" in constraints_text
        assert "zero_extend" in constraints_text
        assert "param1_1" in constraints_text
        assert "(= param1_2 ((_ zero_extend 32) ((_ extract 31 0) param1_1)))" in constraints_text

    def test_build_with_abi_constraints_blocks_unbridged_return_width_mismatch(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _analysis("func1", "x", 8)
        analysis2 = _analysis("func2", "y", 4)
        abi_constraints = {"x_1": ("signed", 32)}

        section = builder.build_abi_assertion_section(abi_constraints, "_1", "_2")
        section_text = "\n".join(section)
        assert "MIPS64 ABI constraints" in section_text
        assert "sign_extend" in section_text
        assert "x_1" in section_text
        assert "x_2" in section_text

        with pytest.raises(ReturnWidthMismatchError) as exc_info:
            builder.build_with_abi_constraints(analysis1, analysis2, abi_constraints)

        assert exc_info.value.reason_id == "return_width_bridge_missing"

    def test_build_abi_assertion_section(self):
        builder = FormulaBuilder(debug=False)
        section_lines = builder.build_abi_assertion_section(
            {"param0_1": ("signed", 32)},
            "_1",
            "_2",
        )

        assert any("MIPS64 ABI constraints" in line for line in section_lines)
        section_text = "\n".join(section_lines)
        assert "param0_1" in section_text
        assert "param0_2" in section_text
        assert "sign_extend" in section_text

    def test_build_abi_assertion_section_empty(self):
        builder = FormulaBuilder(debug=False)
        assert builder.build_abi_assertion_section({}, "_1", "_2") == []

    def test_suffix_resolution_in_abi_constraints(self):
        builder = FormulaBuilder(debug=False)

        text_1to2 = "\n".join(builder.build_abi_constraints({"x_1": ("signed", 32)}, "_1", "_2"))
        assert "x_1" in text_1to2
        assert "x_2" in text_1to2
        assert "(= x_1" in text_1to2
        assert "x_2))" in text_1to2

        text_2to1 = "\n".join(builder.build_abi_constraints({"y_2": ("unsigned", 32)}, "_1", "_2"))
        assert "y_2" in text_2to1
        assert "y_1" in text_2to1
        assert "(= y_2" in text_2to1
        assert "y_1))" in text_2to1
        assert "zero_extend" in text_2to1

    def test_suffix_resolution_only_rewrites_trailing_suffix(self):
        builder = FormulaBuilder(debug=False)
        text = "\n".join(
            builder.build_abi_constraints(
                {
                    "param_1_1": ("signed", 32),
                    "param_2_2": ("unsigned", 32),
                },
                "_1",
                "_2",
            )
        )

        assert "param_1_2" in text
        assert "param_2_1" in text
        assert "param_2_2 ((_ sign_extend 32) param_1_1)" not in text
        assert "param_1_1 ((_ zero_extend 32) param_2_2)" not in text
        assert "(= param_1_1 ((_ sign_extend 32) ((_ extract 31 0) param_1_2)))" in text
        assert "(= param_2_2 ((_ zero_extend 32) ((_ extract 31 0) param_2_1)))" in text

    def test_abi_constraints_extract_lower_bits_before_extension(self):
        builder = FormulaBuilder(debug=False)
        text = "\n".join(builder.build_abi_constraints({"x_1": ("signed", 32)}, "_1", "_2"))

        assert "lower 32 bits" in text
        assert "((_ extract 31 0) x_2)" in text
        assert "((_ sign_extend 32) ((_ extract 31 0) x_2))" in text

    def test_build_with_abi_constraints_wrapper_consistency_for_width_mismatch_block(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _analysis("func1", "param0", 8)
        analysis2 = _analysis("func2", "param0", 4)
        abi_constraints = {"param0_1": ("signed", 32)}

        section = builder.build_abi_assertion_section(abi_constraints, "_1", "_2")
        with pytest.raises(ReturnWidthMismatchError) as wrapper_exc:
            builder.build_with_abi_constraints(analysis1, analysis2, abi_constraints)
        with pytest.raises(ReturnWidthMismatchError) as direct_exc:
            builder.build_equivalence_formula_extended(
                analysis1,
                analysis2,
                extra_assertions=section,
            )

        assert wrapper_exc.value.reason_id == direct_exc.value.reason_id
        assert str(wrapper_exc.value) == str(direct_exc.value)

    def test_semantic_width_constraints_are_emitted_for_narrowed_same_width_parameters(self):
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

        result = builder.build_equivalence_formula_extended(analysis1, analysis2)
        formula = result.formula

        assert "Parameter semantic-width constraints" not in formula
        assert "constrain to signed 32-bit semantic value" not in formula
        assert "semantic lower 32 bits must match" in formula
        assert "((_ extract 31 0) x_1)" in formula
        assert "((_ extract 31 0) x_2)" in formula

    def test_fragment_backed_parameter_constraint_ties_wide_param_to_extended_narrow_value(self):
        pair = ParameterPair(
            index=0,
            param1=ParameterInfo("param_1", "param_1_1", 32, 0, is_signed=True),
            param2=ParameterInfo("param_1", "param_1_2", 64, 0, is_signed=True),
        )
        fragment_info = ParameterFragmentInfo(
            fragment_name="in_a0_hi",
            fragment_bit_width=32,
            parent_param_name="param_1",
            parent_param_index=0,
            parent_param_bit_width=32,
            extension_type=ExtensionType.SIGN_EXTEND,
            bit_offset_in_base=32,
            bit_length=32,
            base_register_name="a0",
            base_register_size_bits=64,
        )

        lines = build_fragment_backed_parameter_constraint(
            pair,
            fragment_info1=fragment_info,
        )

        assert lines is not None
        text = "\n".join(lines)
        assert "fragment-backed" in text
        assert "(assert (= param_1_2 ((_ sign_extend 32) param_1_1)))" in text


class TestNoRsplit:
    """rsplit削除の検証テスト"""

    def test_no_rsplit_in_builder(self):
        builder = FormulaBuilder(debug=False)

        assert "rsplit" not in builder.build_abi_constraints.__code__.co_names
        assert "rsplit" not in builder.build_with_abi_constraints.__code__.co_names
        assert "rsplit" not in builder.build_equivalence_formula_extended.__code__.co_names
        assert "rsplit" not in builder.build_abi_assertion_section.__code__.co_names
