# -*- coding: utf-8 -*-
"""Issue #167 root-cause probe (evidence only; production never imports this).

各 probe は実 production の normalizer / FormulaBuilder / SMT lowering を呼び、
その出力を z3 CLI に解かせる。手書きの理想式は使わない。修正前（``1be9c16``）と
修正後の両方で同じ command を実行し、README の期待値と比べる。

    docker compose run --rm -T ghidra-dev \
        python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue167.probe_root_cause

出力は 1 probe 1 行の JSON（key 順固定）。
"""

from __future__ import annotations

import json
import subprocess
import sys
from typing import Any, Dict, List, Optional

from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.semantics.param_semantics import infer_parameter_semantics
from scripts.function_tracer_pcode.semantics.semantic_width import (
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _param(name: str, size: int, index: int = 0) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, value=index, size=size)


def _const(value: int, size: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _bin(op: str, left: Expression, right: Expression, size: int) -> Expression:
    return Expression(ExpressionType.BINARY_OP, operator=op, operands=[left, right], size=size)


def _un(op: str, operand: Expression, size: int) -> Expression:
    return Expression(ExpressionType.UNARY_OP, operator=op, operands=[operand], size=size)


def _low(expr: Expression, size: int) -> Expression:
    return _bin("SUBPIECE", expr, _const(0, 8), size)


def _analysis(
    name: str,
    params: List[Dict[str, Any]],
    returns: List[ReturnInfo],
    return_type: str = "int",
):
    return create_mock_analysis(name, return_type=return_type, parameters=params, returns=returns)


def _ret(value: Expression, *conditions: Expression, negated: bool = False) -> ReturnInfo:
    return ReturnInfo(
        address="0x1000",
        conditions=[Condition(expr, negated) for expr in conditions],
        value=value,
    )


def _z3(formula: str) -> str:
    completed = subprocess.run(
        ["z3", "-in", "-T:30"],
        input=formula,
        capture_output=True,
        text=True,
        check=False,
    )
    lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    return lines[0] if lines else f"no-output rc={completed.returncode}"


def _long_param(name: str = "x", index: int = 0) -> Dict[str, Any]:
    return {"name": name, "index": index, "data_type": "long", "size": 8, "is_signed": True}


def _normalized_condition_texts(analysis) -> List[str]:
    normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))
    texts = []
    for ret in normalized.returns:
        for cond in ret.conditions:
            texts.append(cond.expression.to_smt())
    return texts


def probe_w1_cross_use() -> Dict[str, Any]:
    """use A: SUBPIECE(x,0)==5 (32bit), use B: x==0 (64bit) in one function."""
    x = _param("x", 8)
    use_a = _bin("INT_EQUAL", _low(x, 4), _const(5, 4), 1)
    use_b = _bin("INT_EQUAL", x, _const(0, 8), 1)
    analysis = _analysis(
        "f",
        [_long_param()],
        [_ret(_const(1, 4), use_a), _ret(_const(2, 4), use_b), _ret(_const(3, 4))],
    )
    texts = _normalized_condition_texts(analysis)
    use_b_text = texts[1] if len(texts) > 1 else None
    return {
        "probe": "W1_cross_use_hint_contamination",
        "use_b_normalized": use_b_text,
        "use_b_narrowed": bool(use_b_text and "extract" in use_b_text),
    }


def _monolithic_status(analysis1, analysis2) -> str:
    formula = FormulaBuilder(debug=False).build_equivalence_formula_extended(
        analysis1, analysis2
    ).formula
    return _z3(formula)


def probe_w6_false_eq() -> Dict[str, Any]:
    """f1: return (x == 0) on the full 64 bits.  f2: return ((int)x == 0).

    ``x = 1 << 32`` separates them, so the true verdict is NOT_EQ (SAT).  f1 also
    contains a 32-bit use of x so that a hint exists on the f1 side.
    """
    x1 = _param("x", 8)
    f1 = _analysis(
        "f",
        [_long_param()],
        [
            _ret(_const(7, 4), _bin("INT_EQUAL", _low(x1, 4), _const(0x7FFFFFFF, 4), 1)),
            _ret(_un("INT_ZEXT", _bin("INT_EQUAL", x1, _const(0, 8), 1), 4)),
        ],
    )
    x2 = _param("x", 8)
    f2 = _analysis(
        "f",
        [_long_param()],
        [
            _ret(_const(7, 4), _bin("INT_EQUAL", _low(x2, 4), _const(0x7FFFFFFF, 4), 1)),
            _ret(_un("INT_ZEXT", _bin("INT_EQUAL", _low(x2, 4), _const(0, 4), 1), 4)),
        ],
    )
    # 条件の否定は ReturnInfo 側の順序で決まるので、第 2 return に第 1 条件の否定を付ける。
    f1.returns[1].conditions = [Condition(f1.returns[0].conditions[0].expression, True)]
    f2.returns[1].conditions = [Condition(f2.returns[0].conditions[0].expression, True)]
    return {
        "probe": "W6_false_equivalent",
        "monolithic": _monolithic_status(f1, f2),
        "expected_semantics": "sat",
    }


def probe_w3_false_not_eq() -> Dict[str, Any]:
    """The same function on both sides: return x (64bit), plus a 32-bit use of x."""

    def build():
        x = _param("x", 8)
        return _analysis(
            "g",
            [_long_param()],
            [
                _ret(_const(0, 8), _bin("INT_EQUAL", _low(x, 4), _const(5, 4), 1)),
                _ret(x, _bin("INT_EQUAL", _low(x, 4), _const(5, 4), 1), negated=True),
            ],
            return_type="long",
        )

    left = build()
    right = build()
    return {
        "probe": "W3_false_not_equivalent",
        "monolithic": _monolithic_status(left, right),
        "expected_semantics": "unsat",
    }


def _rewrite_pair(expr: Expression, analysis_params: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Normalize ``return expr`` and SMT-check ``original != rewritten``."""
    analysis = _analysis("h", analysis_params, [_ret(expr)])
    normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))
    rewritten = normalized.returns[0].value
    original_bits = expression_smt_bit_width(expr)
    rewritten_bits = expression_smt_bit_width(rewritten)
    declarations = "".join(
        f"(declare-const {p['name']} (_ BitVec {int(p['size']) * 8}))\n" for p in analysis_params
    )
    if original_bits != rewritten_bits:
        status = "sort_changed"
    else:
        formula = (
            "(set-logic QF_BV)\n"
            + declarations
            + f"(assert (not (= {expr.to_smt()} {rewritten.to_smt()})))\n(check-sat)\n"
        )
        status = _z3(formula)
    return {
        "original": expr.to_smt(),
        "rewritten": rewritten.to_smt(),
        "original_bits": original_bits,
        "rewritten_bits": rewritten_bits,
        "differs_somewhere": status,
    }


def probe_sort_change() -> Dict[str, Any]:
    """Bare arithmetic narrowing: 64-bit ``x + 1`` with a 32-bit hint on x."""
    x = _param("x", 8)
    hint_use = _bin("INT_SLESS", _low(x, 4), _const(3, 4), 1)
    expr = _bin("INT_ADD", x, _const(1, 8), 8)
    analysis = _analysis("h", [_long_param()], [_ret(expr, hint_use)])
    normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))
    rewritten = normalized.returns[0].value
    return {
        "probe": "sort_change_bare_arithmetic",
        "original": expr.to_smt(),
        "original_bits": expression_smt_bit_width(expr),
        "rewritten": rewritten.to_smt(),
        "rewritten_bits": expression_smt_bit_width(rewritten),
    }


def probe_signed_unsigned_comparison() -> Dict[str, Any]:
    """``sext64(low32 p) <u 16`` next to an explicit signed 32-bit use of p.

    With low32(p) = 0x80000000 the unsigned comparison is false while the
    rewritten ``low32(p) <s 16`` is true, for every p (no premise needed).
    """
    p = _param("p", 8)
    hint_use = _bin("INT_SLESS", _low(p, 4), _const(3, 4), 1)
    widened = _un("INT_SEXT", _low(p, 4), 8)
    expr = _un("INT_ZEXT", _bin("INT_LESS", widened, _const(16, 8), 1), 4)
    analysis = _analysis("c", [_long_param("p")], [_ret(expr, hint_use)])
    normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))
    rewritten = normalized.returns[0].value
    formula = (
        "(set-logic QF_BV)\n(declare-const p (_ BitVec 64))\n"
        f"(assert (not (= {expr.to_smt()} {rewritten.to_smt()})))\n(check-sat)\n"
    )
    return {
        "probe": "signed_unsigned_comparison",
        "original": expr.to_smt(),
        "rewritten": rewritten.to_smt(),
        "differs_somewhere": _z3(formula),
    }


def probe_mask_parent_sort() -> Dict[str, Any]:
    """``(~(p & 0xffffffff)) == 0xffffffff00000000`` is true at p = 0xffffffff."""
    p = _param("p", 8)
    hint_use = _bin("INT_LESS", _low(p, 4), _const(3, 4), 1)
    masked = _bin("INT_AND", p, _const(0xFFFFFFFF, 8), 8)
    inverted = _un("INT_NEGATE", masked, 8)
    expr = _un(
        "INT_ZEXT",
        _bin("INT_EQUAL", inverted, _const(0xFFFFFFFF00000000, 8), 1),
        4,
    )
    analysis = _analysis("m", [_long_param("p")], [_ret(expr, hint_use)])
    normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))
    rewritten = normalized.returns[0].value
    formula = (
        "(set-logic QF_BV)\n(declare-const p (_ BitVec 64))\n"
        f"(assert (not (= {expr.to_smt()} {rewritten.to_smt()})))\n(check-sat)\n"
    )
    return {
        "probe": "mask_parent_sort",
        "original": expr.to_smt(),
        "rewritten": rewritten.to_smt(),
        "differs_somewhere": _z3(formula),
    }


def probe_div_composite_operand() -> Dict[str, Any]:
    """SDIV of zero-extended operands narrowed as a signed 32-bit division."""
    a = _param("a", 8, 0)
    b = _param("b", 8, 1)
    hint_uses = [
        _bin("INT_SLESS", _low(a, 4), _const(3, 4), 1),
        _bin("INT_SLESS", _low(b, 4), _const(3, 4), 1),
    ]
    a_masked = _bin("INT_AND", a, _const(0xFFFFFFFF, 8), 8)
    b_masked = _bin("INT_AND", b, _const(0xFFFFFFFF, 8), 8)
    expr = _low(_bin("INT_SDIV", a_masked, b_masked, 8), 4)
    params = [_long_param("a", 0), _long_param("b", 1)]
    analysis = _analysis("d", params, [_ret(expr, *hint_uses)])
    normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))
    rewritten = normalized.returns[0].value
    formula = (
        "(set-logic QF_BV)\n(declare-const a (_ BitVec 64))\n(declare-const b (_ BitVec 64))\n"
        f"(assert (not (= {expr.to_smt()} {rewritten.to_smt()})))\n(check-sat)\n"
    )
    return {
        "probe": "div_composite_operand",
        "original": expr.to_smt(),
        "rewritten": rewritten.to_smt(),
        "differs_somewhere": _z3(formula),
    }


def probe_independent_fragment() -> Dict[str, Any]:
    """``PIECE(hi, x)`` collapses to ``sext(x)`` from a fragment tag alone.

    ``hi`` is an independent 32-bit input here; the only link to ``x`` is the
    ``is_signed`` label carried by ``ParameterFragmentInfo``.
    """
    from scripts.function_tracer_pcode.proof.formula.variable import (
        ExtensionType,
        ExtraVariableAnalysis,
        ParameterFragmentInfo,
        VariableClassification,
    )

    x = _param("x", 4)
    hi = Expression(ExpressionType.VARIABLE, name="in_a0_hi", size=4)
    expr = _bin("PIECE", hi, x, 8)
    fragment = ParameterFragmentInfo(
        fragment_name="in_a0_hi",
        fragment_bit_width=32,
        parent_param_name="x",
        parent_param_index=0,
        parent_param_bit_width=32,
        extension_type=ExtensionType.SIGN_EXTEND,
        bit_offset_in_base=32,
        bit_length=32,
        base_register_name="a0",
        base_register_size_bits=64,
    )
    extra = ExtraVariableAnalysis(
        name="in_a0_hi",
        bit_width=32,
        classification=VariableClassification.PARAMETER_FRAGMENT,
        fragment_info=fragment,
    )
    analysis = _analysis(
        "fr",
        [{"name": "x", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        [_ret(expr)],
        return_type="long",
    )
    import inspect

    if "fragment_infos" in inspect.signature(normalize_analysis_semantic_width).parameters:
        # 1be9c16: fragment 情報は normalizer の引数だった。
        normalized = normalize_analysis_semantic_width(
            analysis, infer_parameter_semantics(analysis), {"in_a0_hi": extra}
        )
    else:
        # 修正後: fragment tag は書き換えの根拠にならないので引数自体が無い。
        normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))
    rewritten = normalized.returns[0].value
    formula = (
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 32))\n"
        "(declare-const in_a0_hi (_ BitVec 32))\n"
        f"(assert (not (= {expr.to_smt()} {rewritten.to_smt()})))\n(check-sat)\n"
    )
    return {
        "probe": "independent_fragment_collapse",
        "original": expr.to_smt(),
        "rewritten": rewritten.to_smt(),
        "differs_somewhere": _z3(formula),
    }


def main(argv: Optional[List[str]] = None) -> int:
    del argv
    probes = (
        probe_w1_cross_use,
        probe_w6_false_eq,
        probe_w3_false_not_eq,
        probe_sort_change,
        probe_signed_unsigned_comparison,
        probe_mask_parent_sort,
        probe_div_composite_operand,
        probe_independent_fragment,
    )
    for probe in probes:
        try:
            payload = probe()
        except Exception as exc:  # evidence script: 例外も結果として記録する
            payload = {"probe": probe.__name__, "exception": f"{type(exc).__name__}: {exc}"}
        print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
