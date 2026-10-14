# -*- coding: utf-8 -*-
"""Test support: mock FormulaBuilder が「渡された relation を報告する」ようにする（Issue #167）。

本物の ``FormulaBuilder.build_base_context`` / ``build_equivalence_formula_extended``
は、caller から受け取った最終 ``InputCorrespondenceSet`` で premise を描き、同じ
値を ``base_ctx["input_correspondence"]`` / ``FormulaBuilderResult.input_correspondence``
として返す。decisive gate はその値が strategy の relation と同じかを照合し、報告が
無ければ ``unavailable`` で fail-closed にする。

header を手で書いた mock builder を使う test（call effect / coverage / replay など
別の gate の test）は、この helper で本物と同じ報告契約だけを与える。premise の
正しさ自体は ``test_input_correspondence*.py`` が本物の builder で検証する。
"""

from __future__ import annotations

from contextlib import contextmanager
import dataclasses
from typing import Any, Iterator

from scripts.function_tracer_pcode.proof.formula.types import FormulaBuilderResult


def echo_input_correspondence(builder: Any) -> Any:
    base_context = builder.build_base_context

    def build_base_context(*_args: Any, **kwargs: Any) -> Any:
        value = base_context.return_value
        if isinstance(value, dict):
            # 本物と同じく caller が後から書き足す dict そのものを返す（test が
            # 読み戻す key があるので複製しない）。
            value["input_correspondence"] = kwargs.get("input_correspondence")
        return value

    base_context.side_effect = build_base_context

    formula = builder.build_equivalence_formula_extended

    def build_formula(*_args: Any, **kwargs: Any) -> Any:
        value = formula.return_value
        if isinstance(value, FormulaBuilderResult) and value.input_correspondence is None:
            value = dataclasses.replace(value, input_correspondence=kwargs.get("input_correspondence"))
        return value

    formula.side_effect = build_formula
    return builder


def synthetic_input_extension_evidence(analysis: Any, index: int, *, logical_bits: int, storage_bits: int, kind: Any):
    """consumer test 用の合成 IEE（validator を通す。production にこの出所は無い）。

    production provider（``checker/arch/input_extension.py``）は信頼済み signature が
    無いので IEE を発行しない。ここは IEE を消費する側（relation・書き換え・proof）が
    正しく扱うかを確かめるためだけに、封印 token で信頼済み分類を作る。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import evidence as iee_contract
    from scripts.function_tracer_pcode.semantics.rewrite_contract import ExtensionKind

    binding = iee_contract.analysis_parameter_binding(analysis, index)
    assert binding is not None, "the analysis needs binary_id and function_ref for a binding"
    rule = iee_contract.AbiExtensionRule(
        abi_id="synthetic-test-abi",
        binary_id=binding.binary_id,
        register_class="register",
        storage_bits=storage_bits,
        logical_bits=logical_bits,
        is_signed=None,
        kind=kind,
        source_reference="test fixture",
    )
    classification = iee_contract.TrustedParameterClassification(
        binding, logical_bits, kind is ExtensionKind.SIGN, "int",
        "synthetic_test_signature", "0" * 64,
        _factory_token=iee_contract._TRUSTED_CLASSIFICATION_TOKEN,
    )
    storage = iee_contract.StorageObservation(binding, "r0", "register", 0, storage_bits, storage_bits)
    evidence, reasons = iee_contract.validate_input_extension_evidence(rule, classification, storage)
    assert reasons == (), reasons
    return evidence


def comparison_binding_of(analysis1: Any, analysis2: Any, relation: Any = None, **relation_options: Any) -> Any:
    """raw pair ``(analysis1, analysis2)`` と最終 relation の ``ComparisonAuthorityBinding``。"""

    from scripts.function_tracer_pcode.proof.call_effect.preflight import StrategySourceAnalysisPair
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        ComparisonAuthorityBinding,
        build_input_correspondence_set,
    )

    if relation is None:
        relation = build_input_correspondence_set(analysis1, analysis2, **relation_options)
    return ComparisonAuthorityBinding.of(StrategySourceAnalysisPair.create(analysis1, analysis2), relation)


@contextmanager
def comparison_of(analysis1: Any, analysis2: Any, relation: Any = None, **relation_options: Any) -> Iterator[Any]:
    """producer と gate を直接呼ぶ test 用: 1 つの比較（raw pair と最終 relation）の範囲を開く。

    production では dispatch 境界（``run_strategy_branch``）と stage runner が比較の
    範囲を開き、比較の中で作った証拠はその比較に束縛される（Issue #167）。
    yield するのは ``ComparisonAuthorityBinding``（``.relation`` が最終 relation）。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import comparison_scope

    binding = comparison_binding_of(analysis1, analysis2, relation, **relation_options)
    with comparison_scope(binding):
        yield binding


@contextmanager
def positional_comparison(parameters: Any) -> Iterator[Any]:
    """左右が同じ parameter 表（位置どおり・同じ名前・全幅の等式の relation）の比較の範囲を開く。

    owner を含まない key で左右を同一視する producer（plan v4 PR-P の gate の下）を直接呼ぶ
    test 用。``parameters`` は両側に使う parameter descriptor の列。gate が通る relation で
    あることを確かめてから yield する。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        comparison_scope,
        positional_identity_gate,
    )
    from scripts.function_tracer_pcode.core import Expression, ReturnInfo
    from scripts.function_tracer_pcode.tests.unit._publication import raw_function_analysis

    def analysis(entry_point: str) -> Any:
        # 各 parameter を全幅で読む return（読みの無い parameter は狭い幅の射影 R3 になり、
        # 位置どおり・全幅の等式にならない）。
        returns = [
            ReturnInfo(
                f"{entry_point}:{item['index']}",
                Expression.parameter(
                    item["name"], int(item["index"]), data_type=item.get("data_type"),
                    size=int(item["size"]),
                ),
                [],
            )
            for item in parameters
        ]
        return raw_function_analysis(
            function_name="f", entry_point=entry_point,
            parameters=[dict(item) for item in parameters], returns=returns, return_type="long",
        )

    binding = comparison_binding_of(analysis("0x1000"), analysis("0x2000"))
    gate = positional_identity_gate(binding.relation)
    assert gate.passed, gate.evidence_refs
    with comparison_scope(binding):
        yield binding


def open_cross_side_gate(monkeypatch: Any) -> None:
    """owner を含まない同一視の gate（plan v4 PR-P）を常に通す。

    位置どおりでない relation（幅の違う組・extension）の下の producer の仕組みそのものを確かめる
    test 用。gate が閉じていることは別の assert で先に確かめ、ここでは「relation を通した翻訳
    （PR-H）で回復する経路の中身」だけを見る。production では使わない。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import gate as gate_module

    monkeypatch.setattr(gate_module, "positional_identity_gate", lambda _ics: gate_module.CrossSideIdentityGate.accept())
    monkeypatch.setattr(
        gate_module, "closure_reads_are_full",
        lambda _ics, _left, _right: gate_module.CrossSideIdentityGate.accept(),
    )


def fixed_test_comparison(name: str = "f") -> Any:
    """1 引数関数どうしの、決まった比較（raw pair と最終 relation）。"""

    from scripts.function_tracer_pcode.core import Expression, FunctionReturnAnalysis, ReturnInfo

    def analysis(function_name: str) -> Any:
        return FunctionReturnAnalysis(
            function_name=function_name, entry_point="0x1000",
            parameters=[{"name": "p0", "index": 0, "size": 4, "data_type": "int"}],
            returns=[ReturnInfo("0x1010", Expression.parameter("p0", 0, data_type="int", size=4), [])],
            return_type="int",
        )

    return comparison_binding_of(analysis(name), analysis(name + "_peer"))


def comparison_frame(comparison: Any, **fields: Any) -> Any:
    """branch の結果に付く dispatch frame の、比較の authority だけを持つ代役。"""

    from types import SimpleNamespace

    fields.setdefault("obligation_runtime", None)
    return SimpleNamespace(
        source=SimpleNamespace(comparison_digest=comparison.raw_pair_digest),
        comparison_binding=comparison,
        **fields,
    )


def bound_to(comparison: Any, record: Any, *, identification: Any = "correspondence") -> Any:
    """``record`` を ``comparison`` の中で作った比較の証拠として束縛する。

    ``identification`` は producer の申告の代役（既定は relation の premise の下の証拠。
    ``None`` は申告なし）。左右の同一視の検査（plan v4 PR-P）を見る test だけが変える。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        CrossSideIdentification,
        bind_evidence_to_comparison,
    )

    declared = None if identification is None else CrossSideIdentification(identification)
    return bind_evidence_to_comparison(record, comparison, identification=declared)
