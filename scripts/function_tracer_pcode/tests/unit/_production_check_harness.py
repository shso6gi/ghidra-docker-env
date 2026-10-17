# -*- coding: utf-8 -*-
"""Test support: 本番の check 経路を、Ghidra の解析だけ差し替えて走らせる（Issue #185）。

phase workflow・stage plan・strategy・z3 CLI・production cutover connector はすべて本物。
差し替えるのは ``EquivalenceChecker(analyzer_factory=...)``（Issue #109: production が
解析器を作る唯一の collaborator）だけで、fake の解析器は **本番と同じ公開境界**
（``publish_raw_function_analysis``: 意味値の公開と入力領域の封印）を通した新しい解析を
毎回返す。本番の再解析も毎回新しい解析を作るので、テンプレートの解析は公開前
（封印の無い）ものを渡す。

* z3 CLI が無ければ skip ではなく FAIL（recorded replay と同じ契約: 黙って通らない）。
* ``call_effect_manifest_failure``: call-effect manifest の構築を、指定した pair の
  ときだけ失敗させる注入 seam（``checker.preflight_gate`` が呼ぶ名前を差し替える）。
  manifest の構築失敗を pair failure にするのは S1b の責務で、この seam はその前提を
  作るだけ。
"""

from __future__ import annotations

from contextlib import contextmanager
import shutil
from typing import Any, Callable, Dict, Iterator, Optional

import pytest

from scripts.function_tracer_pcode.core.analysis import publish_raw_function_analysis
from scripts.function_tracer_pcode.core.parameter_domain import synthetic_parameter_kind


def require_z3_cli() -> None:
    if shutil.which("z3") is None:
        pytest.fail("the production check needs the z3 CLI on PATH (not skipped: a missing solver must not pass)")


def _activate_execution_authority(case_id: str) -> None:
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )

    activate_process_worker_execution_authority_deployment(
        key_id="e2e-" + case_id, key=(case_id.encode() * 32)[:32], key_source_id="/tmp/e2e-" + case_id,
    )


def _production_checker(analyzer_factory: Any = None, *, debug: bool = False) -> Any:
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        build_default_cutover_connector,
    )
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    checker = EquivalenceChecker(debug=debug, analyzer_factory=analyzer_factory)
    checker.v2_dual_write_pilot_connector = build_default_cutover_connector()
    return checker


def _require_unpublished(*templates: Any) -> None:
    for template in templates:
        assert getattr(template, "raw_parameter_domains", None) is None, (
            "pass the analysis as the analyzer produced it (before publication); the harness publishes it"
        )


def publish_like_the_analyzer(template: Any) -> Any:
    """本番の解析と同じく新しい解析を作り、同じ公開境界（公開と封印）を通す。"""

    return publish_raw_function_analysis(template.semantic_successor())


def run_production_check(
    case_id: str,
    left: Any,
    right: Any,
    *,
    left_architecture: str = "x86:LE:64:default",
    right_architecture: str = "x86:LE:64:default",
    retry_with_type_fix: bool = True,
    debug: bool = False,
    analyze: Optional[Callable[[Any], Any]] = None,
) -> Dict[str, Any]:
    """``left`` / ``right``（公開前の解析）を比べた production の結果（``to_dict()``）。

    ``retry_with_type_fix`` の既定は CLI と同じ（``--no-retry-phases`` を付けない実行）。
    ``analyze``（template → 公開した解析）の既定は ``publish_like_the_analyzer``（公開境界だけを通す）。
    解析器の公開前の段も本物で通すときは ``_analyzer_pipeline_harness.analyze_through_pipeline`` を渡す。
    """

    from scripts.function_tracer_pcode.tests.conftest import MockProgram

    require_z3_cli()
    _require_unpublished(left, right)
    _activate_execution_authority(case_id)
    table = {"left": left, "right": right}
    if analyze is None:
        analyze = publish_like_the_analyzer

    class FakeReturnAnalyzer:
        def __init__(self, program: Any, **_kwargs: Any) -> None:
            self._program = program

        def analyze_function_by_name(self, _name: str, _timeout: Any) -> Any:
            return analyze(table[self._program.getName()])

        def refresh_structural_recurrence_summary(self, analysis: Any, **_kwargs: Any) -> Any:
            return analysis

        def get_last_analysis_failure(self) -> Any:
            return None

        def get_last_function_lookup_error(self) -> Any:
            return None

        def dispose(self) -> None:
            pass

    from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
        entered_certificate_session,
    )

    checker = _production_checker(FakeReturnAnalyzer, debug=debug)
    # production の実行は自分で左右の同一視の証明書の session を持つ（test の既定の session を使わない）。
    with entered_certificate_session(None):
        result = checker.check_from_binaries(
            MockProgram("left", left_architecture), MockProgram("right", right_architecture), "f", "f",
            binary1_id="left-id", binary2_id="right-id",
            binary1_content_identity=("sha256", "a" * 64), binary2_content_identity=("sha256", "b" * 64),
            retry_with_type_fix=retry_with_type_fix,
        )
    return result.to_dict()


def run_recursive_abstraction_branch(case_id: str, left: Any, right: Any, *, debug: bool = False) -> Any:
    """再帰 abstraction の分岐（``S_ABSTRACT_RECURSIVE_SUMMARY`` の本体）を直接呼んだ checker の結果。"""

    require_z3_cli()
    _require_unpublished(left, right)
    _activate_execution_authority(case_id)
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
        entered_certificate_session,
    )

    checker = _production_checker(debug=debug)
    with entered_certificate_session(None):
        return checker._run_recursive_abstraction_stage(
            publish_like_the_analyzer(left), publish_like_the_analyzer(right),
            "left", "right", False, None, 0, None, None,
        )


def has_no_synthetic_parameter(analysis1: Any, analysis2: Any) -> bool:
    """raw pair（abstraction の前）か: どちらの表にも synthetic の名乗りが無い。"""

    return not any(
        synthetic_parameter_kind(param)
        for analysis in (analysis1, analysis2)
        for param in (getattr(analysis, "parameters", None) or ())
    )


@contextmanager
def call_effect_manifest_failure(when: Callable[[Any, Any], bool]) -> Iterator[list]:
    """``when(analysis1, analysis2)`` が真の pair だけ、call-effect manifest の構築を失敗させる。

    yield するのは失敗させた回数の記録（test が注入が本当に効いたことを確かめる）。
    """

    from scripts.function_tracer_pcode.checker import preflight_gate

    original = preflight_gate.build_call_effect_shadow_manifest
    injected: list = []

    def build(analysis1: Any, analysis2: Any, *args: Any, **kwargs: Any) -> Any:
        if when(analysis1, analysis2):
            injected.append((getattr(analysis1, "function_name", None), getattr(analysis2, "function_name", None)))
            raise RuntimeError("injected call-effect manifest construction failure")
        return original(analysis1, analysis2, *args, **kwargs)

    preflight_gate.build_call_effect_shadow_manifest = build
    try:
        yield injected
    finally:
        preflight_gate.build_call_effect_shadow_manifest = original
