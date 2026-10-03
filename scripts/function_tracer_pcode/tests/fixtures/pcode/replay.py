# -*- coding: utf-8 -*-
"""記録済み fixture を production path で再生する 1 つの入口（Issue #109）。

再生の経路定義はここにしか無い。往復 test（PR-A）と recorded-pair test
（PR-B）が同じ関数を呼ぶので、「production connector 付きの
``check_from_binaries`` を記録済み object の上で走らせる」という宣言が
test ごとに分かれて drift することがない。記録器（``tests/tools/
record_pcode_fixture.py``）も同じ collaborator（``recorded_analyzer_factory``
と同型の factory + ``build_default_cutover_connector`` + worker authority）で
実 Ghidra を回しており、record と replay で経路が違わない。

ここは **judgement を持たない**: outcome を書き換えない、欠落を既定値へ
丸めない、例外を UNKNOWN へ変換しない。呼び出し側が
:attr:`ReplayOutcome.failure` と ``missing_accesses`` を見て判定する。
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Mapping, Optional

from scripts.function_tracer_pcode.tests.fixtures.pcode.recorded_program import (
    RecordedProgram,
    recorded_analyzer_factory,
    recorded_program_from_payload,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.snapshot import (
    AnalysisSnapshotCollector,
)
from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget


#: 再生中に import させない runtime。``ImportError`` を出すのは Ghidra の
#: 無い環境と**同じ**振る舞いにするため（production には
#: ``from ghidra... import X`` を ``try/except`` で包んだ型判定 probe が
#: 複数あり、別の例外を出すとその経路だけ記録と食い違う）。
BLOCKED_RUNTIME_PREFIXES = ("ghidra", "pyghidra", "jpype")

#: 再生が「実 decompiler を組み立てる遅延生成」に入っていないことの見張り。
DECOMPILER_MODULE = "ghidra.app.decompiler"

#: 記録された object の kind のうち、decompile 結果（HighFunction / P-code /
#: varnode / DecompileResults）が属する Java package。fast path ON の再生が
#: これらを 1 つも読まないことを呼び出し側が assert できるようにする。
DECOMPILED_IR_PACKAGES = (
    "ghidra.program.model.pcode.",
    "ghidra.app.decompiler.",
)


class BlockedImportFinder:
    """再生中に Ghidra / PyGhidra / JPype を使わせない meta path finder。"""

    def __init__(self, *prefixes: str) -> None:
        self._prefixes = prefixes or BLOCKED_RUNTIME_PREFIXES
        self.blocked: List[str] = []

    def find_module(self, fullname, path=None):  # pragma: no cover - 互換 API
        return self.find_spec(fullname, path)

    def find_spec(self, fullname, path=None, target=None):
        for prefix in self._prefixes:
            if fullname == prefix or fullname.startswith(prefix + "."):
                self.blocked.append(fullname)
                raise ImportError(
                    "replay must not use a real Ghidra runtime: " + fullname
                )
        return None


@dataclass
class ReplayOutcome:
    """1 回の再生で観測できたものすべて。判定はしない。"""

    left: RecordedProgram
    right: RecordedProgram
    payload: Optional[Dict[str, Any]]
    collector: AnalysisSnapshotCollector
    result: Any
    failure: Optional[BaseException]
    checker: Any
    blocker: BlockedImportFinder
    identical_fast_path: bool
    analyzer_factory_calls: List[str] = field(default_factory=list)
    #: snapshot の再利用の観測（Issue #219）: `body_executions_in_scope` は本体を外から包んで
    #: 数えた、再利用の scope の中の実行回数。`stores` は閉じた scope ごとの計測値
    snapshot_reuse: Dict[str, Any] = field(default_factory=dict)

    def accessed_object_kinds(self) -> Dict[str, set]:
        """side → 実際に member を引かれた object の kind 集合。"""

        kinds = {}
        for side, program in (("left", self.left), ("right", self.right)):
            payload = program._rec_context.payload
            kinds[side] = {
                payload["objects"][object_id]["kind"]
                for object_id, _member in program.access_log
            }
        return kinds

    def decompiler_access_log(self) -> Dict[str, List[str]]:
        """side → ``RecordedDecompiler`` から引かれた member key の列。"""

        log = {}
        for side, program in (("left", self.left), ("right", self.right)):
            root = program._rec_context.roots["decompiler"]
            log[side] = [
                member for object_id, member in program.access_log
                if object_id == root
            ]
        return log

    def decompiled_ir_access_count(self) -> Dict[str, int]:
        """side → decompile 結果（HighFunction / P-code）を読んだ回数。"""

        counts = {}
        for side, program in (("left", self.left), ("right", self.right)):
            objects = program._rec_context.payload["objects"]
            counts[side] = sum(
                1 for object_id, _member in program.access_log
                if objects[object_id]["kind"].startswith(DECOMPILED_IR_PACKAGES)
            )
        return counts


def replay_recorded_pair(
    left_payload: Mapping[str, Any],
    right_payload: Mapping[str, Any],
    *,
    case_id: str,
    monkeypatch,
    identical_fast_path: Optional[bool] = None,
    configure_checker: Optional[Callable[[Any], None]] = None,
    analysis_deadline: Any = None,
) -> ReplayOutcome:
    """記録と同じ production path を、記録済み object の上で 1 回走らせる。

    ``identical_fast_path`` を省略すると **記録時の mode** を使う。呼び出し側が
    別の mode を指定できるのは、同一 fixture を ON / OFF の 2 variant で
    再生するため（Issue #15 の identical case）。
    """

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
        validate_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        build_default_cutover_connector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )
    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    left = recorded_program_from_payload(left_payload)
    right = recorded_program_from_payload(right_payload)
    left_header = left.fixture_header
    right_header = right.fixture_header
    if identical_fast_path is None:
        identical_fast_path = bool(
            left_header["recording_mode"]["identical_fast_path"]
        )

    activate_process_worker_execution_authority_deployment(
        key_id="issue109-replay-" + case_id,
        key=(case_id.encode() * 32)[:32],
        key_source_id="/tmp/issue109-replay-" + case_id,
    )
    blocker = BlockedImportFinder()
    monkeypatch.setattr(sys, "meta_path", [blocker, *sys.meta_path])

    collector = AnalysisSnapshotCollector()
    analyzer_factory_calls: List[str] = []
    snapshot_reuse = _observe_snapshot_reuse(monkeypatch)

    def _analyzer_factory(program, **kwargs):
        analyzer_factory_calls.append(getattr(program, "_rec_object_id", "?"))
        return recorded_analyzer_factory(program, **kwargs)

    checker = EquivalenceChecker(
        debug=False,
        identical_fast_path=identical_fast_path,
        analyzer_factory=collector.wrap(_analyzer_factory),
    )
    checker.v2_dual_write_pilot_connector = build_default_cutover_connector()
    if configure_checker is not None:
        configure_checker(checker)

    payload: Optional[Dict[str, Any]] = None
    failure: Optional[BaseException] = None
    result: Any = None
    try:
        result = checker.check_from_binaries(
            left, right,
            left_header["target"]["function_name"],
            right_header["target"]["function_name"],
            binary1_id=left_header["binary"]["binary_id"],
            binary2_id=right_header["binary"]["binary_id"],
            binary1_content_identity=("sha256", left_header["binary"]["sha256"]),
            binary2_content_identity=("sha256", right_header["binary"]["sha256"]),
            analysis_deadline=analysis_deadline,
        )
        payload = result.to_dict()
        finalization = getattr(result, "_canonical_finalization_context", None)
        if finalization is not None:
            evidence, session = finalization
            bundle = build_canonical_result_finalization_bundle(
                result_payload_preimage=payload,
                evidence=evidence, session=session, work=SealWorkBudget.for_result()
            )
            validate_canonical_result_finalization_bundle(
                bundle, result_payload_preimage=payload, work=SealWorkBudget.for_result()
            )
            payload["canonical_result_finalization_bundle"] = bundle
    except Exception as exc:  # 欠落注入では production 側が途中で落ちることもある
        failure = exc
        result = None
    return ReplayOutcome(
        left=left, right=right, payload=payload, collector=collector,
        result=result, failure=failure, checker=checker, blocker=blocker,
        identical_fast_path=bool(identical_fast_path),
        analyzer_factory_calls=analyzer_factory_calls,
        snapshot_reuse=snapshot_reuse,
    )


def _observe_snapshot_reuse(monkeypatch) -> Dict[str, Any]:
    """snapshot の本体の実行を外から数え、閉じた再利用の scope の計測値を集める（判定はしない）。

    数え方を再利用の判断に頼らない: canonical な経路の本体（読んだ値から snapshot を作る
    `assemble_snapshot`）を包み、再利用の scope の中で実際に走った回数を数える。
    """

    from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse as reuse

    observed: Dict[str, Any] = {"body_executions_in_scope": 0, "stores": []}
    assemble = reuse.assemble_snapshot
    release = reuse.SnapshotReuse.release

    def counted_assemble(read, **kwargs):
        if reuse.snapshot_reuse_metrics():
            observed["body_executions_in_scope"] += 1
        return assemble(read, **kwargs)

    def observed_release(store):
        observed["stores"].append(store.metrics())
        return release(store)

    monkeypatch.setattr(reuse, "assemble_snapshot", counted_assemble)
    monkeypatch.setattr(reuse.SnapshotReuse, "release", observed_release)
    return observed


def assert_no_real_decompiler_was_built(outcome: ReplayOutcome) -> None:
    """実 ``DecompInterface`` の遅延生成に入っていないこと。

    型判定 probe の import 失敗は Ghidra 無し環境と同じなので許すが、
    ``lifecycle.get_decompiler`` が decompiler module を import しようと
    したなら、それは再生が記録の外へ出たということ。
    """

    assert DECOMPILER_MODULE not in sys.modules
    assert DECOMPILER_MODULE not in outcome.blocker.blocked


class SimplePatcher:
    """``monkeypatch.setattr`` だけを持つ最小の差し替え器。

    子 process で 1 回再生して終了する worker 用（pytest に依存しない）。
    """

    def setattr(self, target: Any, name: str, value: Any) -> None:
        setattr(target, name, value)


REPLAY_REPORT_SCHEMA = "recorded-pair-replay-report-v1"


def replay_report(
    outcome: ReplayOutcome, *, case_id: str, variant: str, seconds: float,
    solver_forbidden: bool,
) -> Dict[str, Any]:
    """1 回の再生で観測できたものを JSON にする（判定はしない）。

    判定は親 process が行う。ここで「合格/不合格」に畳むと、子が自分の
    結果を採点することになって test の意味が薄くなる。
    """

    return {
        "schema": REPLAY_REPORT_SCHEMA,
        "case_id": case_id,
        "variant": variant,
        "identical_fast_path": outcome.identical_fast_path,
        "solver_forbidden": bool(solver_forbidden),
        "seconds": seconds,
        "failure": None if outcome.failure is None else {
            "type": type(outcome.failure).__name__,
            "message": str(outcome.failure),
        },
        "payload": outcome.payload,
        "missing_accesses": {
            side: [list(access.as_tuple()) for access in program.missing_accesses]
            for side, program in (("left", outcome.left), ("right", outcome.right))
        },
        "analyzer_factory_calls": list(outcome.analyzer_factory_calls),
        "snapshot_reuse": outcome.snapshot_reuse,
        "decompiler_access": outcome.decompiler_access_log(),
        "decompiled_ir_access": outcome.decompiled_ir_access_count(),
        "decompiler_module_imported": DECOMPILER_MODULE in sys.modules,
        "decompiler_module_blocked": DECOMPILER_MODULE in outcome.blocker.blocked,
        "blocked_imports": sorted(set(outcome.blocker.blocked)),
    }


__all__ = [
    "BLOCKED_RUNTIME_PREFIXES",
    "BlockedImportFinder",
    "DECOMPILED_IR_PACKAGES",
    "DECOMPILER_MODULE",
    "REPLAY_REPORT_SCHEMA",
    "ReplayOutcome",
    "SimplePatcher",
    "assert_no_real_decompiler_was_built",
    "replay_recorded_pair",
    "replay_report",
]
