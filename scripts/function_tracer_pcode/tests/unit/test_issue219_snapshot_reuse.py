# -*- coding: utf-8 -*-
"""snapshot の再利用（Issue #219 PR-219-B、C-RS1 / C-RS3〜C-RS8 と、C-RS2 との接続）。

「いつ再利用してよいか」の invariant を固定する。oracle は再利用の実装ではなく:

* **本体**（`AnalysisSnapshot._build_from_function_analysis` をその時点で直接呼んだ結果。memo を
  通らない snapshot）
* **memo を切った経路**（`snapshot_reuse._SNAPSHOT_REUSE_ENABLED = False`）
* **writer**（解析・共有 list・共有要約・#191 の注記を、production と同じ書き方で書き換える）
* **実際の scope 境界**（`snapshot_reuse_scope` と、production の pair 境界）

本体の実行回数は、本体の関数を外から包んで数える（store の計測値は、その数と一致すること
だけを確かめる）。store の型・counter の名前の詳細は assert しない。
"""

from __future__ import annotations

import dataclasses
import enum
import random
import threading
from typing import Any, List

import pytest

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary
from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo, ReturnInfo
from scripts.function_tracer_pcode.core.budget_policy import (
    BudgetPolicy,
    budget_observations,
    budget_policy_scope,
    serialization_scope,
)
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.errors import (
    ExpressionSizeBudgetExceeded,
    InternalError,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted
from scripts.function_tracer_pcode.core import CallTargetRef
from scripts.function_tracer_pcode.core.runtime_refs import PcodeOpRef
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    serialization_closed,
    serialization_pending,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.proof.obligations import snapshot as snapshot_module
from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    SNAPSHOT_SERIALIZATION_SITE,
    AnalysisSnapshot,
    SnapshotFingerprintCodec,
    record_comparison_annotation,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import (
    ElidedSemanticValue,
    snapshot_reuse_metrics,
    snapshot_reuse_scope,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


# ---------------------------------------------------------------------------
# 材料
# ---------------------------------------------------------------------------


_RAW_BUILD = AnalysisSnapshot.__dict__["_build_from_function_analysis"].__func__


_ORACLE = threading.local()


def body(analysis: Any) -> AnalysisSnapshot:
    """oracle: memo を通らない本体（その時点の解析の状態の snapshot。本体の実行回数には数えない）。"""

    _ORACLE.active = True
    try:
        return _RAW_BUILD(AnalysisSnapshot, analysis)
    finally:
        _ORACLE.active = False


def fields_of(snapshot: AnalysisSnapshot) -> tuple:
    """snapshot の比べる全 field（`diagnostic_refs` の object は identity で）。"""

    refs = dict(snapshot.diagnostic_refs)
    function_ref = refs.pop("function_ref", None)
    return (
        snapshot.snapshot_id,
        dict(snapshot.semantic_fields),
        snapshot.semantic_fingerprint,
        snapshot.comparison_fingerprint,
        snapshot.extraction_schema_version,
        refs,
        id(function_ref),
    )


class BodyCounter:
    """本体（高コストな部分）の実行回数を外から数える。

    canonical な経路は読み（`read_snapshot_inputs`）の後の `assemble_snapshot`、通常の本体へ回した経路は
    `snapshot_material` の呼び出しのうち読みの外のもの（main の本体）。`hook(analysis)` は本体を作る前に呼ぶ
    （読みの直後: 入力の読みの後、snapshot を作る前）。
    """

    def __init__(self, monkeypatch, hook=None) -> None:
        self.calls: List[Any] = []
        self.reads: List[Any] = []
        self.hook = hook
        lock = threading.Lock()
        original_read = snapshot_reuse.read_snapshot_inputs
        original_assemble = snapshot_reuse.assemble_snapshot
        original_material = snapshot_module.snapshot_material
        reading = threading.local()

        def counted_read(analysis, leaf_substitution=None):
            with lock:
                self.reads.append(analysis)
            reading.active = True
            try:
                read = original_read(analysis, leaf_substitution)
            finally:
                reading.active = False
            read_analyses[id(read)] = analysis
            return read

        read_analyses = {}

        def counted_assemble(read):
            analysis = read_analyses.pop(id(read), None)
            with lock:
                self.calls.append(analysis)
            if self.hook is not None:
                self.hook(analysis)
            return original_assemble(read)

        def counted_material(analysis, *args, **kwargs):
            if not getattr(reading, "active", False) and not getattr(_ORACLE, "active", False):
                with lock:
                    self.calls.append(analysis)
                if self.hook is not None:
                    self.hook(analysis)
            return original_material(analysis, *args, **kwargs)

        monkeypatch.setattr(snapshot_reuse, "read_snapshot_inputs", counted_read)
        monkeypatch.setattr(snapshot_reuse, "assemble_snapshot", counted_assemble)
        monkeypatch.setattr(snapshot_module, "snapshot_material", counted_material)

    @property
    def count(self) -> int:
        return len(self.calls)


@pytest.fixture
def bodies(monkeypatch):
    return BodyCounter(monkeypatch)


def _storage(name: str, offset: int = 8) -> StorageInfo:
    return StorageInfo(
        is_register=True, space_name="register", offset=offset, size=4,
        register_name=name, base_register_name=name,
    )


def _param(name: str, index: int = 0) -> Expression:
    return Expression.parameter(name, index, size=4, storage_info=_storage("x%d" % index, offset=8 * index))


def _value(seed: int) -> Expression:
    guard = Condition(Expression.binary_op("INT_LESS", _param("a"), Expression.constant(seed, size=4)))
    body_expr = Expression.binary_op("INT_ADD", _param("a"), Expression.constant(seed, size=4))
    return Expression.phi([(guard, body_expr), (None, Expression.constant(0, size=4))])


def _analysis(name: str = "f", *, seed: int = 1, effect: Any = None, value: Any = None) -> Any:
    analysis = create_mock_analysis(
        name,
        parameters=[{"name": "a", "data_type": "int"}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[Condition(Expression.binary_op("INT_EQUAL", _param("a"), Expression.constant(seed, size=4)))],
                value=_value(seed) if value is None else value,
            ),
            ReturnInfo(address="0x00401010", conditions=[], value=Expression.constant(seed + 1, size=4)),
        ],
    )
    if effect is not None:
        analysis.effect_summary = effect
    return analysis


@pytest.fixture
def pair_scope():
    """production の pair と同じ: 予算の scope と再利用の scope を同じ寿命で開く。"""

    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope() as store:
        yield store


def _counts() -> dict:
    return snapshot_reuse_metrics().get("counts", {})


# ---------------------------------------------------------------------------
# T-B1 同一 witness / T-B2 別 object・同一 read-set
# ---------------------------------------------------------------------------


def test_t_b1_the_same_analysis_through_three_production_paths_builds_once(pair_scope, bodies):
    from scripts.function_tracer_pcode.proof.call_effect.preflight import (
        _analysis_digest,
        _changed_semantic_roots,
    )
    from scripts.function_tracer_pcode.proof.obligations.runtime import ObligationRuntimeSession

    analysis = _analysis()
    oracle = body(analysis)

    digest = _analysis_digest(analysis)
    changed = _changed_semantic_roots(analysis, analysis)
    snapshot = ObligationRuntimeSession._snapshot(analysis, "left")

    assert bodies.count == 1
    assert digest == oracle.semantic_fingerprint
    assert changed == ()
    assert fields_of(snapshot) == fields_of(oracle)
    assert _counts()["body_executions"] == bodies.count


def test_t_b2_a_replaced_view_with_the_same_read_set_reuses_the_body(pair_scope, bodies):
    raw = _analysis()
    view = dataclasses.replace(raw)
    assert view is not raw and view.analysis_notes is raw.analysis_notes

    first = AnalysisSnapshot.from_function_analysis(raw)
    second = AnalysisSnapshot.from_function_analysis(view)

    assert bodies.count == 1
    assert fields_of(second) == fields_of(body(view)) == fields_of(first)


# ---------------------------------------------------------------------------
# T-B3 書き換え / T-B4 共有 list / T-B5 共有要約 / T-B6 #191 の注記
# ---------------------------------------------------------------------------


def _deferred_call() -> DeferredCallInfo:
    return DeferredCallInfo(
        placeholder_name="call_1",
        target_ref=CallTargetRef.from_name("g", program_id=7, entry_offset=0x2000),
        arguments=[_param("a")],
        sequence=1,
    )


def _mutations():
    """解析の書き換え（in-place・`__setattr__` を通るもの・通らないもの）。"""

    def in_place_return(analysis):
        analysis.returns[0].address = "0x00409999"

    def parameter_entry(analysis):
        analysis.parameters[0]["name"] = "renamed"

    def note_append(analysis):
        analysis.analysis_notes.append("indirect_control_flow_unresolved")

    def deferred_value(analysis):
        analysis.deferred_calls[next(iter(analysis.deferred_calls))].effect_class = "pure"

    def return_conditions(analysis):
        analysis.returns[1].conditions.append(
            Condition(Expression.binary_op("INT_LESS", _param("a"), Expression.constant(99, size=4)))
        )

    def attribute_assignment(analysis):
        analysis.unknown_event_count = 5

    return [in_place_return, parameter_entry, note_append, deferred_value, return_conditions, attribute_assignment]


@pytest.mark.parametrize("mutate", _mutations(), ids=lambda fn: fn.__name__)
def test_t_b3_a_mutation_after_caching_is_never_served_stale(pair_scope, bodies, mutate):
    analysis = _analysis()
    call = _deferred_call()
    analysis.deferred_calls = {call.deferred_call_ref.stable_key(): call}
    before = AnalysisSnapshot.from_function_analysis(analysis)
    assert fields_of(AnalysisSnapshot.from_function_analysis(analysis)) == fields_of(before)
    built = bodies.count

    mutate(analysis)

    after = AnalysisSnapshot.from_function_analysis(analysis)
    assert fields_of(after) == fields_of(body(analysis))
    assert after.semantic_fields != before.semantic_fields
    assert bodies.count == built + 1


@pytest.mark.parametrize(
    "before, after",
    [(True, 1), (1, 1.0), (0.0, -0.0), (1, "1"), ((1, 2), [1, 2, 0])],
    ids=["bool_to_int", "int_to_float", "zero_sign", "int_to_str", "sequence_length"],
)
def test_t_b3_a_change_that_equality_would_hide_is_never_served_stale(pair_scope, bodies, before, after):
    """`==` で等しい値の違い（`True` / `1` / `1.0`、`0.0` / `-0.0`）も witness を変える。"""

    analysis = _analysis()
    analysis.return_abi_facts = {"probe": before}
    first = AnalysisSnapshot.from_function_analysis(analysis)

    analysis.return_abi_facts["probe"] = after

    second = AnalysisSnapshot.from_function_analysis(analysis)
    assert fields_of(second) == fields_of(body(analysis))
    assert second.semantic_fingerprint != first.semantic_fingerprint
    assert bodies.count == 2


class _Mode(str, enum.Enum):
    A = "a"
    B = "b"


class _Level(enum.IntEnum):
    LOW = 1
    HIGH = 2


@pytest.mark.parametrize("before, after", [(_Mode.A, _Mode.B), (_Level.LOW, _Level.HIGH), (_Mode.A, "a")])
def test_t_b3_enum_members_in_the_material_are_compared_and_reused(pair_scope, bodies, before, after):
    """mixin の enum の member（codec が写しにそのまま置く値）も witness の材料になり、再利用もできる。"""

    analysis = _analysis()
    analysis.effect_summary = EffectSummary([], [], incomplete_reasons=(before,))
    first = AnalysisSnapshot.from_function_analysis(analysis)
    assert fields_of(AnalysisSnapshot.from_function_analysis(analysis)) == fields_of(first)
    assert bodies.count == 1 and "bypass:witness_failed:RecursionError" not in _counts()

    analysis.effect_summary.incomplete_reasons = (after,)

    second = AnalysisSnapshot.from_function_analysis(analysis)
    assert fields_of(second) == fields_of(body(analysis))
    assert bodies.count == 2


def test_t_b4_a_write_to_a_shared_list_rebuilds_the_view_that_did_not_write(pair_scope, bodies):
    raw = _analysis()
    view = dataclasses.replace(raw)
    stale = AnalysisSnapshot.from_function_analysis(view)

    raw.analysis_notes.append("symbolic_post_state_reads")

    fresh = AnalysisSnapshot.from_function_analysis(view)
    assert fields_of(fresh) == fields_of(body(view))
    assert fresh.semantic_fingerprint != stale.semantic_fingerprint


def test_t_b5_a_shared_effect_summary_change_rebuilds_both_owners(pair_scope, bodies):
    shared = EffectSummary([], [], incomplete_reasons=("effect_path_gap",))
    left = _analysis("f", effect=shared)
    right = _analysis("g", effect=shared)
    before = [AnalysisSnapshot.from_function_analysis(item) for item in (left, right)]
    built = bodies.count

    shared.incomplete_reasons = ("effect_path_gap", "callee_effect_unknown")

    after = [AnalysisSnapshot.from_function_analysis(item) for item in (left, right)]
    assert [fields_of(item) for item in after] == [fields_of(body(left)), fields_of(body(right))]
    assert all(a.semantic_fingerprint != b.semantic_fingerprint for a, b in zip(after, before))
    assert bodies.count == built + 2


def test_t_b6_a_comparison_annotation_rebuilds_the_raw_and_its_sharing_surface_only(pair_scope, bodies):
    raw = _analysis("f")
    surface = dataclasses.replace(raw)
    unrelated = _analysis("g", seed=3)
    for item in (raw, surface, unrelated):
        AnalysisSnapshot.from_function_analysis(item)
    unrelated_before = bodies.calls.count(unrelated)

    record_comparison_annotation(raw, "return_case_coverage_gap")

    for item in (raw, surface):
        snapshot = AnalysisSnapshot.from_function_analysis(item)
        assert fields_of(snapshot) == fields_of(body(item))
        assert "return_case_coverage_gap" in snapshot.semantic_fields["semantic_analysis_notes"]
    AnalysisSnapshot.from_function_analysis(unrelated)
    assert bodies.calls.count(unrelated) == unrelated_before


# ---------------------------------------------------------------------------
# T-B7 reanalysis / T-B8 derived view
# ---------------------------------------------------------------------------


def test_t_b7_a_reanalysis_with_new_objects_misses_and_the_same_object_hits(pair_scope, bodies):
    first = _analysis()
    again = _analysis()  # 同じ内容・新しい式の object（再解析）
    original = AnalysisSnapshot.from_function_analysis(first)
    rebuilt = AnalysisSnapshot.from_function_analysis(again)
    assert bodies.count == 2
    assert rebuilt.semantic_fingerprint == original.semantic_fingerprint

    cached = AnalysisSnapshot.from_function_analysis(first)  # analyzer cache が同じ object を返した
    assert bodies.count == 2
    assert fields_of(cached) == fields_of(body(first))


def _derived_views(raw):
    replaced_return = dataclasses.replace(
        raw, returns=[raw.returns[0], ReturnInfo(address="0x00401010", conditions=[], value=Expression.constant(9, size=4))],
    )
    other_effect = dataclasses.replace(raw, effect_summary=EffectSummary([], [], incomplete_reasons=("x",)))
    other_scope = dataclasses.replace(raw, analysis_scope_key=("analysis_scope", "other"))
    same_ref_value = CallTargetRef.from_name("f", program_id=raw.function_ref.program_id, entry_offset=0x00401000)
    other_ref_object = dataclasses.replace(raw, function_ref=same_ref_value)
    return {
        "returns": replaced_return,
        "effect_summary": other_effect,
        "analysis_scope_key": other_scope,
        "function_ref_object": other_ref_object,
    }


@pytest.mark.parametrize("which", ["returns", "effect_summary", "analysis_scope_key", "function_ref_object"])
def test_t_b8_a_derived_view_that_differs_in_one_field_does_not_inherit(pair_scope, bodies, which):
    raw = _analysis()
    AnalysisSnapshot.from_function_analysis(raw)
    view = _derived_views(raw)[which]

    snapshot = AnalysisSnapshot.from_function_analysis(view)

    assert bodies.count == 2
    assert fields_of(snapshot) == fields_of(body(view))
    assert snapshot.diagnostic_refs["function_ref"] is view.function_ref


def test_t_b8_a_derived_view_that_only_shares_inherits(pair_scope, bodies):
    raw = _analysis()
    first = AnalysisSnapshot.from_function_analysis(raw)
    view = dataclasses.replace(raw)
    assert fields_of(AnalysisSnapshot.from_function_analysis(view)) == fields_of(first)
    assert bodies.count == 1


# ---------------------------------------------------------------------------
# T-B9 pair scope / T-B10 入れ子の scope / T-B11 policy
# ---------------------------------------------------------------------------


def test_t_b9_outside_a_scope_every_call_builds_and_a_closed_scope_keeps_nothing(bodies):
    analysis = _analysis()
    with budget_policy_scope(BudgetPolicy()):
        AnalysisSnapshot.from_function_analysis(analysis)
        AnalysisSnapshot.from_function_analysis(analysis)
        assert bodies.count == 2
        assert snapshot_reuse_metrics() == {}
        with snapshot_reuse_scope():
            AnalysisSnapshot.from_function_analysis(analysis)
            AnalysisSnapshot.from_function_analysis(analysis)
        assert bodies.count == 3
        AnalysisSnapshot.from_function_analysis(analysis)
        assert bodies.count == 4


def test_t_b9_closing_the_scope_releases_the_values_the_tokens_held():
    import gc
    import weakref

    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope() as store:
        analysis = _analysis()
        AnalysisSnapshot.from_function_analysis(analysis)
        held = weakref.ref(analysis.returns[0].value)
        del analysis
        gc.collect()
        assert held() is not None  # entry の token が強参照を持つ（id は再利用されない）
    gc.collect()
    # store を持ち続ける側があっても、scope を抜けた entry は値を離している
    assert held() is None and store.metrics()["entries"] == 0


def test_t_b9_both_pair_boundary_paths_open_one_store_with_the_budget_scope_lifetime(monkeypatch):
    from scripts.function_tracer_pcode.core import budget_policy
    from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
        _analyses,
        _healthy_stage_plan,
        _run_pair,
    )
    from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
        _connector,
    )

    analysis1, analysis2 = _analyses()
    seen = []
    counter = BodyCounter(monkeypatch)

    def _analyze(self, name, timeout):
        analysis = analysis1 if name == "func1" else analysis2
        AnalysisSnapshot.from_function_analysis(analysis)
        seen.append((snapshot_reuse._active_store(), budget_policy._active_scope(), counter.count))
        return analysis

    for connector in (_connector(), None, _connector()):
        before = counter.count
        _run_pair(analyze=_analyze, stage_plan=_healthy_stage_plan, connector=connector)
        assert snapshot_reuse._active_store() is None
        assert budget_policy._active_scope() is None
        assert counter.count > before

    stores = [store for store, _scope, _count in seen]
    scopes = [scope for _store, scope, _count in seen]
    assert all(store is not None for store in stores)
    # 1 pair の中は同じ store・同じ予算の scope、pair が変われば両方とも新しい
    for index in (0, 2, 4):
        assert stores[index] is stores[index + 1] and scopes[index] is scopes[index + 1]
    assert len({id(store) for store in stores}) == 3
    assert len({id(scope) for scope in scopes}) == 3
    # 前の pair の entry は次の pair で使わない（各 pair の最初の呼び出しは本体を実行する）
    counts = [count for _store, _scope, count in seen]
    assert counts[2] > counts[1] and counts[4] > counts[3]


def test_t_b10_a_nested_scope_does_not_see_the_outer_entries(pair_scope, bodies):
    analysis = _analysis()
    AnalysisSnapshot.from_function_analysis(analysis)
    with snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(analysis)
        assert bodies.count == 2
        AnalysisSnapshot.from_function_analysis(analysis)
        assert bodies.count == 2
    AnalysisSnapshot.from_function_analysis(analysis)
    assert bodies.count == 2


def test_t_b8_equal_content_in_other_objects_is_another_read_set(bodies):
    """内容の等しい別 object の式は同じ read-set ではない（DAG の共有が違えば本体の node の勘定が違う）。"""

    from scripts.function_tracer_pcode.core.budget_policy import BudgetKind

    shared = _value(1)
    sharing = _analysis("f", value=shared)
    sharing.returns[1].value = shared  # 2 つの return が同じ object
    # 残りの材料（条件・function_ref・表）は共有し、return の値だけ内容の同じ別 object にする
    distinct = dataclasses.replace(
        sharing,
        returns=[
            dataclasses.replace(sharing.returns[0], value=_value(1)),
            dataclasses.replace(sharing.returns[1], value=_value(1)),
        ],
    )
    from scripts.function_tracer_pcode.tests.unit._publication import published

    for item in distinct.returns:
        published(item.value)
    assert [item.value.to_dict() for item in sharing.returns] == [item.value.to_dict() for item in distinct.returns]

    def nodes(analysis):
        with budget_policy_scope(BudgetPolicy()):
            with serialization_scope(site="probe", target_parts=("p",)) as work:
                snapshot_module.snapshot_material(analysis, analysis.to_dict, work)
                return work.distinct_nodes

    limit = nodes(sharing)
    assert nodes(distinct) > limit
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy(serialization_nodes=limit)):
        with snapshot_reuse_scope():
            AnalysisSnapshot.from_function_analysis(sharing)
            with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
                AnalysisSnapshot.from_function_analysis(distinct)
    assert BudgetKind.SERIALIZATION_NODES.value in " ".join(caught.value.evidence_refs)


def test_t_b11_a_different_policy_does_not_hit_the_same_store(bodies):
    analysis = _analysis()
    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(analysis)
        with budget_policy_scope(BudgetPolicy(serialization_bytes=1_000_000)):
            inner = AnalysisSnapshot.from_function_analysis(analysis)
            assert bodies.count == 2
            assert fields_of(inner) == fields_of(body(analysis))
            # 値の等しい policy（別 object）は同じ本体の入力
            with budget_policy_scope(BudgetPolicy(serialization_bytes=1_000_000)):
                AnalysisSnapshot.from_function_analysis(analysis)
            assert bodies.count == 2
        AnalysisSnapshot.from_function_analysis(analysis)
        assert bodies.count == 2


def test_t_b11_a_policy_that_makes_the_body_fail_is_not_served_from_a_permissive_entry(bodies):
    analysis = _analysis()
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(analysis)
        with budget_policy_scope(BudgetPolicy(serialization_bytes=64)):
            with pytest.raises(ExpressionSizeBudgetExceeded):
                AnalysisSnapshot.from_function_analysis(analysis)


# ---------------------------------------------------------------------------
# T-B12 同時の初回アクセス / T-B13 build の途中の書き換え（C-RS8）
# ---------------------------------------------------------------------------


def test_t_b12_concurrent_first_access_builds_twice_and_keeps_one_entry(monkeypatch):
    barrier = threading.Barrier(2, timeout=30)
    counter = BodyCounter(monkeypatch, hook=lambda _analysis: barrier.wait())
    analysis = _analysis()
    oracle = body(analysis)
    results: List[Any] = [None, None]
    errors: List[BaseException] = []

    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope() as store:

        def run(index: int) -> None:
            try:
                results[index] = AnalysisSnapshot.from_function_analysis(analysis)
            except BaseException as exc:  # noqa: BLE001 - test が thread の失敗を持ち帰る
                errors.append(exc)

        threads = [threading.Thread(target=run, args=(index,)) for index in range(2)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(60)
        assert errors == []
        # 本体は lock の外: 2 つの本体が同時に barrier まで来た（重複実行を許す）
        assert counter.count == 2
        assert fields_of(results[0]) == fields_of(results[1]) == fields_of(oracle)
        assert store.metrics()["entries"] == 1
        assert _counts()["body_executions"] == 2 and _counts()["stores"] == 1
        # store は壊れていない: 次の呼び出しは hit（本体を実行しない）
        counter.hook = None
        assert fields_of(AnalysisSnapshot.from_function_analysis(analysis)) == fields_of(oracle)
        assert counter.count == 2


def test_t_b13_a_write_after_the_read_is_seen_by_the_next_call(monkeypatch):
    """読みの後・snapshot を作る前の書き換え（同じ thread）: その呼び出しは読んだ時点の snapshot、次の
    呼び出しは書き換えた後の snapshot。

    snapshot は読んだ値の純粋な関数なので、読みの後の書き換えはその呼び出しの結果を変えない（main の本体も
    読んだ値から snapshot を作る）。C-RS8 の前提（別の thread が生成中に書き換えない）は変えない。
    """

    analysis = _analysis()
    read_time = body(analysis)
    written = []

    def write_once(target):
        if not written:
            written.append(True)
            target.analysis_notes.append("indirect_control_flow_unresolved")

    counter = BodyCounter(monkeypatch, hook=write_once)
    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope() as store:
        first = AnalysisSnapshot.from_function_analysis(analysis)
        assert fields_of(first)[:6] == fields_of(read_time)[:6]
        after = AnalysisSnapshot.from_function_analysis(analysis)
        assert counter.count == 2 and store.metrics()["entries"] == 2
        assert fields_of(after) == fields_of(body(analysis))
        assert after.semantic_fingerprint != first.semantic_fingerprint


# ---------------------------------------------------------------------------
# T-B14 on / off の全 field 一致
# ---------------------------------------------------------------------------


def _random_analysis(rng: random.Random, name: str) -> Any:
    from scripts.function_tracer_pcode.tests.unit.test_issue219_serialization_closed import _random_expression

    returns = []
    for index in range(rng.randrange(1, 4)):
        returns.append(
            ReturnInfo(
                address="0x%08x" % (0x401000 + index),
                conditions=[Condition(_random_expression(rng, 2, []))] if rng.random() < 0.5 else [],
                value=_random_expression(rng, 3, []),
            )
        )
    analysis = create_mock_analysis(name, parameters=[{"name": "a", "data_type": "int"}], returns=returns)
    if rng.random() < 0.5:
        analysis.effect_summary = EffectSummary([], [], incomplete_reasons=("r%d" % rng.randrange(3),))
    return analysis


def _scenario(seed: int):
    """解析の列と、その間の書き換え・派生（on / off で同じ順に行う）。"""

    rng = random.Random(seed)
    analyses = [_random_analysis(rng, "f%d" % index) for index in range(3)]
    steps = []
    for _ in range(12):
        choice = rng.randrange(5)
        target = rng.randrange(len(analyses))
        if choice == 0:
            steps.append(("note", target))
        elif choice == 1:
            steps.append(("replace", target))
        elif choice == 2:
            steps.append(("annotate", target))
        else:
            steps.append(("snapshot", target))
    return analyses, steps


def _play(analyses, steps):
    out = []
    for kind, target in steps:
        analysis = analyses[target]
        if kind == "note":
            analysis.analysis_notes.append("symbolic_post_state_reads")
        elif kind == "replace":
            analyses.append(dataclasses.replace(analysis))
        elif kind == "annotate":
            record_comparison_annotation(analysis, "return_case_coverage_gap")
        else:
            snapshot = AnalysisSnapshot.from_function_analysis(analysis)
            # 呼び出しの時点の本体と全 field が等しい（stale ではない）
            assert fields_of(snapshot) == fields_of(body(analysis))
            out.append(fields_of(snapshot)[:6])
    for analysis in analyses:
        snapshot = AnalysisSnapshot.from_function_analysis(analysis)
        assert fields_of(snapshot) == fields_of(body(analysis))
        out.append(fields_of(snapshot)[:6])
    return out


@pytest.mark.parametrize("seed", range(12))
def test_t_b14_memo_on_and_off_return_identical_snapshots(monkeypatch, seed):
    results = {}
    for enabled in (True, False):
        monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", enabled)
        analyses, steps = _scenario(seed)
        with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
            results[enabled] = _play(analyses, steps)
    assert results[True] == results[False]


def test_t_b14_a_pair_has_the_same_outcome_and_reasons_with_memo_on_and_off(monkeypatch):
    from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
        _healthy_stage_plan,
        _run_pair,
    )
    from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
        _connector,
    )

    outcomes = {}
    for enabled in (True, False):
        monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", enabled)
        analysis1, analysis2 = _analysis("func1"), _analysis("func2", seed=2)

        def _analyze(self, name, timeout, _pair=(analysis1, analysis2)):
            return _pair[0] if name == "func1" else _pair[1]

        result = _run_pair(analyze=_analyze, stage_plan=_healthy_stage_plan, connector=_connector())
        payload = result.to_dict()
        outcomes[enabled] = (
            payload.get("final_outcome"),
            sorted(reason.reason_id for reason in result.unknown_reasons),
            payload.get("is_equivalent"),
        )
    assert outcomes[True] == outcomes[False]


# ---------------------------------------------------------------------------
# T-B15 例外の原子性 / T-B16 witness の失敗
# ---------------------------------------------------------------------------


def test_t_b15_a_budget_failure_of_the_body_leaves_the_store_empty_and_repeats(bodies):
    analysis = _analysis()
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy(serialization_bytes=64)):
        with snapshot_reuse_scope() as store:
            raised = []
            for _ in range(2):
                with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
                    AnalysisSnapshot.from_function_analysis(analysis)
                raised.append((type(caught.value), caught.value.site))
            assert store.metrics()["entries"] == 0
            # 読み（本体と同じ scope・上限）が上げる: snapshot は作らない
            assert bodies.count == 0 and len(bodies.reads) == 2
        assert raised[0] == raised[1] == (ExpressionSizeBudgetExceeded, SNAPSHOT_SERIALIZATION_SITE)


def test_t_b15_a_type_error_of_the_body_leaves_the_store_empty_and_repeats(pair_scope, bodies):
    analysis = _analysis()
    analysis.return_abi_facts = {"opaque": object()}
    for _ in range(2):
        with pytest.raises(Exception) as caught:
            AnalysisSnapshot.from_function_analysis(analysis)
        with pytest.raises(type(caught.value)):
            body(analysis)
    assert pair_scope.metrics()["entries"] == 0


@pytest.mark.parametrize("where", ["witness", "store"])
def test_t_b16_a_comparison_too_deep_to_judge_builds_without_storing(monkeypatch, pair_scope, bodies, where):
    """witness を比べられない（再帰の深さ）ときは保存せずに作る（結果は同じ純粋な関数: 本体と同じ）。"""

    analysis = _analysis()

    def too_deep(*_args, **_kwargs):
        raise RecursionError("deep")

    if where == "witness":
        monkeypatch.setattr(snapshot_reuse, "_witness_of", too_deep)
    else:
        monkeypatch.setattr(snapshot_reuse.SnapshotReuse, "put_if_absent", too_deep)
    for _ in range(2):
        snapshot = AnalysisSnapshot.from_function_analysis(analysis)
        assert fields_of(snapshot) == fields_of(body(analysis))
    assert bodies.count == 2
    assert pair_scope.metrics()["entries"] == 0
    assert _counts()["bypass:witness_failed:RecursionError"] == 2


def test_t_b16_a_witness_failure_the_body_shares_raises_the_body_failure(monkeypatch, pair_scope, bodies):
    analysis = _analysis()
    analysis.return_abi_facts = {"opaque": object()}
    with pytest.raises(Exception) as off:
        body(analysis)
    with pytest.raises(type(off.value)):
        AnalysisSnapshot.from_function_analysis(analysis)


# ---------------------------------------------------------------------------
# T-B17 token の封じ込め / T-B18 入れ子の直列化
# ---------------------------------------------------------------------------


def test_t_b17_a_token_that_reaches_the_body_codec_is_rejected():
    token = ElidedSemanticValue(_value(1))
    for payload in (token, {"x": token}, [token], (("k", token),)):
        with pytest.raises(TypeError):
            SnapshotFingerprintCodec.digest(payload)
        with pytest.raises(TypeError):
            SnapshotFingerprintCodec.freeze(payload)
    with pytest.raises(TypeError):
        AnalysisSnapshot.create(("id",), {"returns": [token]})


def test_t_b18_a_call_inside_another_serialization_neither_looks_up_nor_stores(monkeypatch, bodies):
    analysis = _analysis()
    consumed = {}
    for enabled in (True, False):
        monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", enabled)
        with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope() as store:
            AnalysisSnapshot.from_function_analysis(analysis)  # 外では entry がある（on）
            before = bodies.count
            with serialization_scope(site="test.outer", target_parts=("outer",)) as work:
                inner = AnalysisSnapshot.from_function_analysis(analysis)
                inner_again = AnalysisSnapshot.from_function_analysis(analysis)
            assert bodies.count == before + 2
            assert fields_of(inner) == fields_of(inner_again)
            consumed[enabled] = work.consumed
            assert store.metrics()["entries"] == (1 if enabled else 0)
    # 外側の作業量への合算は memo の on / off で同じ
    assert consumed[True] == consumed[False]


# ---------------------------------------------------------------------------
# T-B20 budget の観測
# ---------------------------------------------------------------------------


def _snapshot_observation():
    return {
        key: value for key, value in budget_observations().items()
        if key.endswith("@" + SNAPSHOT_SERIALIZATION_SITE) or "snapshot_reuse" in key
    }


def test_t_b20_every_call_observes_its_read_like_the_body_with_memo_on_and_off(monkeypatch, bodies):
    """観測値（結果の JSON の `diagnostics.expression_budget.observed`）は on / off と main の本体で同じ。

    呼び出しはどれも本体と同じ読み（同じ scope）を 1 回行うので、hit も本体と同じ量を観測する。
    再利用は自分の観測点を持たない。
    """

    observed = {}
    for mode in ("on", "off", "main"):
        monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", mode == "on")
        analysis = _analysis()
        with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
            rows = []
            for _ in range(3):
                if mode == "main":
                    body(analysis)
                else:
                    AnalysisSnapshot.from_function_analysis(analysis)
                rows.append(_snapshot_observation())
            observed[mode] = (rows, budget_observations())
    assert observed["on"] == observed["off"] == observed["main"]
    assert observed["on"][0][0]
    assert not any("snapshot_reuse" in key for key in observed["on"][1])


# ---------------------------------------------------------------------------
# C-RS2 との接続: pending / closed / unsealable、sealing の失敗・再入・外部の状態
# ---------------------------------------------------------------------------


_EXTERNAL = {"text": "a"}


@dataclasses.dataclass(frozen=True)
class _ExternalStateRef:
    """表現を作る code が field の外の状態を読む ref（写すと、その時点の値で固定される）。"""

    key: int

    def stable_key(self):
        return ("external", self.key)

    def json_items(self):
        yield "key", self.key
        yield "text", _EXTERNAL["text"]


@dataclasses.dataclass(frozen=True)
class _FailingRef:
    """表現を作る code が「表現を作れない」以外の失敗を上げる ref。"""

    key: int

    def stable_key(self):
        return ("failing", self.key)

    def json_items(self):
        raise OSError("ref storage is gone")
        yield  # pragma: no cover


_REENTRANT: List[Any] = []


@dataclasses.dataclass(frozen=True)
class _ReentrantRef:
    """表現を作る code が別の解析の snapshot を作る ref（sealing の中からの再入）。"""

    key: int

    def stable_key(self):
        return ("reentrant", self.key)

    def json_items(self):
        for analysis in _REENTRANT:
            AnalysisSnapshot.from_function_analysis(analysis)
        yield "key", self.key


def _ref_value(ref: Any) -> Expression:
    return Expression.binary_op(
        "INT_ADD", _param("a"), Expression.unknown("u", runtime_ref=ref),
    )


def test_pending_values_are_sealed_at_the_boundary_with_memo_on_and_off(monkeypatch, bodies):
    for enabled in (True, False):
        monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", enabled)
        analysis = _analysis(value=_ref_value(PcodeOpRef(address_offset=0x10, mnemonic="INT_ADD", input_sizes=(4, 4))))
        root = analysis.returns[0].value
        assert serialization_pending(root)
        with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
            snapshot = AnalysisSnapshot.from_function_analysis(analysis)
            assert serialization_closed(root) and not serialization_pending(root)
            assert _counts()["sealed"] >= 1
            assert fields_of(snapshot) == fields_of(body(analysis))


def test_sealing_runs_outside_every_walk_and_serialization(monkeypatch, pair_scope, bodies):
    """sealing（ref の code を走らせる明示の状態確定）は抽出の外で行う（閉じた値の読み口・葉の置き換えの中ではない）。"""

    from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work
    from scripts.function_tracer_pcode.core.json_encoding import active_walk_work

    seen = []
    real = snapshot_reuse.seal_serialization

    def observed(value, **kwargs):
        # 読みが描いた表現から写す（ref の code を走らせない）
        seen.append((active_walk_work() is None, active_serialization_work() is None, callable(kwargs.get("observed"))))
        return real(value, **kwargs)

    monkeypatch.setattr(snapshot_reuse, "seal_serialization", observed)
    analysis = _analysis(value=_ref_value(PcodeOpRef(address_offset=0x20, mnemonic="INT_ADD", input_sizes=(4, 4))))
    AnalysisSnapshot.from_function_analysis(analysis)
    assert seen and all(outside == (True, True, True) for outside in seen)


def test_an_analysis_without_to_dict_fails_like_the_body_even_after_a_hit(pair_scope, bodies):
    analysis = _analysis()
    AnalysisSnapshot.from_function_analysis(analysis)

    class _NoToDict:
        def __init__(self, inner):
            self._inner = inner

        def __getattr__(self, name):
            if name == "to_dict":
                raise AttributeError(name)
            return getattr(self._inner, name)

    with pytest.raises(TypeError):
        body(_NoToDict(analysis))
    with pytest.raises(TypeError):
        AnalysisSnapshot.from_function_analysis(_NoToDict(analysis))


def test_values_outside_a_scope_are_not_sealed(bodies):
    analysis = _analysis(value=_ref_value(PcodeOpRef(address_offset=0x10, mnemonic="INT_ADD", input_sizes=(4, 4))))
    with budget_policy_scope(BudgetPolicy()):
        AnalysisSnapshot.from_function_analysis(analysis)
    assert serialization_pending(analysis.returns[0].value)


def test_external_state_read_by_ref_code_is_fixed_at_sealing_with_memo_on_and_off(monkeypatch):
    results = {}
    for enabled in (True, False):
        monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", enabled)
        _EXTERNAL["text"] = "before"
        analysis = _analysis(value=_ref_value(_ExternalStateRef(1)))
        with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
            first = AnalysisSnapshot.from_function_analysis(analysis)
            _EXTERNAL["text"] = "after"
            second = AnalysisSnapshot.from_function_analysis(analysis)
            assert fields_of(second) == fields_of(body(analysis))
            results[enabled] = (fields_of(first)[:6], fields_of(second)[:6])
    assert results[True] == results[False]
    # 写した値は写しから描く（外の状態の変化は表現に現れない: C-RS2）
    assert results[True][0] == results[True][1]


def test_an_unsealable_value_is_walked_by_value(monkeypatch, bodies):
    from scripts.function_tracer_pcode.core.frozen_representation import CAPTURE_MAX_BYTES

    _EXTERNAL["text"] = "x" * (CAPTURE_MAX_BYTES + 16)  # 写しの上限を超える = UNSEALABLE
    analysis = _analysis(value=_ref_value(_ExternalStateRef(2)))
    root = analysis.returns[0].value
    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        before = AnalysisSnapshot.from_function_analysis(analysis)
        assert not serialization_closed(root) and not serialization_pending(root)
        _EXTERNAL["text"] = "y" * (CAPTURE_MAX_BYTES + 16)
        after = AnalysisSnapshot.from_function_analysis(analysis)
        assert fields_of(after) == fields_of(body(analysis))
        assert after.semantic_fingerprint != before.semantic_fingerprint
        assert bodies.count == 2


@pytest.mark.parametrize("mode", ["on", "off", "no_scope"])
def test_a_sealing_failure_propagates_like_the_live_body_and_stays_pending(monkeypatch, mode):
    monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", mode == "on")
    analysis = _analysis(value=_ref_value(_FailingRef(3)))
    root = analysis.returns[0].value
    with budget_policy_scope(BudgetPolicy()):
        with pytest.raises(OSError):
            body(analysis)  # 生の ref を描く本体も同じ失敗
        if mode == "no_scope":
            with pytest.raises(OSError):
                AnalysisSnapshot.from_function_analysis(analysis)
        else:
            with snapshot_reuse_scope() as store:
                with pytest.raises(OSError):
                    AnalysisSnapshot.from_function_analysis(analysis)
                with pytest.raises(OSError):
                    AnalysisSnapshot.from_function_analysis(analysis)
                assert store.metrics()["entries"] == 0
    assert serialization_pending(root)


def test_a_snapshot_requested_while_sealing_bypasses_reuse(pair_scope, bodies):
    other = _analysis("g", seed=4)
    _REENTRANT[:] = [other]
    try:
        analysis = _analysis(value=_ref_value(_ReentrantRef(5)))
        snapshot = AnalysisSnapshot.from_function_analysis(analysis)
    finally:
        _REENTRANT[:] = []
    assert fields_of(snapshot) == fields_of(body(analysis))
    assert _counts().get("bypass:nested_serialization", 0) >= 1
    assert _counts()["body_executions"] == bodies.count


# ---------------------------------------------------------------------------
# 計測は実際の実行回数（同時の重複・fallback・bypass を含む）
# ---------------------------------------------------------------------------


def test_the_counted_body_executions_are_the_actual_executions(monkeypatch, bodies):
    analysis = _analysis()
    with budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(analysis)
        AnalysisSnapshot.from_function_analysis(analysis)
        analysis.analysis_notes.append("symbolic_post_state_reads")
        AnalysisSnapshot.from_function_analysis(analysis)
        with serialization_scope(site="test.outer", target_parts=("outer",)):
            AnalysisSnapshot.from_function_analysis(analysis)
        monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", False)
        AnalysisSnapshot.from_function_analysis(analysis)
        counts = _counts()
    # canonical な経路の本体（読んだ値から作る）3 回 + 通常の本体へ回した入れ子 1 回
    assert counts["body_executions"] == 3 and bodies.count == 4
    assert counts["requests"] == 4 and counts["hits"] == 1 and counts["misses"] == 2
    assert counts["bypass:nested_serialization"] == 1
    # 読みは 4 回（入れ子は読みの外の本体）
    assert len(bodies.reads) == 4


def test_t_b21_body_executions_equal_the_distinct_safe_witnesses_of_a_sequential_pair(pair_scope, bodies):
    """AC1（unit）: 逐次で安定した実行では、本体の実行回数 == 保存された distinct な witness の数。

    distinct な fingerprint の数との一致は求めない（別 object の同じ内容は別の witness）。
    """

    first = _analysis("f")
    rebuilt = _analysis("f")  # 同じ fingerprint・別の object
    view = dataclasses.replace(first)
    for _ in range(3):
        for item in (first, rebuilt, view):
            AnalysisSnapshot.from_function_analysis(item)
    counts = _counts()
    assert counts.get("unstable", 0) == 0
    assert bodies.count == pair_scope.metrics()["entries"] == 2
    fingerprints = {AnalysisSnapshot.from_function_analysis(item).semantic_fingerprint for item in (first, rebuilt)}
    assert len(fingerprints) == 1
