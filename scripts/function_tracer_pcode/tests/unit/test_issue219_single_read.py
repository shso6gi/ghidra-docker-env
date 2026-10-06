# -*- coding: utf-8 -*-
"""snapshot の再利用の単一の読み（Issue #219 PR-219-B レビュー 4）: 同じ初期状態から始めた呼び出しの列は、
再利用の on / off と main の本体で、同じ結果・同じ副作用になる。

oracle は production の再利用を使わない: 同じ factory から作った **別の初期状態** を mode ごとに用意し、同じ手順を
流して、次を mode の間で比べる。

* 各呼び出しの結果（snapshot の全 field を型まで写した形・fingerprint・返る型）か、上げた例外の型と文面
* 手順の後の入力の状態（producer の code が読んだ回数・書いた値）

run ごとに object が違うので、object の葉は factory が付けた名前で比べる（同じ run の中の保持の identity は
`_snapshot_oracle` が別に確かめる）。main の本体は `_build_from_function_analysis` を直接呼ぶ（再利用を通らない）。

mode:

* `on`: 再利用の scope の中、memo あり
* `off`: 再利用の scope の中、memo なし（`_SNAPSHOT_REUSE_ENABLED = False`）
* `main`: 再利用の scope の外の本体（main と同じ本体）

runtime ref の表現を作る code が外の状態を読む場合は、C-RS2 の規則（写した値は写しから描く）で on / off は同じ、
main とは違い得る（`test_issue219_snapshot_reuse.py` の外部状態の test）。ここの producer はそれを含まない。
"""

from __future__ import annotations

import dataclasses
import random
from typing import Any, Callable, Dict, List, Tuple

import pytest

from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy, budget_policy_scope, serialization_scope
from scripts.function_tracer_pcode.core.errors import pair_failure_scope, reset_pair_failure_scopes
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.runtime_refs import PcodeOpRef
from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import snapshot_reuse_metrics, snapshot_reuse_scope
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.tests.unit._publication import published


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


@pytest.fixture(autouse=True, params=["hash", "collide"])
def _witness_hash_mode(request, monkeypatch):
    """`collide` は witness の hash を定数にして、比べ方（`_same`）だけで決めさせる。"""

    if request.param == "collide":
        monkeypatch.setattr(snapshot_reuse, "_witness_hash", lambda parts, placed=None: 0)
        monkeypatch.setattr(snapshot_reuse, "_hash", lambda value, retained=False, placed=None: 0)
    yield request.param


# ---------------------------------------------------------------------------
# 入力の producer（package の型: codec が protocol を呼ぶ）
# ---------------------------------------------------------------------------


class Counting:
    """`json_items` が読むたびに内部の counter を進める record（読みの副作用）。"""

    def __init__(self) -> None:
        self.reads = 0

    def json_items(self):
        self.reads += 1
        yield "reads", self.reads

    def observe(self) -> Any:
        return ("reads", self.reads)


class CountingKey:
    """`stable_key` が読むたびに counter を進める object（identity の読みの副作用）。"""

    def __init__(self) -> None:
        self.reads = 0

    def stable_key(self):
        self.reads += 1
        return ("keyed", self.reads)

    def observe(self) -> Any:
        return ("reads", self.reads)


class FailsOnRead:
    """`fail_at` 回目の読みで失敗する record（例外の経路）。"""

    def __init__(self, fail_at: int) -> None:
        self.reads = 0
        self.fail_at = fail_at

    def json_items(self):
        self.reads += 1
        if self.reads == self.fail_at:
            raise ValueError("read %d failed" % self.reads)
        yield "reads", self.reads

    def observe(self) -> Any:
        return ("reads", self.reads)


class WritesNote:
    """読むたびに解析の別の field（注記）へ書く record（読みの中の別 field への書き込み）。"""

    def __init__(self) -> None:
        self.target: Any = None
        self.reads = 0

    def json_items(self):
        self.reads += 1
        if self.target is not None:
            self.target.analysis_notes.append("diagnostic:read-%d" % self.reads)
        yield "reads", self.reads

    def observe(self) -> Any:
        return ("reads", self.reads)


@dataclasses.dataclass
class Plain:
    """副作用の無い、変わり得る dataclass（状態の変更の経路）。"""

    value: Any

    def observe(self) -> Any:
        return ("value", self.value)


PRODUCERS: Dict[str, Callable[[], Any]] = {
    "counting": Counting,
    "counting_key": CountingKey,
    "fails_on_third": lambda: FailsOnRead(3),
    "writes_note": WritesNote,
    "plain": lambda: Plain(1),
}


# ---------------------------------------------------------------------------
# 生成経路
# ---------------------------------------------------------------------------


class Derived(AnalysisSnapshot):
    """`create` が field を足す派生（生成経路が違う）。"""

    @classmethod
    def create(cls, snapshot_id, semantic_fields, *, diagnostic_refs=None, **kwargs):
        fields = dict(semantic_fields)
        fields["derived_extra"] = ("derived", len(fields))
        return super().create(snapshot_id, fields, diagnostic_refs=diagnostic_refs, **kwargs)


class Inherit(AnalysisSnapshot):
    """継承だけの派生（返る型だけが違う）。"""


CLASSES = {"canonical": AnalysisSnapshot, "derived": Derived, "inherit": Inherit}


# ---------------------------------------------------------------------------
# 状態と手順
# ---------------------------------------------------------------------------


class State:
    """1 run 分の入力（factory が毎回新しく作る）。object の葉は名前で比べる。"""

    def __init__(self, producers: List[str], *, pending: bool) -> None:
        self.objects: Dict[str, Any] = {}
        facts = {}
        for index, name in enumerate(producers):
            value = PRODUCERS[name]()
            self.objects["%s#%d" % (name, index)] = value
            facts["p%d" % index] = value
        closed = published(Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(7, size=4)))
        values = [closed]
        if pending:
            values.append(published(Expression.binary_op(
                "INT_ADD", Expression.parameter("a", 0, size=4),
                Expression.unknown("u", runtime_ref=PcodeOpRef(address_offset=0x40, mnemonic="INT_ADD", input_sizes=(4, 4))),
            )))
        self.analysis = create_mock_analysis(
            "f",
            returns=[ReturnInfo(address="0x%08x" % (0x401000 + 4 * i), conditions=[], value=v) for i, v in enumerate(values)],
        )
        self.analysis.return_abi_facts = facts
        self.analysis.analysis_scope_key = ("scope", tuple(facts.values())[:1])
        for value in facts.values():
            if isinstance(value, WritesNote):
                value.target = self.analysis
        self.labels = {id(value): label for label, value in self.objects.items()}

    def observe(self) -> Any:
        return (
            tuple((label, value.observe()) for label, value in sorted(self.objects.items())),
            tuple(self.analysis.analysis_notes),
        )


def _shape(value: Any, labels: Dict[int, str]) -> Any:
    """run をまたいで比べる形（型まで。object は名前、名前の無い object は型名と内容）。"""

    kind = type(value)
    if value is None or kind in (bool, int, str, bytes):
        return (kind.__name__, value)
    if kind is float:
        return ("float", float.__repr__(value))
    if kind in (tuple, list):
        return (kind.__name__, tuple(_shape(item, labels) for item in value))
    if kind in (frozenset, set):
        return (kind.__name__, tuple(sorted(repr(_shape(item, labels)) for item in value)))
    if isinstance(value, dict) or type(value).__name__ == "mappingproxy":
        return (kind.__name__, tuple((_shape(key, labels), _shape(item, labels)) for key, item in value.items()))
    label = labels.get(id(value))
    if label is not None:
        return ("object", label)
    if dataclasses.is_dataclass(value):
        return (kind.__name__, tuple((f.name, _shape(getattr(value, f.name), labels)) for f in dataclasses.fields(value)))
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict) and isinstance(value, Expression):
        return ("Expression", _shape(to_dict(), labels))
    return ("opaque", kind.__name__)


def _result(snapshot: AnalysisSnapshot, labels: Dict[int, str]) -> Any:
    refs = dict(snapshot.diagnostic_refs)
    refs.pop("function_ref", None)
    return (
        type(snapshot).__name__,
        _shape(snapshot.snapshot_id, labels),
        _shape(snapshot.semantic_fields, labels),
        snapshot.semantic_fingerprint,
        snapshot.comparison_fingerprint,
        _shape(refs, labels),
    )


Step = Tuple[str, Any]


def _mutate_plain(state: State) -> None:
    for value in state.objects.values():
        if isinstance(value, Plain):
            value.value = value.value + 1


def _replace_first(state: State) -> None:
    key = sorted(state.analysis.return_abi_facts)[0]
    state.analysis.return_abi_facts[key] = Plain(99)
    state.labels[id(state.analysis.return_abi_facts[key])] = "replacement"


def _append_note(state: State) -> None:
    state.analysis.analysis_notes.append("indirect_control_flow_unresolved")


MUTATIONS = {"mutate_plain": _mutate_plain, "replace_first": _replace_first, "append_note": _append_note}


def _call(mode: str, cls: Any, analysis: Any, *, nested: bool) -> Any:
    if mode == "main":
        return cls._build_from_function_analysis(analysis)
    if nested:
        with serialization_scope(site="test.outer", target_parts=("outer",)):
            return cls.from_function_analysis(analysis)
    return cls.from_function_analysis(analysis)


def _run(mode: str, factory: Callable[[], State], steps: List[Step], monkeypatch) -> Any:
    reset_pair_failure_scopes()
    monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", mode == "on")
    state = factory()
    out: List[Any] = []
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        for kind, arg in steps:
            if kind in ("call", "nested"):
                try:
                    snapshot = _call(mode, CLASSES[arg], state.analysis, nested=kind == "nested")
                    out.append(("ok", _result(snapshot, state.labels)))
                except (TypeError, ValueError) as failure:
                    out.append(("raised", type(failure).__name__, str(failure)))
                except Exception as failure:  # noqa: BLE001 - test oracle: record any exception type
                    out.append(("raised", type(failure).__name__, str(failure)[:200]))
            else:
                MUTATIONS[arg](state)
        metrics = snapshot_reuse_metrics()
    out.append(("state", state.observe()))
    return out, metrics


def _compare(factory: Callable[[], State], steps: List[Step], monkeypatch) -> Dict[str, Any]:
    runs = {mode: _run(mode, factory, steps, monkeypatch) for mode in ("on", "off", "main")}
    assert runs["on"][0] == runs["off"][0], steps
    assert runs["on"][0] == runs["main"][0], steps
    return {mode: run[1] for mode, run in runs.items()}


# ---------------------------------------------------------------------------
# 回帰: レビュー 4 の反例
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("producer", sorted(PRODUCERS))
@pytest.mark.parametrize("where", ["return_abi_facts", "analysis_scope_key"])
def test_a_reading_side_effect_runs_the_same_number_of_times_with_memo_on_off_and_main(producer, where, monkeypatch):
    """読むたびに状態を変える producer: on / off / main で同じ fingerprint の列・同じ回数の読み（レビュー 4 の A）。"""

    def factory() -> State:
        state = State([producer], pending=False)
        if where == "analysis_scope_key":
            value = state.analysis.return_abi_facts.pop("p0")
            state.analysis.analysis_scope_key = ("scope", value)
        return state

    _compare(factory, [("call", "canonical")] * 4, monkeypatch)


@pytest.mark.parametrize("order", [("canonical", "derived"), ("derived", "canonical"), ("canonical", "inherit"), ("inherit", "canonical")])
def test_each_generation_path_returns_its_own_type_and_fields_in_either_order(order, monkeypatch):
    """同じ pair・同じ解析で生成経路を混ぜても、それぞれの経路の本体と同じ型・field（レビュー 4 の B）。"""

    def factory() -> State:
        return State(["plain"], pending=False)

    steps = [("call", order[0]), ("call", order[1]), ("call", order[0]), ("call", order[1])]
    metrics = _compare(factory, steps, monkeypatch)
    counts = metrics["on"]["counts"]
    assert counts["bypass:generation_path"] == 2


def test_a_replaced_body_or_create_is_not_the_canonical_path(monkeypatch):
    """置き換えた `create` / 本体は canonical でない（読む前に通常の本体へ）。"""

    seen = []
    original = AnalysisSnapshot.__dict__["create"].__func__

    def recorded_create(cls, *args, **kwargs):
        seen.append(cls)
        return original(cls, *args, **kwargs)

    monkeypatch.setattr(AnalysisSnapshot, "create", classmethod(recorded_create))
    state = State(["plain"], pending=False)
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(state.analysis)
        AnalysisSnapshot.from_function_analysis(state.analysis)
        counts = snapshot_reuse_metrics()["counts"]
    assert seen == [AnalysisSnapshot, AnalysisSnapshot]
    assert counts == {"bypass:generation_path": 2}


# ---------------------------------------------------------------------------
# 組み合わせ: hit / miss / bypass、生成経路、状態の変更、副作用、例外、sealing
# ---------------------------------------------------------------------------


def _random_steps(rng: random.Random) -> List[Step]:
    steps: List[Step] = []
    for _ in range(rng.randrange(3, 9)):
        pick = rng.random()
        if pick < 0.55:
            steps.append(("call", rng.choice(("canonical", "canonical", "derived", "inherit"))))
        elif pick < 0.65:
            steps.append(("nested", "canonical"))
        else:
            steps.append(("mutate", rng.choice(sorted(MUTATIONS))))
    return steps


@pytest.mark.parametrize("seed", range(120))
def test_random_sequences_have_the_same_results_and_side_effects_with_memo_on_off_and_main(seed, monkeypatch):
    rng = random.Random(seed)
    producers = [rng.choice(sorted(PRODUCERS)) for _ in range(rng.randrange(1, 4))]
    pending = rng.random() < 0.5
    steps = _random_steps(rng)

    def factory() -> State:
        return State(producers, pending=pending)

    _compare(factory, steps, monkeypatch)


def test_hits_happen_and_the_body_runs_once_per_distinct_witness(monkeypatch):
    """同じ読みは hit する（全部を作り直す修正ではない）。pending な値は 1 回目の読みの後で写す。"""

    def factory() -> State:
        return State(["plain"], pending=True)

    metrics = _compare(factory, [("call", "canonical")] * 5, monkeypatch)
    counts = metrics["on"]["counts"]
    # 1 回目: pending を描いて読み、写す。2 回目: closed になった値の token で読む（別の witness）。以後は hit
    assert counts["body_executions"] == 2 and counts["hits"] == 3 and counts["sealed"] == 1
    assert metrics["off"]["counts"]["sealed"] == 1 and "hits" not in metrics["off"]["counts"]


# ---------------------------------------------------------------------------
# 監査で見つけた隣接の経路（view の code が読む葉・codec の入口・thread・hit の object）
# ---------------------------------------------------------------------------


from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis  # noqa: E402


class _DedupingAnalysis(FunctionReturnAnalysis):
    """view が自分で walk の結果を読み、`==` で重複を除く解析（置き換えた葉を view の code が受け取り得る）。"""

    def semantic_snapshot_dict(self):
        seen = []
        for ret in self.returns:
            tree = ret.to_dict()["value"]
            if tree not in seen:
                seen.append(tree)
        return {"distinct_values": seen, "count": len(seen)}


def test_a_view_that_reads_its_own_walk_never_receives_a_token(monkeypatch):
    def factory() -> State:
        state = State(["plain"], pending=False)
        twin = published(Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(7, size=4)))
        analysis = _DedupingAnalysis.__new__(_DedupingAnalysis)
        analysis.__dict__.update(state.analysis.__dict__)
        analysis.returns = [state.analysis.returns[0], ReturnInfo(address="0x00401100", conditions=[], value=twin)]
        state.analysis = analysis
        return state

    _compare(factory, [("call", "canonical")] * 3, monkeypatch)


@pytest.mark.parametrize("name", ["digest", "freeze", "_freeze_unmetered", "_freeze_placing", "digest_frozen"])
def test_a_replaced_codec_entry_is_not_the_canonical_path(monkeypatch, name):
    from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec

    original = SnapshotFingerprintCodec.__dict__[name]
    monkeypatch.setattr(SnapshotFingerprintCodec, name, original)
    # 同じ関数でも、置き直した入口は定義のままと言えない（読む前に通常の本体へ）
    monkeypatch.setattr(SnapshotFingerprintCodec, name, type(original)(original.__func__))
    state = State(["plain"], pending=False)
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        AnalysisSnapshot.from_function_analysis(state.analysis)
        counts = snapshot_reuse_metrics()["counts"]
    assert counts == {"bypass:generation_path": 1}


def test_a_scope_closing_in_one_thread_keeps_the_scope_another_thread_opened_later():
    import threading

    entered, release, done = threading.Event(), threading.Event(), threading.Event()
    seen = {}

    def inner():
        with snapshot_reuse_scope() as store:
            entered.set()
            release.wait(5)
            seen["active"] = snapshot_reuse._active_store() is store
        done.set()

    with snapshot_reuse_scope() as outer:
        worker = threading.Thread(target=inner)
        worker.start()
        assert entered.wait(5)
    release.set()
    assert done.wait(5)
    worker.join(5)
    assert seen["active"] is True
    assert outer is not None and snapshot_reuse._active_store() is None


def test_a_hit_returns_a_new_snapshot_object_with_the_same_retained_values():
    from scripts.function_tracer_pcode.tests.unit import _snapshot_oracle as oracle

    state = State(["plain"], pending=False)
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        first = AnalysisSnapshot.from_function_analysis(state.analysis)
        second = AnalysisSnapshot.from_function_analysis(state.analysis)
        assert snapshot_reuse_metrics()["counts"]["hits"] == 1
        built = AnalysisSnapshot._build_from_function_analysis(state.analysis)
    assert second is not first
    assert oracle.snapshot_problems(second, built) == []


def test_the_witness_digest_of_the_codec_copy_follows_the_fingerprint_and_token_identity():
    """codec の写しの witness の digest: token が無ければ fingerprint の digest と同じ。token は値の identity で書く。
    token として書くのは、読みが置いた token（`PlacedTokens`）だけ: 置いていない同じ型の object は JSON にできない値。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot import (
        NO_PLACED_TOKENS,
        PlacedTokens,
        SnapshotFingerprintCodec,
        witness_fingerprint_digest,
    )
    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import ElidedSemanticValue

    plain = SnapshotFingerprintCodec.freeze({"a": [1, 2.5, "x", None, True]})
    assert witness_fingerprint_digest(plain, NO_PLACED_TOKENS) == SnapshotFingerprintCodec.digest_frozen(plain)
    value = published(Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(7, size=4)))
    twin = published(Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(7, size=4)))
    tokens = [ElidedSemanticValue(value), ElidedSemanticValue(value), ElidedSemanticValue(twin)]
    placed = PlacedTokens(tokens)
    first, again, other = ((("k", token),) for token in tokens)
    assert witness_fingerprint_digest(first, placed) == witness_fingerprint_digest(again, placed)
    assert witness_fingerprint_digest(first, placed) != witness_fingerprint_digest(other, placed)
    with pytest.raises(TypeError):
        witness_fingerprint_digest((("k", object()),), placed)
    # 置いていない token（同じ型・同じ値を包む）は token として書かない
    with pytest.raises(TypeError):
        witness_fingerprint_digest((("k", ElidedSemanticValue(value)),), placed)
    with pytest.raises(TypeError):
        witness_fingerprint_digest(first, NO_PLACED_TOKENS)


# ---------------------------------------------------------------------------
# 方針: token をほとんど置けない pair では再利用しない（費用の判断。結果は同じ）
# ---------------------------------------------------------------------------


class _BoxedInt(int):
    """組み込みの `int` の subclass（closed の規則が受けない scalar。実 run の JPype の整数の代わり）。"""


def _open_state() -> State:
    """返す値の大半が closed にならない解析（入口を通らずに subclass の scalar を置く）。"""

    state = State(["plain"], pending=False)
    values = []
    for index in range(6):
        value = Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(index, size=4))
        value.operands[1].__dict__["size"] = _BoxedInt(4)
        values.append(published(value))
    state.analysis.returns = state.analysis.returns + [
        ReturnInfo(address="0x%08x" % (0x402000 + 4 * i), conditions=[], value=v) for i, v in enumerate(values)
    ]
    return state


def test_a_pair_that_elides_little_stops_eliding_and_still_matches_main(monkeypatch):
    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_READS

    metrics = _compare(_open_state, [("call", "canonical")] * (_POLICY_READS + 4), monkeypatch)
    counts = metrics["on"]["counts"]
    assert counts["policy:elision_off"] == 1
    assert counts["bypass:elision_policy"] == 4
    assert counts["requests"] == _POLICY_READS + 4


def test_a_pair_that_elides_most_keeps_reusing(monkeypatch):
    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_READS

    def factory() -> State:
        return _sized_state(closed_depth=80, closed_count=1, open_depth=1, open_count=0)

    metrics = _compare(factory, [("call", "canonical")] * (_POLICY_READS + 4), monkeypatch)
    counts = metrics["on"]["counts"]
    assert "policy:elision_off" not in counts and "bypass:elision_policy" not in counts
    assert counts["hits"] == _POLICY_READS + 3


def _chain(depth: int, *, boxed: bool) -> Expression:
    """`depth` 段の加算の鎖（`boxed` なら葉の 1 つに subclass の scalar を置き、closed にしない）。"""

    value = Expression.parameter("a", 0, size=4)
    for index in range(depth):
        constant = Expression.constant(index, size=4)
        if boxed and index == 0:
            constant.__dict__["size"] = _BoxedInt(4)
        value = Expression.binary_op("INT_ADD", value, constant)
    return published(value)


def _sized_state(*, closed_depth: int, closed_count: int, open_depth: int, open_count: int) -> State:
    state = State(["plain"], pending=False)
    values = [_chain(closed_depth, boxed=False) for _ in range(closed_count)]
    values += [_chain(open_depth, boxed=True) for _ in range(open_count)]
    state.analysis.returns = state.analysis.returns + [
        ReturnInfo(address="0x%08x" % (0x403000 + 4 * i), conditions=[], value=v) for i, v in enumerate(values)
    ]
    return state


def test_the_policy_weighs_leaves_by_size_many_small_closed_and_one_large_open_stops(monkeypatch):
    """closed な葉が数で多くても、直列化の大きさの大半が open な pair では elision を止める（比べる費用が上回る）。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_READS

    factory = lambda: _sized_state(closed_depth=1, closed_count=8, open_depth=80, open_count=1)
    metrics = _compare(factory, [("call", "canonical")] * (_POLICY_READS + 2), monkeypatch)
    counts = metrics["on"]["counts"]
    assert counts["policy:elision_off"] == 1 and counts["bypass:elision_policy"] == 2


def test_the_policy_weighs_leaves_by_size_one_large_closed_and_many_small_open_keeps(monkeypatch):
    """open な葉が数で多くても、直列化の大きさの多くが closed な葉の pair では再利用を続ける。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_READS

    factory = lambda: _sized_state(closed_depth=80, closed_count=1, open_depth=1, open_count=8)
    metrics = _compare(factory, [("call", "canonical")] * (_POLICY_READS + 2), monkeypatch)
    counts = metrics["on"]["counts"]
    assert "policy:elision_off" not in counts and counts["hits"] == _POLICY_READS + 1


def test_the_policy_weighs_the_whole_read_all_leaves_closed_but_a_large_record_stops(monkeypatch):
    """式の葉は全部 closed でも、読みが直列化する大きさの大半が葉でない record の pair では elision を止める
    （実 run: 葉が直列化の 0.1 % しかない pair。葉の中の割合では量らない）。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_READS

    def factory() -> State:
        state = _sized_state(closed_depth=4, closed_count=2, open_depth=1, open_count=0)
        state.objects["plain#0"].value = list(range(4000))
        return state

    metrics = _compare(factory, [("call", "canonical")] * (_POLICY_READS + 2), monkeypatch)
    counts = metrics["on"]["counts"]
    # 割合はほぼ 0（下限の 1/4 にも届かない）: 早い判断の読みで止める
    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_EARLY_READS

    assert counts["policy:elision_off"] == 1
    assert counts["bypass:elision_policy"] == _POLICY_READS + 2 - _POLICY_EARLY_READS


def test_the_read_keeps_the_codec_copy_only_when_it_holds_tokens():
    """`create` と同じく、codec の写しは digest にしてから `retained_form` の写しを作る: token の無い読みは写しを
    持ち越さず（大きな写しが次の写しの間に生き残ると、GC の世代へ昇格して pair 全体が遅くなる）、digest は
    `create` の fingerprint そのもの。token のある読みだけが、miss の組み立てのために写しを持つ。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot import assemble_snapshot, read_snapshot_inputs

    state = _sized_state(closed_depth=6, closed_count=2, open_depth=3, open_count=1)
    with budget_policy_scope(BudgetPolicy()):
        plain = read_snapshot_inputs(state.analysis, snapshot_reuse._ReadHook(elide=False))
        body = AnalysisSnapshot._build_from_function_analysis(state.analysis)
        hook = snapshot_reuse._ReadHook(elide=True)
        tokens = read_snapshot_inputs(state.analysis, hook)
    assert plain.frozen_payload is None
    assert plain.frozen_digest == body.semantic_fingerprint
    assert hook.elided > 0 and tokens.frozen_payload is not None
    assert tokens.frozen_digest != body.semantic_fingerprint
    assert assemble_snapshot(tokens).semantic_fingerprint == body.semantic_fingerprint
    assert assemble_snapshot(plain).semantic_fingerprint == body.semantic_fingerprint
    assert not plain.placed and tokens.placed


# ---------------------------------------------------------------------------
# 方針の早い判断（レビュー 7: 実 run の pair が最初の 16 回の token を置く読みで比べる費用だけを払っていた）
# ---------------------------------------------------------------------------


def _policy_flip_read(shares) -> Any:
    """読みごとの (直列化した byte, token に置いた byte) を方針へ渡し、止めた読みの番号（1 始まり。止めなければ None）。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _ElisionPolicy

    policy = _ElisionPolicy()
    for index, (serialized, elided) in enumerate(shares, 1):
        if policy.observe(serialized, elided):
            return index
    return None


def test_the_policy_does_not_stop_on_the_first_reads_before_sealing_closes_values():
    """得をする pair でも最初の読みでは割合がほぼ 0（読みの後で写した値が以後 closed になる。recorded corpus で
    1〜2 回目は 0.000〜0.012）: その形の pair を止めない（早い判断が早すぎれば落ちる）。"""

    reads = [(1000, 0), (1000, 0), (1000, 0)] + [(1000, 600)] * 20
    assert _policy_flip_read(reads) is None


def test_the_policy_stops_at_the_early_read_when_the_share_is_far_below_the_bound():
    """（定数の根拠: recorded corpus の variant が早い判断で止まらないことは、全 replay が
    `replay_validation._assert_snapshot_reuse` で確かめる）"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import (
        _POLICY_EARLY_FACTOR, _POLICY_EARLY_READS, _POLICY_MIN_SHARE,
    )

    numerator, denominator = _POLICY_MIN_SHARE
    serialized = denominator * _POLICY_EARLY_FACTOR * 100
    at_bound = numerator * 100  # ちょうど 下限 / 倍率
    assert _policy_flip_read([(serialized, at_bound - 1)] * 30) == _POLICY_EARLY_READS
    # 境界: ちょうど下限 / 倍率なら早い判断では止めない（16 回目の判断で止める）
    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_READS

    assert _policy_flip_read([(serialized, at_bound)] * 30) == _POLICY_READS


def test_the_policy_keeps_the_full_window_for_a_share_between_the_early_and_the_final_bound():
    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import _POLICY_READS

    # 下限の 1/2（早い判断の下限より上、最終の下限より下）: 16 回目で止める
    assert _policy_flip_read([(1000, 125)] * 30) == _POLICY_READS
    # 下限以上: 止めない
    assert _policy_flip_read([(1000, 250)] * 30) is None
