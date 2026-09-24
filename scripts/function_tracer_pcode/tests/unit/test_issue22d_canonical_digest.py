# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D: 有界な fingerprint（`core/canonical_digest.canonical_fingerprint`）と、
証拠を有界にする唯一の入口（`core/json_encoding.bounded_evidence`）の契約。

* fingerprint は `authority_digest(value)` と **同じ値**（辿り終えたとき）。canonical な形が等しい
  値の fingerprint は等しい。逆（fingerprint が等しい ⇒ 値が等しい）は契約にしない（SHA-256 の
  衝突耐性に頼る照合の手がかり）。
* 有界: 作業量（`work`）の上限で止まる。幅・深さ・巨大な文字列・正規化し続ける object・共有 DAG
  でも、処理時間・peak memory・作業量が上限に比例して止まる。
* 閉路は `CanonicalValueCycle`（型つきの失敗）。
"""

from __future__ import annotations

import dataclasses
import enum
import random
import time
import tracemalloc
from unittest import mock

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest, canonical_value
from scripts.function_tracer_pcode.core.canonical_digest import (
    CanonicalValueCycle,
    canonical_fingerprint,
)
from scripts.function_tracer_pcode.core.json_encoding import (
    UNFINGERPRINTED_UNSUPPORTED,
    BoundedEvidence,
    JsonBudget,
    JsonBudgetExhausted,
    UNFINGERPRINTED_CYCLE,
    UNFINGERPRINTED_WORK_EXHAUSTED,
    bounded_evidence,
)


class _Color(enum.Enum):
    RED = 1
    PAIR = (1, [2, 3])
    TABLE = {"x": 1, "a": [1, 2]}
    NUMBERED = {3: 1, 10: 2, True: 0}


class _Named(str, enum.Enum):
    X = "x"


@dataclasses.dataclass
class _Point:
    a: int
    b: tuple


class _JInt(int):
    """PyGhidra の Java primitive（int の subclass）。"""


class _JStr(str):
    pass


class _Authority:
    def to_authority_dict(self):
        return {"k": (1, 2), "z": None}


_EDGE_VALUES = [
    None, True, 1, 1.5, float("nan"), "a\"b\\\n é\x01", _JInt(7), _JStr("s"),
    (1, 2, [3, {"b": 1, "a": 2}]), {"z": 1, "a": {"q": frozenset({1, 2, 3})}},
    {1: "a", 2: "b", 10: "c"}, {_Color.RED: 1}, {_Named.X: 1}, _Color.RED, _Color.PAIR, _Color.TABLE,
    _Point(1, (2, 3)), _Authority(), frozenset({(1, 2), (3,), "x"}), {frozenset({1}), frozenset({2, 3})},
    [_Color.NUMBERED], {None: 1, True: 2}, 2 ** 200, ["x" * 200_000], {1.5: 2, 0.1: 3}, "\ud800",
]


def _outcome(fn, value):
    try:
        return fn(value)
    except Exception as exc:  # noqa: BLE001 - 失敗の種類も一致させる
        return ("error", type(exc).__name__)


def _random_value(rng, depth=0):
    roll = rng.random()
    if depth > 3 or roll < 0.3:
        return rng.choice([None, True, False, rng.randint(-10 ** 6, 10 ** 6), rng.random(), "s", _Color.RED, _JInt(3)])
    if roll < 0.5:
        return tuple(_random_value(rng, depth + 1) for _ in range(rng.randint(0, 4)))
    if roll < 0.65:
        return [_random_value(rng, depth + 1) for _ in range(rng.randint(0, 4))]
    if roll < 0.85:
        return {rng.choice(["a", "b", 1, 2, _Color.RED]): _random_value(rng, depth + 1) for _ in range(rng.randint(0, 4))}
    return frozenset(rng.choice([1, 2, 3, "x", (1, 2), frozenset({1})]) for _ in range(rng.randint(0, 4)))


def test_the_fingerprint_equals_authority_digest_including_sets_enums_and_subclasses():
    rng = random.Random(22)
    values = _EDGE_VALUES + [_random_value(rng) for _ in range(3_000)]
    for value in values:
        expected = _outcome(authority_digest, value)
        actual = _outcome(lambda item: canonical_fingerprint(item, work=JsonBudget(None)), value)
        assert actual == expected, value


def test_equal_canonical_forms_have_equal_fingerprints_and_the_converse_is_not_claimed():
    # 保証するのは 1 方向だけ: canonical な形が等しい（set と、その canonical な tuple）なら等しい
    raw = {"key": frozenset({(1, 2), (3,), "x"})}
    assert canonical_fingerprint(raw, work=JsonBudget(None)) == canonical_fingerprint(
        canonical_value(raw), work=JsonBudget(None),
    )
    # canonical な形が違えば（衝突が無い限り）違う。値の等しさを digest から結論する API は無い
    assert canonical_fingerprint((1, 2), work=JsonBudget(None)) != canonical_fingerprint(
        (2, 1), work=JsonBudget(None),
    )
    assert not hasattr(BoundedEvidence, "match_digest")


def _bounded_run(value, limit):
    tracemalloc.start()
    started = time.perf_counter()
    work = JsonBudget(limit)
    try:
        with pytest.raises(JsonBudgetExhausted):
            canonical_fingerprint(value, work=work)
    finally:
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
    return time.perf_counter() - started, peak, work.consumed


def test_a_wide_mapping_is_charged_before_it_is_sorted():
    wide = {f"k{index}": index for index in range(1_000_000)}
    elapsed, peak, consumed = _bounded_run(wide, 4_096)
    # 幅を数えた時点で止まる: 100 万の組を並べない・写さない
    assert consumed <= 4_096 + 1_000_001
    assert peak < 8 * 1024 * 1024
    assert elapsed < 1.0


def test_a_deep_chain_and_a_huge_string_stop_at_the_work_limit():
    deep = ()
    for _ in range(200_000):
        deep = (deep,)
    elapsed, peak, _ = _bounded_run(deep, 10_000)
    assert elapsed < 1.0 and peak < 8 * 1024 * 1024
    huge = "x" * (64 * 1024 * 1024)
    elapsed, peak, consumed = _bounded_run((huge,), 1_000_000)
    # 文字列は chunk ごとに数えてから hash する: 64 MB を escape・encode しない
    assert consumed < 1_000_000 + (1 << 16) + 16
    assert peak < 8 * 1024 * 1024
    assert elapsed < 1.0


def test_an_object_that_normalizes_forever_stops_at_the_work_limit():
    # `Mock` はどの属性にも応えるので `to_authority_dict()` が無限に続く
    elapsed, peak, consumed = _bounded_run(mock.Mock(), 50)
    assert consumed <= 51
    assert elapsed < 1.0 and peak < 8 * 1024 * 1024


def test_a_deeply_shared_dag_exhausts_the_work_instead_of_expanding():
    node = ("leaf",)
    for _ in range(60):
        node = (node, node)  # 木に展開すると 2^60 個の葉
    elapsed, peak, consumed = _bounded_run(node, 100_000)
    assert consumed <= 100_000 + 64
    assert elapsed < 1.0 and peak < 8 * 1024 * 1024


def _self_list():
    cell = []
    cell.append(cell)
    return cell


def _self_dict():
    cell = {}
    cell["self"] = cell
    return cell


def _nested_cycle():
    cell = []
    cell.append({"inner": [cell]})
    return cell


@pytest.mark.parametrize("make", [_self_list, _self_dict, _nested_cycle])
def test_a_self_referential_value_is_a_typed_cycle_failure(make):
    started = time.perf_counter()
    with pytest.raises(CanonicalValueCycle):
        canonical_fingerprint(make(), work=JsonBudget(10_000_000))
    assert time.perf_counter() - started < 1.0


def test_bounded_evidence_uses_one_owner_for_every_outcome():
    work = JsonBudget(10_000_000)
    small = ("k", 1)
    assert bounded_evidence(small, work=work) is small
    large = ("key",) + tuple(range(5_000))
    summary = bounded_evidence(large, work=work)
    assert type(summary) is BoundedEvidence
    assert summary.fingerprint_kind == "canonical_sha256"
    assert summary.fingerprint == authority_digest(large)
    # canonical な値にならない証拠（live な object）は型つき token の fingerprint
    opaque = bounded_evidence([object()] * 1_000, work=work)
    assert opaque.fingerprint_kind == "token_sha256"
    # 閉路は fingerprint の無い要約（理由つき）
    cycle = _self_list()
    cycle.extend(range(5_000))
    assert bounded_evidence(cycle, work=work).unfingerprinted == UNFINGERPRINTED_CYCLE
    # 作業量を使い切った後は値を辿らない（作業量は増えない）
    spent = JsonBudget(10)
    assert bounded_evidence(large, work=spent).unfingerprinted == UNFINGERPRINTED_WORK_EXHAUSTED
    used = spent.consumed
    assert bounded_evidence(large, work=spent).unfingerprinted == UNFINGERPRINTED_WORK_EXHAUSTED
    assert spent.consumed == used
    # 呼ぶ側の identity があれば値を辿らない
    named = bounded_evidence(large, work=JsonBudget(10), identity="cause:abc")
    assert named.fingerprint == "cause:abc" and named.fingerprint_kind == "authority_identity"


def test_bounded_evidence_equality_compares_summaries_not_the_original_values():
    left = BoundedEvidence(fingerprint="f" * 64, fingerprint_kind="canonical_sha256", kind="tuple[3]")
    right = BoundedEvidence(fingerprint="f" * 64, fingerprint_kind="canonical_sha256", kind="list[3]")
    # 同じ fingerprint でも要約が違えば違う（元の値の等しさを `==` で結論しない）
    assert left != right
    with pytest.raises(ValueError):
        BoundedEvidence(fingerprint=None, fingerprint_kind=None, kind="x")


class _Fresh:
    """`to_authority_dict()` が毎回新しい一時的な容器を返す object（id が再利用され得る）。"""

    def __init__(self, depth):
        self.depth = depth

    def to_authority_dict(self):
        return {"child": [_Fresh(self.depth - 1)] if self.depth else [], "pad": [0] * 3}


def test_temporaries_freed_mid_walk_are_not_mistaken_for_a_cycle():
    value = [_Fresh(3) for _ in range(2_000)]
    assert canonical_fingerprint(value, work=JsonBudget(None)) == authority_digest(value)


class _Holder:
    def __init__(self):
        self.inner = None

    def to_authority_dict(self):
        return {"inner": self.inner}


def test_a_cycle_through_a_set_member_is_a_typed_cycle():
    holder = _Holder()
    outer = frozenset({("x", holder)})
    holder.inner = outer
    with pytest.raises(CanonicalValueCycle):
        canonical_fingerprint(outer, work=JsonBudget(10_000_000))


def test_values_without_a_bounded_canonical_form_fall_back_to_a_token_fingerprint():
    # set の中の、mapping を値に持つ enum: 並びの digest が流す byte と別の形なので約束しない
    in_set = frozenset({_Color.TABLE, _Color.RED})
    with pytest.raises(TypeError):
        canonical_fingerprint(in_set, work=JsonBudget(None))
    summary = bounded_evidence((in_set,) + tuple(range(5_000)), work=JsonBudget(10_000_000))
    assert summary.fingerprint_kind == "token_sha256"
    # 深すぎる set の入れ子は RecursionError（証拠は fingerprint の無い要約か token）
    deep = frozenset()
    for _ in range(5_000):
        deep = frozenset({deep})
    summary = bounded_evidence((deep,) + tuple(range(5_000)), work=JsonBudget(10_000_000))
    assert summary.fingerprint_kind in {"token_sha256", None}
    if summary.fingerprint_kind is None:
        assert summary.unfingerprinted == UNFINGERPRINTED_UNSUPPORTED


def test_unfingerprinted_summaries_are_equal_only_to_themselves():
    spent = JsonBudget(0)
    first = bounded_evidence(("a",) + tuple(range(5_000)), work=spent)
    second = bounded_evidence(("b",) + tuple(range(5_000)), work=spent)
    assert first.fingerprint is None and second.fingerprint is None
    assert first.kind == second.kind and first.unfingerprinted == second.unfingerprinted
    # 同じ種類・理由でも別の値の要約: 重ねない
    assert first != second and len({first, second}) == 2
    assert first == first


def test_the_encoded_size_lower_bound_is_what_was_measured():
    from scripts.function_tracer_pcode.core.json_encoding import EVIDENCE_INLINE_BYTES

    work = JsonBudget(10_000_000)
    large = ("key",) + tuple(range(5_000))
    assert bounded_evidence(large, work=work).encoded_bytes_over == EVIDENCE_INLINE_BYTES
    assert bounded_evidence(large, work=work, inline_bytes=100).encoded_bytes_over == 100
    # plain でない値（live な object）は測っていない: 下限は 0
    assert bounded_evidence([object()] * 1_000, work=work).encoded_bytes_over == 0
