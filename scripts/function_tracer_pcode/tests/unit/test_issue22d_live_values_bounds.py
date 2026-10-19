# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D: `core/live_values`（bounded path が live な値を読む唯一の owner）自身の仕事の上限。

live な値の storage を作業量を受け取らずに読む関数は、どれも次のどれか（J22 を owner 自身へ）:

* A: 固定の大きさ（module の定数の組・登録した directory）だけを辿る
* B: 固定の上限の型の契約（`SCAN_LIMIT`）: 長さを組み込みの slot で O(1) に読んで比べてから辿る。
  上限の意味は読むものの種類で 2 つ: **型**（namespace・MRO・closure）は「確かめられない」= 信頼しない
  （文脈に依らず cache する）、**値の storage**（dict / `__dict__` の key・key の tuple・proxy の段・写す
  容器）は安全の判定ではなく量で、意味は今の文脈の量の owner（作業量・呼ぶ側・`core/read_limits`）
* C: iterator を返し、辿る側が要素ごとに数える

この file は `live_values` 自身の契約を、量の意味を呼ぶ側が決める文脈（`signalled_storage_reads`: 量の
信号 `StorageBeyondReadBound`）と作業量の文脈で確かめる。作業量を受け取らない文脈の意味（型つきの
限界）は `test_issue22d_read_bound_contract.py`。
"""

from __future__ import annotations

import ast
import time
import types
from collections import OrderedDict
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import JsonBudget, JsonBudgetExhausted
from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as audit

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
BIG = 1_000_000
BEYOND = live_values.StorageBeyondReadBound


def _quick(call, *args, seconds=0.05):
    """`call(*args)` の結果（または上げた例外）と、それが一瞬で終わったこと。"""

    started = time.perf_counter()
    with live_values.signalled_storage_reads():
        try:
            outcome = call(*args)
        except (TypeError, BEYOND) as exc:
            outcome = exc
    assert time.perf_counter() - started < seconds, call
    return outcome


def _signal(outcome):
    """量の信号（`TypeError` でも限界でもない）。"""

    return type(outcome) is BEYOND and not isinstance(outcome, TypeError)


class _Record:
    pass


@pytest.fixture(scope="module")
def big_record():
    record = _Record()
    record.__dict__.update({f"k{index}": index for index in range(BIG)})
    return record


def test_a_million_key_instance_state_is_a_quantity_signal_not_an_unsafe_value(big_record, monkeypatch):
    """100 万 key の `__dict__`: key の型を確かめる走査をせず、量の信号（`TypeError` にしない）。"""

    scanned = []
    real_is = live_values._IS
    monkeypatch.setattr(live_values, "_IS", lambda *args: scanned.append(1) or real_is(*args))
    outcome = _quick(live_values.instance_state, big_record, "k1")
    assert _signal(outcome) and outcome.observed == BIG and outcome.limit == live_values.SCAN_LIMIT
    # 型の namespace（小さい）は確かめても、100 万 key の `__dict__` の key は 1 つも確かめない
    assert len(scanned) < 100
    assert _signal(_quick(live_values.attribute, big_record, "k1"))
    assert _signal(_quick(live_values.set_state, big_record, "k1", 0))
    # 上限の内側の record は今までどおり読める
    small = _Record()
    small.x = 1
    assert live_values.instance_state(small, "x") == 1


def test_a_bounded_meter_reads_beyond_the_fixed_bound_and_charges_only_the_excess():
    """作業量を持つ owner の中（`metered_storage_reads`）は、上限を超えた分だけを作業量へ数えて読む。"""

    record = _Record()
    record.__dict__.update({f"k{index}": index for index in range(live_values.SCAN_LIMIT + 10)})
    work = JsonBudget(1_000)
    with live_values.metered_storage_reads(work):
        assert live_values.instance_state(record, "k1") == 1
    assert work.consumed == 10
    small = _Record()
    small.x = 1
    untouched = JsonBudget(1_000)
    with live_values.metered_storage_reads(untouched):
        live_values.instance_state(small, "x")
    assert untouched.consumed == 0  # 上限の内側の入力の勘定は変わらない
    # 作業量が足りなければ、その作業量の超過（信号ではない）
    with pytest.raises(JsonBudgetExhausted):
        with live_values.metered_storage_reads(JsonBudget(5)):
            live_values.instance_state(record, "k1")


def test_an_unbounded_meter_reads_like_the_builtin_containers_it_walks():
    """上限の無い作業量の owner は組み込みの容器を上限なしで辿る: 値の storage の読みも上限なしで読む
    （容器の種類で結果を変えない）。入れ子では内側の作業量で数える（読むのは内側の owner の走査）。"""

    record = _Record()
    record.__dict__.update({f"k{index}": index for index in range(live_values.SCAN_LIMIT + 10)})
    big = OrderedDict((index, index) for index in range(live_values.SCAN_LIMIT + 10))
    unbounded = JsonBudget(None, detached=True)
    with live_values.metered_storage_reads(unbounded):
        assert live_values.instance_state(record, "k1") == 1
        assert live_values.builtin_mapping(big) is big
    outer = JsonBudget(1 << 20)
    with live_values.metered_storage_reads(outer):
        with live_values.metered_storage_reads(JsonBudget(None, detached=True)):
            assert live_values.builtin_mapping(big) is big
        # `None` は外の作業量をそのまま使う
        with live_values.metered_storage_reads(None):
            assert live_values.builtin_mapping(big) is big
    assert outer.consumed == 10


def test_only_registered_meters_are_accepted():
    class _Anything:
        def charge(self, size):  # pragma: no cover - never registered
            pass

    # 回復用の `except TypeError` に吸われない型で拒む（owner の不備）
    with pytest.raises(ValueError):
        live_values.metered_storage_reads(_Anything())


def test_a_large_class_namespace_is_not_trusted_or_read(monkeypatch):
    namespace = {f"m{index}": index for index in range(BIG)}
    big_type = type("BigNamespace", (), namespace)
    assert _quick(live_values.package_type, big_type) is False
    outcome = _quick(live_values.type_attribute, big_type, "m1")
    assert isinstance(outcome, TypeError) and not _signal(outcome)


def test_type_trust_does_not_depend_on_an_active_meter():
    """型の信頼の判定は文脈に依らない: meter の中でも外でも、上限の外の値を持つ型は信頼しない。"""

    blob = _Record()
    blob.__dict__.update({f"a{index}": index for index in range(live_values.SCAN_LIMIT + 10)})
    inside = type("InsideMeter", (), {"blob": blob})
    outside = type("OutsideMeter", (), {"blob": blob})
    with live_values.metered_storage_reads(JsonBudget(1 << 20)):
        assert live_values.package_type(inside) is live_values.package_type(inside)
        verdict_inside = live_values.package_type(inside)
    assert live_values.package_type(outside) is verdict_inside


def test_a_long_mro_is_not_walked():
    kinds = [object]
    for index in range(live_values.SCAN_LIMIT + 5):
        kinds.append(type(f"Deep{index}", (kinds[-1],), {}))
    deepest = kinds[-1]
    assert _quick(live_values.package_type, deepest) is False
    assert isinstance(_quick(live_values.type_attribute, deepest, "x"), TypeError)


def test_a_large_ordered_dict_is_a_quantity_signal_and_its_length_needs_no_key_scan():
    """反復の安全（key の hash）は値の storage の読み: 上限の外は量の信号。長さ・真偽は key を読まない。
    `builtin_container` は反復してよいかの判定（`builtin_mapping` と同じ）。"""

    big = OrderedDict((index, index) for index in range(BIG))
    assert _signal(_quick(live_values.builtin_mapping, big))
    assert _signal(_quick(live_values.builtin_container, big))
    assert _quick(live_values.size, big) == BIG
    assert _quick(live_values.as_bool, big) is True
    small = OrderedDict(a=1)
    assert live_values.builtin_mapping(small) is small


def test_deep_and_wide_tuple_keys_are_a_quantity_signal():
    wide = tuple(range(BIG))
    deep = ()
    for _ in range(BIG):
        deep = (deep,)
    for key in (wide, deep):
        assert _signal(_quick(live_values.hash_safe_key, key))
        assert _signal(_quick(live_values._plain_key, key))
        assert _signal(_quick(live_values.lookup, {}, key))
    assert live_values.hash_safe_key((1, ("a", 2.0))) is True
    # 安全でない key は量と関係なく「安全でない」（信号にしない）
    assert live_values.hash_safe_key((1, object())) is False


def test_mapping_reads_by_key_beyond_the_bound_are_a_quantity_signal():
    big = {index: index for index in range(BIG)}
    big["odd"] = 1
    assert _signal(_quick(live_values.copied_container, big))
    assert _signal(_quick(live_values.merged_mappings, {"a": 1}, {f"k{i}": i for i in range(10)} | big))
    assert _signal(_quick(live_values.copied_container, list(range(BIG))))

    class _Key(str):
        def __eq__(self, other):  # pragma: no cover - must never run
            raise AssertionError("a live key's __eq__ ran")

        __hash__ = str.__hash__

    mixed = {f"k{i}": i for i in range(live_values.SCAN_LIMIT + 1)}
    mixed[_Key("x")] = 0
    assert _signal(_quick(live_values.lookup, mixed, "k1"))
    # 上限の内側の、組み込みでない key を持つ mapping は安全でない key を比べずに探す
    few = {"k1": 1, _Key("x"): 0}
    assert live_values.lookup(few, "k1") == 1


def test_a_chain_of_mapping_proxies_is_a_quantity_signal():
    proxy = types.MappingProxyType({"a": 1})
    for _ in range(live_values.SCAN_LIMIT + 5):
        proxy = types.MappingProxyType(proxy)
    assert _signal(_quick(live_values.builtin_mapping, proxy))
    assert _signal(_quick(live_values._unwrapped, proxy))
    shallow = types.MappingProxyType(types.MappingProxyType({"a": 1}))
    assert live_values.builtin_mapping(shallow) is shallow


def test_storage_count_reads_the_base_slot_without_running_value_code():
    """`storage_count` は振る舞いを確かめる前に基底型の slot で数える（上書きした `__len__` を呼ばない）。"""

    class _Loud(dict):
        def __len__(self):  # pragma: no cover - must never run
            raise AssertionError("a live __len__ ran")

    loud = _Loud({"a": 1, "b": 2})
    assert live_values.storage_count(loud) == 2
    assert live_values.storage_count(OrderedDict(a=1)) == 1
    assert live_values.storage_count(types.MappingProxyType({"a": 1, "b": 2})) == 2
    assert live_values.storage_count(iter([1])) is None
    assert live_values.storage_count("text") is None
    chain = types.MappingProxyType({})
    for _ in range(live_values.SCAN_LIMIT + 5):
        chain = types.MappingProxyType(chain)
    assert live_values.storage_count(chain) == live_values.SCAN_LIMIT + 1


def test_nested_closures_are_checked_without_recursion():
    """実行環境の wrapper が包んだ callable の入れ子は 1 つの列で辿り、上限を超えれば信頼しない。"""

    import functools

    wrapped = len
    for _ in range(live_values.SCAN_LIMIT + 5):
        wrapped = functools.lru_cache(maxsize=None)(wrapped)
    started = time.perf_counter()
    assert live_values._trusted_callable(wrapped, generated=False) is False
    assert time.perf_counter() - started < 0.5
    assert live_values._trusted_callable(functools.lru_cache(maxsize=None)(len), generated=False) is True


def test_an_unverifiable_type_is_never_left_trusted():
    """判定の途中で上限の外の値に当たっても、その型を信頼しない（仮の「信頼」を残さない）。"""

    blob = _Record()
    blob.__dict__.update({f"a{index}": index for index in range(live_values.SCAN_LIMIT + 10)})

    def outside():  # pragma: no cover - never called
        return None

    outside.__code__ = outside.__code__.replace(co_filename="/elsewhere/outside.py")
    kind = type("Unverifiable", (), {"blob": blob, "f": outside})
    assert live_values.package_type(kind) is False
    assert live_values.package_type(kind) is False  # 2 回目も（cache に信頼が残らない）


def test_class_chains_are_checked_once_per_class():
    """class の body は class ごとに 1 度だけ確かめる: 継承の鎖でも MRO × namespace を毎回辿らない。"""

    kinds = [object]
    for index in range(100):
        body = {f"attr{member}": member for member in range(1_000)}
        kinds.append(type(f"Chain{index}", (kinds[-1],), body))
    started = time.perf_counter()
    for kind in kinds[1:]:
        live_values.package_type(kind)
    assert time.perf_counter() - started < 5.0


def test_non_str_namespaces_are_bounded_across_the_whole_mro():
    """組み込みの `str` でない key の namespace は key を辿らない（当たった class で TypeError: 量は class の数だけ）。"""

    kinds = [object]
    for index in range(40):
        namespace = {f"n{member}": member for member in range(200)}
        namespace[1] = "not a str key"
        kinds.append(type(f"Odd{index}", (kinds[-1],), namespace))
    outcome = _quick(live_values.type_attribute, kinds[-1], "missing", seconds=0.5)
    assert isinstance(outcome, TypeError) and "not a builtin str" in str(outcome)


def test_nested_type_references_stop_at_the_nesting_limit():
    """型の中の値が別の型を指す入れ子が深くても、判定は深さの上限で止まる（stack を使い尽くさない）。"""

    inner = type("Leaf", (), {})
    for index in range(live_values.NESTING_LIMIT * 4):
        inner = type(f"Holder{index}", (), {"inner": inner})
    assert live_values.package_type(inner) in (True, False)


# ---------------------------------------------------------------------------
# J22 を owner 自身へ: 入力に比例する構文を持つ関数は A / B / C のどれかに分類する
# ---------------------------------------------------------------------------

_A = "A: 固定の大きさ（module の定数の組・登録した directory）だけを辿る"
_B = (
    "B: `SCAN_LIMIT` の固定の上限（長さを O(1) で比べてから辿る。型の上限の外は信頼しない / TypeError、"
    "値の storage の上限の外は今の文脈の量の owner（作業量へ超えた分・呼ぶ側へ量の信号・`read_limits` の限界））"
)
_B_CALLER = "B(呼ぶ側): 呼ぶ側が先に数を上限と比べてから呼ぶ（呼ぶ関数はどれも B。下の test が確かめる）"
_C = "C: iterator を返し、辿る側が要素ごとに数える"
_AMORTIZED = (
    "B(償却): 型の信頼の判定 1 つにつき高々 1 つの仮の判定で、深さの組を移るのは高々 `NESTING_LIMIT` 回"
    "（仕事は判定の数に比例し、判定そのものは `SCAN_LIMIT` の中。循環の test が数を確かめる）。"
    "入れ子の上限で切った判定は残さないので、切られる形の型は問い合わせごとに辿り直す（既存の設計）"
)

_RELIANCE = (
    "R: 走っている監査済みの code が記録した頼る事実（walker の receiver と `package_instance` の絞り込み。1 つの値は "
    "activation に 1 度だけ）だけを辿る: 量は監査済みの code が数え済みの自分の仕事（絞り込んだ値の数）の中"
)

LIVE_VALUES_WORK_OWNERS = {
    "package_file": _A,
    "_package_type_uncached": _B,
    "_trusted_callables": _B,
    "_trusted_namespace_value": _A,
    "_trusted_class_body_values": _B,
    "_type_lookup": _B,
    "_exact_str_raw": _B_CALLER,
    "_builtin_hashed_type": _A,
    "_one_of": _A,
    "_in_mro": _B,
    "_dataclass_field_names": _B,
    "_mapping_storage": _B,
    "storage_extent": _B,
    "_builtin_behaviour": _A,
    "_unwrapped": _B,
    "_plain_keys": _B,
    "_hash_safe_keys": _B,
    "_hash_safe_key": _B,
    "merged_mappings": _B,
    "copied_container": _B,
    "lookup": _B,
    "_plain_key": _B,
    # 判定の途中の状態の 2 引数の `min`（入れ子の深さの比較）だけ
    "package_type": _A,
    "_trusted_class_body": _A,
    # 深さの組（`NESTING_LIMIT + 1` 個）を作るだけ
    "_Nesting.__init__": _A,
    "_settle": _AMORTIZED,
    # 2 引数の `max`（固定の上限の中の分を数えない）だけ / 登録した meter の型の組だけ
    "_StorageRead.admit": _A,
    "_registered_meter": _A,
    "register_storage_meter": _A,
    # Issue #242: 構築の中で受理した値を読む reader（反復の確かめ。辿る数を値の storage の読みの上限と比べる）
    "_exact_tree_read": _B,
    # 型の tuple（呼ぶ側が書いた固定の組）だけ
    "is_kind": _A,
    # 固定の組（`_TREE_BASES`）だけ。結果は型ごとに memo（`id(型)` の数の上限まで）
    "_kind_entry": _A,
    # 既に組み込みの木かを確かめる（辿った数を `SCAN_LIMIT` と比べ、超えれば遅い経路の読みへ）
    "_already_plain": _B,
    "_tree_children": _B_CALLER,
    "_tree_rebuild": _B_CALLER,
    "defined_attribute": _B,
    # 写した木と元の値のどちらかの `repr`（読みは `_exact_tree_read`）
    "scalar_repr": _A,
    # 組み込みの例外の型（`__str__` を定義する組み込みの class）の MRO と名前空間の field だけ
    "exception_text": _A,
    "_exception_fields": _A,
    # 例外の状態（組み込みの例外の field・instance の `__dict__`・中の例外）: 写す値は `exact_tree` が上限の中で読む
    # MRO の長さを `SCAN_LIMIT` と比べてから辿る
    "_new_exception": _B,
    "_exception_instance_dict": _A,
    # 辿る数を `SCAN_LIMIT` と比べる（超えれば `TypeError`: 文字列化できない印）
    "_nested_exceptions": _B,
    "_replace_exceptions": _B,
    # 平らな tuple の確かめ（長さを `SCAN_LIMIT` と比べてから辿る）。それ以外は `_exact_tree_read`
    "exact_tree_in": _B,
    # MRO の長さを `SCAN_LIMIT` と比べてから辿る
    "_defining_class": _B,
    # Issue #242 第 6 回: 比べる側の契約（辿る数・容器の長さを `SCAN_LIMIT` と比べる。超えれば判定しない:
    # `UndecidableComparison`）
    "inert": _B,
    "sorted_trees": _B,
    "_exact_elements": _B_CALLER,
    # Issue #242 第 7 回: 比較は組み込みの演算に任せる（写しと包み・写しの有効性の確かめ。辿る数・容器の数を
    # `SCAN_LIMIT` と比べる）
    "_covered": _B,
    "_comparison_shape": _B,
    "_resolved_dunder": _B,
    "_require_same_comparison": _A,
    "_plain_operands": _B,
    "_CopyFrame._read": _B,
    "_leaf_trust": _B,
    # 登録した比較・自己完結の組み込みの型（書いた数の組）だけ
    "_classify_dunder": _A,
    # 比べる 2 つの値だけ
    "_leaf_operands": _A,
    "_plain_tree": _B,
    "_CopyFrame.__init__": _B,
    "_checked": _B,
    # 登録した比較の実装（package の関数: 書いた数）だけ
    # Issue #242 第 8 回: 型の事実の表（引くたびに型の状態を確かめる）と名前空間の読み（key の hook を呼ばない）
    "_TypeFactTable._key": _A,
    "_TypeFactTable.get": _A,
    "_class_snapshot": _B,
    "_namespace_part": _B,
    # 記録した snapshot だけを辿る（snapshot を作るときに上限と比べた）
    "_state_check": _B,
    "_state_holds": _B,
    "_merged_watch": _B,
    "_accessors_hold": _B,
    "_builtin_enum_type_checked": _A,
    "outside_audit.__exit__": _A,
    # Issue #242 第 11 回: 走っている監査済みの code が頼る事実（activation の記録）だけを辿る
    "_recheck_reliance": _RELIANCE,
    "end_reliance": _RELIANCE,
    # `zip` が包む iterator の数を `SCAN_LIMIT` と比べてから辿る
    "builtin_iterator": _B,
    "audited_entry": _A,
    "_lru_callee": _A,
    # 判定が値から読む状態（書いた数の slot だけ）・記録した値の列（名前空間の上限の中: 呼ぶ側が比べた）
    "_watch": _B,
    "_watch_holds": _B,
    "_object_state": _A,
    "_dataclass_table_state": _B,
    # 依存の class の列は `record` が上限と比べてから持つ（`_state` はその列だけを辿る）
    "_TypeFactTable.record": _B,
    # dataclass の field の表（長さを上限と比べてから読む）と `Field` の slot（書いた 3 つの名前）
    "dataclass_field_specs": _B,
    "_field_slots": _A,
    # 比べる 2 つの葉だけ・型の MRO（長さを上限と比べてから辿る）
    "_require_explicit_ne": _A,
    "_resolved_comparison": _B,
    # 条件つきの自己完結の実装（`Enum.__hash__`）: 型の MRO（長さを上限と比べてから辿る）と書いた 3 つの名前
    "_self_contained_for": _B,
    # 名前の引きだけで決まる型の事実の表: 計算が引いた名前の記録（計算の引きの数: 型の MRO の上限の中）を確かめる
    "_remember_plain_mro": _B_CALLER,
    "_fixed_dict_entries": _B,
    "_LookupFactTable.record": _B_CALLER,
    "_witnessed": _B,
    "lookup_fact": _A,
    # 基底型の書いた数の名前だけ・型の MRO（長さを上限と比べてから辿る）
    "_same_behaviour": _A,
    "plain_attribute_lookup": _B,
    "class_defines": _A,
    # 比較の分類（使う時点の分類・hash で置く位置の値・作り直しの規則）と hash の読み（NaN の印）
    "_strongest_trust": _B,
    "_hashed_members": _B,
    "_rebuild_container": _B,
    "_rebuildable": _B,
    "_require_hashed_lookups": _B,
    "_flat_exact": _B,
    "_CopyFrame.unchanged": _B,
    # 例外の読みだけの field（型が決める field の数）だけ
    "_readonly_positions": _A,
    "_readonly_exceptions": _A,
    "_readonly_values": _A,
    # 例外の状態の木（例外の数を `SCAN_LIMIT` と比べる。値は `exact_tree` が 1 回の読みで写す）
    "_exception_graph": _B,
    "_graph_values": _B,
    "_copy_graph": _B,
    # 例外の状態（型が決める field の数・型の traverse が辿る参照の数）だけ
    "_none_referents": _A,
    # 割り当ての候補は `_ASSIGNMENT_LIMIT`（固定の数）まで: 型が決める field の数
    "_none_assignments": _A,
    "_exception_state_matches": _A,
    # 例外の状態の (元, 写し) の木を辿る（`_StorageRead` で辿る数を確かめる）
    "_identity_kept": _B,
}

#: `core/read_limits`（作業量を受け取らない読みの固定の上限の owner）の入力に比例する関数
READ_LIMITS_WORK_OWNERS = {
    "_counted": _B,
    "_prefix": _B,
    # 2 引数の `max` だけ
    "omitted_beyond_limit": _A,
}

#: owner の file → その分類（J22 を owner 自身へ）
OWNER_WORK = {
    "core/live_values.py": LIVE_VALUES_WORK_OWNERS,
    "core/read_limits.py": READ_LIMITS_WORK_OWNERS,
}

#: B の関数が上限と比べる呼び出し（長さを O(1) で読んで比べる owner の関数）
_BOUNDING_CALLS = frozenset({
    "_within_scan", "_require_scan", "_exact_str_keys", "admit", "_admit", "_admit_storage",
})


def _live_values_functions(path="core/live_values.py"):
    tree = ast.parse((PACKAGE_ROOT / path).read_text(encoding="utf-8"))
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node.name, node
        elif isinstance(node, ast.ClassDef):
            for item in node.body:
                if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    yield f"{node.name}.{item.name}", item


@pytest.mark.parametrize("path", sorted(OWNER_WORK))
def test_j22_every_proportional_function_of_the_owner_is_classified(path):
    owners = OWNER_WORK[path]
    proportional = {
        name: audit.proportional_constructs(function)
        for name, function in _live_values_functions(path)
        if audit.proportional_constructs(function)
    }
    assert set(proportional) == set(owners), set(proportional) ^ set(owners)


@pytest.mark.parametrize("path", sorted(OWNER_WORK))
def test_j22_the_bounded_functions_compare_with_the_bound_before_they_walk(path):
    functions = dict(_live_values_functions(path))
    unbounded = []
    for name, kind in OWNER_WORK[path].items():
        if kind != _B:
            continue
        calls = {
            (sub.func.id if isinstance(sub.func, ast.Name) else getattr(sub.func, "attr", None))
            for sub in ast.walk(functions[name]) if isinstance(sub, ast.Call)
        }
        # `range(SCAN_LIMIT)` / `islice(..., SCAN_LIMIT [+ 1])`: 辿る数そのものを上限で切る
        ranges = any(
            isinstance(sub, ast.Call)
            and (getattr(sub.func, "id", None) == "range" or getattr(sub.func, "attr", None) == "islice")
            and any(
                isinstance(node, ast.Name) and node.id == "SCAN_LIMIT"
                for arg in sub.args for node in ast.walk(arg)
            )
            for sub in ast.walk(functions[name])
        )
        # 辿る数そのものを `SCAN_LIMIT` と比べる（`layers > SCAN_LIMIT`）
        compares = any(
            isinstance(sub, ast.Compare)
            and any(_names_the_bound(node) for node in ast.walk(sub))
            for sub in ast.walk(functions[name])
        )
        if not (calls & _BOUNDING_CALLS or ranges or compares):
            unbounded.append(name)
    assert unbounded == []


def _names_the_bound(node):
    return (isinstance(node, ast.Name) and node.id == "SCAN_LIMIT") or (
        isinstance(node, ast.Attribute) and node.attr == "SCAN_LIMIT"
    )


def _called(node):
    return node.func.id if isinstance(node.func, ast.Name) else getattr(node.func, "attr", None)


def _position(node):
    return (node.lineno, node.col_offset)


@pytest.mark.parametrize("path", sorted(OWNER_WORK))
def test_j22_caller_bounded_functions_are_called_only_after_the_bound(path):
    """B(呼ぶ側) の関数の呼び出しは、どれも **同じ storage の数** を上限と比べる呼び出しより後にある
    （呼ぶ関数に上限の呼び出しがどこかに在るだけでは足りない: 順序と、比べる数の storage を確かめる）。"""

    functions = dict(_live_values_functions(path))
    caller_bounded = {name for name, kind in OWNER_WORK[path].items() if kind == _B_CALLER}
    offenders, checked = [], 0
    for name, function in functions.items():
        if name in caller_bounded:
            continue
        bounds = []
        for sub in ast.walk(function):
            if isinstance(sub, ast.Call) and _called(sub) in _BOUNDING_CALLS:
                bounds.append((_position(sub), {node.id for arg in sub.args for node in ast.walk(arg) if isinstance(node, ast.Name)}))
        # 数を変数へ置いてから比べる形（`count = dict.__len__(raw)` → `_admit_storage(count, ...)`）
        assigned = {}
        for sub in ast.walk(function):
            if isinstance(sub, ast.Assign) and len(sub.targets) == 1 and isinstance(sub.targets[0], ast.Name):
                assigned[sub.targets[0].id] = {node.id for node in ast.walk(sub.value) if isinstance(node, ast.Name)}
        for sub in ast.walk(function):
            if not (isinstance(sub, ast.Call) and _called(sub) in caller_bounded and sub.args):
                continue
            checked += 1
            storage = sub.args[0].id if isinstance(sub.args[0], ast.Name) else None
            ok = storage is not None and any(
                position < _position(sub)
                and (storage in names or any(storage in assigned.get(name, ()) for name in names))
                for position, names in bounds
            )
            if not ok:
                offenders.append((name, _called(sub), sub.lineno))
    assert offenders == []
    if path == "core/live_values.py":
        assert checked >= 5  # instance の状態・key の走査・型の namespace の呼び出し


def test_the_bound_has_one_owner():
    assert live_values.SCAN_LIMIT == 1 << 12
    source = (PACKAGE_ROOT / "core" / "live_values.py").read_text(encoding="utf-8")
    assert source.count("SCAN_LIMIT = ") == 1


def test_a_verified_container_never_runs_its_own_truth_method():
    """確かめた容器（反復・長さ・真偽は組み込みの slot）は、`__bool__` を上書きした subclass を含まない
    （audit は確かめた容器の真偽の判定を許すので、owner がその slot まで確かめる）。"""

    def _boom(self):  # pragma: no cover - must never run
        raise AssertionError("a live __bool__ ran")

    for base, predicate in (
        (list, live_values.builtin_sequence), (tuple, live_values.builtin_sequence),
        (set, live_values.builtin_set), (frozenset, live_values.builtin_set),
    ):
        loud = type(f"Loud{base.__name__}", (base,), {"__bool__": _boom})
        quiet = type(f"Quiet{base.__name__}", (base,), {})
        assert predicate(loud()) is False
        assert predicate(quiet()) is True
    assert live_values.builtin_mapping(type("LoudDict", (dict,), {"__bool__": _boom})()) is None
    assert live_values.builtin_mapping(type("QuietDict", (dict,), {})()) is not None


# ---------------------------------------------------------------------------
# 作業量を受け取らない関数の入口（`core/read_limits`: 上限の超過は登録済みの限界、診断は先頭だけ）
# ---------------------------------------------------------------------------


def test_a_metaclass_hash_never_runs_through_the_class_body_cache():
    """class の body の cache の key は metaclass が `__hash__` / `__eq__` を持たない class だけ。"""

    calls = []

    class _Loud(type):
        def __hash__(cls):  # pragma: no cover - must never run
            calls.append("hash")
            return type.__hash__(cls)

        def __eq__(cls, other):  # pragma: no cover - must never run
            calls.append("eq")
            return type.__eq__(cls, other)

    class _Quiet(_Loud):
        __hash__ = type.__hash__
        __eq__ = type.__eq__

    base = _Loud("LoudBase", (), {})
    kind = _Quiet("QuietKind", (base,), {})
    live_values.package_type(kind)
    live_values._trusted_class_body(base)
    assert calls == []


def _holder_chain(tag):
    chain = [type(f"{tag}Leaf", (), {})]
    for index in range(live_values.NESTING_LIMIT + 4):
        chain.append(type(f"{tag}Holder{index}", (), {"inner": chain[-1]}))
    return chain


def test_a_verdict_cut_by_the_nesting_limit_is_not_cached():
    """入れ子の上限で切った判定は残さない: 深い型を先に聞いても、浅い深さから聞けば同じ形の新しい型と
    同じ判定（上限の内側）になる。"""

    cut_first = _holder_chain("Cut")
    fresh = _holder_chain("Fresh")
    mid = len(cut_first) // 2
    assert live_values.package_type(cut_first[-1]) is False  # 上限で切られる
    expected = live_values.package_type(fresh[mid])
    assert expected is True
    assert live_values.package_type(cut_first[mid]) is expected


def test_a_verdict_that_assumed_an_untrusted_ancestor_is_not_cached():
    """循環の途中で祖先を仮に信頼して出した判定は、祖先の判定が「信頼しない」に決まったら残らない。"""

    def outside():  # pragma: no cover - never called
        return None

    outside.__code__ = outside.__code__.replace(co_filename="/elsewhere/outside.py")
    ancestor = type("Ancestor", (), {})
    child = type("Child", (), {"ancestor": ancestor})
    ancestor.child = child
    ancestor.outside = outside
    assert live_values.package_type(ancestor) is False
    # child は ancestor を指す: 信頼しない型を指す型は信頼しない（仮定で出した「信頼」を残さない）
    assert live_values.package_type(child) is False


def _connected_types(tag, count):
    kinds = [type(f"{tag}{index}", (), {}) for index in range(count)]
    for kind in kinds:
        for index, other in enumerate(kinds):
            if other is not kind:
                setattr(kind, f"peer{index}", other)
    return kinds


def _counting_evaluations(monkeypatch):
    calls = []
    real = live_values._package_type_uncached

    def _count(kind):
        calls.append(kind)
        return real(kind)

    monkeypatch.setattr(live_values, "_package_type_uncached", _count)
    return calls


def test_a_cycle_of_mutually_trusting_types_is_judged_once_per_type(monkeypatch):
    """互いを指す型の循環（強連結）でも、1 回の判定で型ごとに高々 1 度だけ判定する（循環の経路ごとに判定し直さない）。"""

    kinds = _connected_types("Peer", 12)
    calls = _counting_evaluations(monkeypatch)
    settled = []
    real_settle = live_values._settle

    def _settle(state, depth, **kwargs):
        settled.append(len(state.by_depth[depth]))
        return real_settle(state, depth, **kwargs)

    monkeypatch.setattr(live_values, "_settle", _settle)
    started = time.perf_counter()
    assert live_values.package_type(kinds[0]) is True
    assert time.perf_counter() - started < 1.0
    assert len(calls) <= len(kinds)
    # 仮の判定を確定する仕事は判定の数 × 入れ子の深さ以下（償却）
    assert sum(settled) <= len(calls) * live_values.NESTING_LIMIT
    # 根の判定が「信頼」に決まったので、循環の全部が確定した（聞き直しても判定しない）
    assert all(live_values.package_type(kind) is True for kind in kinds)
    assert len(calls) <= len(kinds)


def test_a_cycle_with_one_untrusted_member_is_untrusted_everywhere(monkeypatch):
    """循環の 1 つが信頼しない値を持てば、どの型から聞いても信頼しない（仮定の「信頼」を残さない）。判定の数も線形。"""

    def outside():  # pragma: no cover - never called
        return None

    outside.__code__ = outside.__code__.replace(co_filename="/elsewhere/outside.py")
    kinds = _connected_types("Tainted", 12)
    kinds[7].outside = outside
    calls = _counting_evaluations(monkeypatch)
    assert live_values.package_type(kinds[0]) is False
    assert all(live_values.package_type(kind) is False for kind in kinds)
    assert len(calls) <= 3 * len(kinds)


def test_no_provisional_verdict_outlives_the_outermost_query():
    """最も外の判定が終わった後に、仮の判定（型・class の body）も深さの組も残らない（確定するか捨てる）。"""

    def outside():  # pragma: no cover - never called
        return None

    outside.__code__ = outside.__code__.replace(co_filename="/elsewhere/outside.py")
    first = type("LeakA", (), {})
    second = type("LeakB", (), {})
    first.b = second
    second.b = second  # 内の型が自分を仮定して根で決まる（外の型の body へ仮定を持ち越さない）
    tainted = _connected_types("LeakTainted", 6)
    tainted[3].outside = outside
    shapes = [first, _connected_types("LeakPeer", 6)[0], tainted[0], _holder_chain("LeakCut")[-1]]
    state = live_values._NESTING
    for kind in shapes:
        live_values.package_type(kind)
        assert state.provisional_types == {} and state.provisional_bodies == {}
        assert all(group == [] for group in state.by_depth)
        assert state.active == {}
    assert live_values._TRUSTED_BODIES.get(first) is True
