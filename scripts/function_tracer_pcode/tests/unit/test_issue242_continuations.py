# -*- coding: utf-8 -*-
"""Issue #242（第 11 回）: 外の code をまたいで続く処理と、組（pair）の中の構造の読み。

契約（`core/live_values` の前提の表の「監査済みの code が頼る型」と「組の読み」の行）:

- 監査済みの code（walker の record の generator・reducer・converter・宣言した generator・J19 の entry root）が値の
  型について頼った事実（record の型の信頼・`package_instance` の絞り込み）は、外の code が走れば失効する。外の code
  から戻るときに、走っている監査済みの code が頼る事実を確かめ直し、止まっている generator は再開の前に確かめ直す。
  確かめが落ちれば、頼った型の code を呼ぶ **前に** 判定不能（`UndecidableComparison`）。
- 組（`inline` / `pairs_of` / record の `json_items` が渡す (key, 値)）は組み込みの tuple / list の基底型の slot で
  読む（tuple の subclass の `__iter__` / `__getitem__` / `__len__` を呼ばない）。それ以外の object・長さが 2 でない
  組は JSON にならない値（拒む）。

期待値は実装と独立: 基底型の双子（組は基底の tuple、書き換えの無い型）から作った値、または契約で正当化した拒否
（禁じた hook を呼ぶ前の拒否だけを数える。hook を呼んだ後の拒否は成功に数えない）。
"""

from __future__ import annotations

import dataclasses

import pytest

from scripts.function_tracer_pcode.core import json_encoding, live_values
from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, RESULT_JSON_POLICY

#: 外の code の hook が呼ばれた記録（各 test の初めに空にする）
HOOKS: list = []


def _foreign_getter(value):
    """package の外の file 名の code の getter（呼ばれたら記録して `value` を返す）。"""

    getter = eval(compile("lambda self: (HOOKS.append('getter'), VALUE)[1]", "<foreign>", "eval"),  # noqa: S307
                  {"HOOKS": HOOKS, "VALUE": value})
    return property(getter)


def _prepare(source):
    return RESULT_JSON_POLICY.prepare(source).value()


def _refused(operation):
    """契約の拒否（判定不能か walker の拒否）なら `"refused"`、それ以外は値。"""

    try:
        return operation()
    except (live_values.UndecidableComparison, JsonValueRejected):
        return "refused"


# ---------------------------------------------------------------------------
# A: 外の code の後に再開・呼び出される処理
# ---------------------------------------------------------------------------


def _record_with_rewriting_child(target_class, name, value):
    """`json_items` が、進めると `target_class.name` を外の property に変える子の generator を渡す record。"""

    def rewriting():
        yield 1
        setattr(target_class, name, _foreign_getter(value))
        yield 2

    def items(self):
        yield "child", rewriting()

    return type("Rewriter", (), {"__module__": __name__, "json_items": items})()


def test_a_suspended_record_generator_does_not_resume_after_its_type_lost_trust():
    """反例 A（walker が保持する record の generator）: record の generator が止まっている間に、外の code（宣言して
    いない package の generator）が record の型へ外の property を足す。再開すれば区間の中で getter を呼ぶ。"""

    HOOKS.clear()

    @dataclasses.dataclass(frozen=True)
    class Record:
        first: object
        second: int

        def json_items(self):
            yield "first", self.first
            yield "second", self.second

    twin = _prepare(Record(first=[1, 2], second=7))
    assert twin == {"first": [1, 2], "second": 7}
    record = Record(first=_record_with_rewriting_child(Record, "second", 999), second=7)
    assert _refused(lambda: _prepare(record)) == "refused"
    assert HOOKS == []


def test_a_loop_summary_does_not_read_a_field_whose_class_was_rewritten_by_a_child():
    """反例 A（`LoopSummaryRef`）: `start_expr` の側の子の generator が `limit_expr` を property に変える。変えた後の
    `package_type` は偽なのに getter を呼んで 999 を書いていた。"""

    from scripts.function_tracer_pcode.core.runtime_refs import LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    HOOKS.clear()
    fields = corpus.BASES[LoopSummaryRef]()
    twin = _prepare(LoopSummaryRef(**fields))
    assert twin["limit_expr"] is not None
    fields["start_expr"] = _record_with_rewriting_child(LoopSummaryRef, "limit_expr", 999)
    try:
        result = _refused(lambda: _prepare(LoopSummaryRef(**fields)))
    finally:
        if "limit_expr" in LoopSummaryRef.__dict__:
            delattr(LoopSummaryRef, "limit_expr")
    assert result == "refused"
    assert HOOKS == []


class _Total(json_encoding.Reducer):
    """test の reducer（package の型）: 件数を `self.count` に数える。"""

    __slots__ = ("count",)

    def __init__(self) -> None:
        self.count = 0

    def add(self, element, *, work):
        self.count = self.count + 1

    def result(self, *, work):
        return self.count


def test_a_scan_does_not_call_reducer_methods_resolved_before_its_values_ran_foreign_code():
    """反例 A（`_Scan`）: `add` / `result` は反復の前に引いていた。値の列（宣言していない generator）が reducer の型の
    field を外の property に変えると、引いておいた `add` が区間の中で getter を呼ぶ。"""

    HOOKS.clear()
    assert _prepare(json_encoding.scan([1, 2, 3], _Total())) == 3
    original = _Total.__dict__["count"]

    def values():
        yield 1
        _Total.count = _foreign_getter(999)
        yield 2

    try:
        result = _refused(lambda: _prepare(json_encoding.scan(values(), _Total())))
    finally:
        _Total.count = original
    assert result == "refused"
    assert HOOKS == []


def test_a_record_does_not_continue_after_a_foreign_comparison_rewrote_its_type():
    """同根（比べる側の契約の外の code）: record の `json_items` が owner の比較を呼び、比べた値の外の `__eq__` が record
    の型を書き換える。比較から戻った後の field の読みは getter を呼ぶ。外の code は比較の中でも走る: 戻るときに確かめる。"""

    HOOKS.clear()

    class Rewriting:
        def __eq__(self, other):
            Record.second = _foreign_getter(999)
            return False

        __hash__ = object.__hash__

    @dataclasses.dataclass(frozen=True)
    class Record:
        probe: object
        second: int

        def json_items(self):
            yield "same", live_values.equal(self.probe, object())
            yield "second", self.second

    try:
        result = _refused(lambda: _prepare(Record(probe=Rewriting(), second=7)))
    finally:
        if "second" in Record.__dict__:
            delattr(Record, "second")
    assert result == "refused"
    assert HOOKS == []


# ---------------------------------------------------------------------------
# B: 組の中の構造
# ---------------------------------------------------------------------------


class _LyingPair(tuple):
    """基底の値は ("k", 1)。反復・添字・長さは別の値を返し、呼ばれたら記録する。"""

    def __iter__(self):
        HOOKS.append("iter")
        return iter(("k", 999))

    def __getitem__(self, index):
        HOOKS.append("getitem")
        return ("k", 999)[index]

    def __len__(self):
        HOOKS.append("len")
        return 2


class _LyingList(list):
    def __iter__(self):
        HOOKS.append("iter")
        return iter(["k", 999])


@pytest.mark.parametrize("make", [
    lambda pair: json_encoding.inline(pair),
    lambda pair: json_encoding.pairs_of([pair]),
    lambda pair: json_encoding.pairs_of(iter([pair])),
], ids=["inline", "pairs_of-list", "pairs_of-iterator"])
@pytest.mark.parametrize("pair", [_LyingPair(("k", 1)), _LyingList(["k", 1])], ids=["tuple-subclass", "list-subclass"])
def test_b_a_pair_is_read_through_its_builtin_slots(make, pair):
    """反例 B: `drain_to` の `child_key, target = child` は tuple の subclass の `__iter__` を呼んでいた。期待値は基底の
    tuple の双子（{"k": 1}）、hook は呼ばない。"""

    HOOKS.clear()
    assert _prepare(make(pair)) == {"k": 1}
    assert HOOKS == []


def test_b_a_record_pair_is_read_through_its_builtin_slots():
    """record の `json_items` が渡す組も同じ読み（walker と `scalar_record_dict`）。"""

    HOOKS.clear()
    pair = _LyingPair(("k", 1))

    class Record:
        def json_items(self):
            yield pair

    assert _prepare(Record()) == {"k": 1}
    assert json_encoding.scalar_record_dict(Record()) == {"k": 1}
    assert HOOKS == []


def _fingerprint(source):
    return RESULT_JSON_POLICY.token_fingerprint(source, work=json_encoding.JsonBudget(1 << 20))


def test_b_snapshot_mapping_items_read_pairs_through_their_builtin_slots():
    """snapshot の mapping の整列（`sorted_mapping_items`）も組を基底型の slot で読む（`read_pair`）: 双子（基底の tuple）
    と同じ並び、hook は呼ばない。組でない値・長さの違う組は値の code の前に拒む。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec as Codec

    HOOKS.clear()
    twin = Codec.sorted_mapping_items((("k", 1), ("a", 2)))
    assert Codec.sorted_mapping_items((_LyingPair(("k", 1)), ("a", 2))) == twin
    assert HOOKS == []
    for bad in ((_LyingPair(("k", 1, 2)),), (("k", 1, 2),), ("ab",)):
        with pytest.raises((TypeError, ValueError)):
            Codec.sorted_mapping_items(bad)
    assert HOOKS == []


@pytest.mark.parametrize("make", [
    lambda pair: json_encoding.inline(pair),
    lambda pair: json_encoding.pairs_of([pair]),
], ids=["inline", "pairs_of"])
def test_b_the_token_fingerprint_reads_pairs_through_their_builtin_slots(make):
    """token の digest は dict の組を frame を作る前に引き出して整列する（`push`）: そこでも組は基底型の slot で読み、
    双子（基底の tuple）と同じ digest。hook は呼ばない。"""

    HOOKS.clear()
    assert _fingerprint(make(_LyingPair(("k", 1)))) == _fingerprint(make(("k", 1)))
    assert HOOKS == []
    with pytest.raises(JsonValueRejected):
        _fingerprint(make(_LyingPair(("k", 1, 2))))
    assert HOOKS == []


def _record_running_foreign_code_between_its_pairs():
    """`json_items` が 1 組目と 2 組目の間に外の code の区間（`outside_audit`）を走らせ、その中で自分の型へ外の property
    を足す record（型と、作る関数）。"""

    @dataclasses.dataclass(frozen=True)
    class Record:
        first: int
        second: int

        def json_items(self):
            yield "first", self.first
            with live_values.outside_audit():
                setattr(Record, "second", _foreign_getter(999))
            yield "second", self.second

    return Record


@pytest.mark.parametrize("operation", [
    _prepare,
    _fingerprint,
    json_encoding.scalar_record_dict,
], ids=["walker-frame", "token-digest-drain", "scalar_record_dict"])
def test_a_a_record_generator_does_not_continue_after_foreign_code_between_its_pairs(operation):
    """反例 A の 3 経路: record の generator が進んでいる（frame・token の digest の整列で frame を積む前・
    `scalar_record_dict`）間に外の code が record の型へ外の property を足す。続ければ getter を呼ぶ。区間を抜けるときの
    確かめで、getter の前に判定不能。"""

    HOOKS.clear()
    Record = _record_running_foreign_code_between_its_pairs()
    assert _refused(lambda: operation(Record(first=1, second=7))) == "refused"
    assert HOOKS == []


class _HookedKey(str):
    """基底の値は "k"。hash・比較は記録してから別の値を返す。"""

    def __hash__(self):
        HOOKS.append("hash")
        return 0

    def __eq__(self, other):
        HOOKS.append("eq")
        return True


@pytest.mark.parametrize("make", [
    lambda key: json_encoding.scalar_record_dict(type("Fixed", (), {"json_items": lambda self: iter(((key, 1),))})()),
    lambda key: __import__(
        "scripts.function_tracer_pcode.core.storage", fromlist=["FrozenStorageRecord"]
    ).FrozenStorageRecord((key,), (1,)).to_dict(),
], ids=["record", "frozen-storage-record"])
def test_b_a_fixed_record_key_is_a_str_before_it_is_hashed(make):
    """組の中の構造（key）: 固定の形の record の key を dict へ置く前に `str` そのものか確かめる。双子（基底の str の
    key）は同じ dict、str の subclass の key は hash・比較の hook を呼ぶ前に拒む。"""

    HOOKS.clear()
    assert make("k") == {"k": 1}
    with pytest.raises(TypeError):
        make(_HookedKey("k"))
    assert HOOKS == []


def _record_with_plain_json_items_running_foreign_code():
    """`json_items` が generator でない関数: 外の code の区間で自分の型へ外の property を足してから `self.second` を読み、
    組の列（組み込みの tuple の iterator）を返す record の型。"""

    @dataclasses.dataclass(frozen=True)
    class Record:
        first: int
        second: int

        def json_items(self):
            with live_values.outside_audit():
                setattr(Record, "second", _foreign_getter(999))
            return iter((("first", self.first), ("second", self.second)))

    return Record


def _inside_an_activation(operation):
    """監査済みの code の中（外側に activation がある）で `operation` を呼び、外側の activation の記録が呼ぶ前と同じ数に
    戻ったかも返す。"""

    state = live_values.begin_activation()
    try:
        outer = state.active[-1]
        before = len(outer)
        result = _refused(operation)
        return result, len(outer) == before
    finally:
        live_values.end_activation(state)


@pytest.mark.parametrize("operation", [_prepare, json_encoding.scalar_record_dict], ids=["walker", "scalar_record_dict"])
@pytest.mark.parametrize("outer", [False, True], ids=["alone", "inside-an-activation"])
@pytest.mark.parametrize("make", [
    _record_running_foreign_code_between_its_pairs,
    _record_with_plain_json_items_running_foreign_code,
], ids=["generator", "plain-function"])
def test_a_record_relied_on_while_json_items_runs_is_rechecked_with_or_without_an_outer_activation(make, outer, operation):
    """反例 A の receiver の記録（`begin_reliance`）: 外側に activation があれば receiver はその activation に記録され、無ければ
    activation を積む。どちらでも、`json_items` が走る間・進める間の外の code の後は record の型を確かめ直し、getter を呼ぶ前に
    判定不能。終わった後、外側の activation の記録は呼ぶ前の数に戻る（頼る間だけの記録）。"""

    HOOKS.clear()
    Record = make()
    if outer:
        result, restored = _inside_an_activation(lambda: operation(Record(first=1, second=7)))
        assert restored
    else:
        result = _refused(lambda: operation(Record(first=1, second=7)))
    assert result == "refused"
    assert HOOKS == []


def test_a_fixed_record_leaves_the_outer_activation_as_it_was():
    """双子（外の code の無い record）でも、外側の activation の記録は呼ぶ前の数に戻る。"""

    @dataclasses.dataclass(frozen=True)
    class Record:
        first: int

        def json_items(self):
            yield "first", self.first

    result, restored = _inside_an_activation(lambda: json_encoding.scalar_record_dict(Record(first=1)))
    assert result == {"first": 1} and restored


class _HookedIterator:
    """`__next__` を呼ばれたら記録する iterator（組み込みの iterator でない）。"""

    def __iter__(self):
        return self

    def __next__(self):
        HOOKS.append("next")
        raise StopIteration


@pytest.mark.parametrize("operation", [_prepare, json_encoding.scalar_record_dict], ids=["walker", "scalar_record_dict"])
def test_a_zip_of_a_non_builtin_iterator_returned_by_json_items_is_refused_before_it_is_stepped(operation):
    """`json_items` が返す `zip` は、包んだ iterator が全部組み込みのときだけ組み込みの列（速い経路）。外の iterator を包む
    `zip` は進める前に拒む（双子: 組み込みの iterator の `zip` は同じ組）。"""

    HOOKS.clear()
    twin = type("Twin", (), {"json_items": lambda self: zip(iter(("k",)), iter((1,)))})()
    assert operation(twin) == {"k": 1}
    record = type("Record", (), {"json_items": lambda self: zip(iter(("k",)), _HookedIterator())})()
    with pytest.raises((TypeError, JsonValueRejected)):
        operation(record)
    assert HOOKS == []


@pytest.mark.parametrize("pair", [
    ("k", 1, 2),
    ("k",),
    _LyingPair(("k", 1, 2)),
    type("Pairish", (), {"__iter__": lambda self: (HOOKS.append("iter"), iter(("k", 1)))[1]})(),
], ids=["three", "one", "subclass-three", "iterable-object"])
def test_b_a_value_that_is_not_a_builtin_pair_of_two_is_refused_before_its_code_runs(pair):
    HOOKS.clear()
    for make in (lambda: json_encoding.inline(pair), lambda: json_encoding.pairs_of([pair])):
        with pytest.raises(JsonValueRejected):
            _prepare(make())
    assert HOOKS == []


def test_expression_operands_render_like_the_twin_and_refuse_a_non_expression():
    """`Expression` の子の描画（子ごとに `package_instance` で絞り込む）: 双子と同じ dict、子に式でない値があれば値の code を呼ぶ
    前に `TypeError`。"""

    from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType

    HOOKS.clear()
    leaf = Expression(ExpressionType.CONSTANT, value=1)
    node = Expression(ExpressionType.BINARY_OP, operator="+", operands=[leaf, Expression(ExpressionType.CONSTANT, value=2)])
    rendered = node.to_dict()
    assert [child["value"] for child in rendered["operands"]] == [1, 2]
    hooked = type("Hooked", (), {"__getattr__": lambda self, name: HOOKS.append(name)})()
    bad = Expression(ExpressionType.BINARY_OP, operator="+", operands=[leaf, hooked])
    with pytest.raises(TypeError):
        bad.to_dict()
    assert HOOKS == []


# ---------------------------------------------------------------------------
# J19 の監査の規則（Issue #242 第 11 回）: 実行時の確かめと同じ境界を静的に求める
# ---------------------------------------------------------------------------

_STUB_LIVE_VALUES = """
def package_instance(value, kind): pass
def elements_of(value): pass
def items_of(value): pass
def read_pair(value): pass
"""

_STUB_JSON_ENCODING = """
class Reducer:
    def add(self, element, *, work): pass
    def result(self, *, work): pass
def source_converter(fn): return fn
"""

_STUB_READ_LIMITS = """
def elements_within_limit(values, scan=None): pass
"""

_CASES = '''
from scripts.function_tracer_pcode.core.live_values import elements_of, items_of, package_instance


class Other:
    def __init__(self, f):
        self.f = f


def helper(record):
    yield "a", 1
    yield "b", record.f


class NarrowWithoutTrust:
    def json_items(self):
        value = self.x
        if type(value) is Other:
            yield "a", value.f


class NarrowChecked:
    def json_items(self):
        value = self.x
        if package_instance(value, Other):
            yield "a", value.f


class NarrowAcrossYield:
    def json_items(self):
        value = self.x
        if package_instance(value, Other):
            yield "a", 1
            yield "b", value.f


class NarrowAcrossLoopYield:
    def json_items(self):
        value = self.x
        if package_instance(value, Other):
            for item in elements_of(self.y):
                yield "a", value.f


class ReceiverAcrossYield:
    def json_items(self):
        yield "a", 1
        yield "b", self.f


class ReceiverIntoNewGenerator:
    def json_items(self):
        return helper(self)


class ReceiverDelegated:
    def json_items(self):
        yield from self._items()

    def _items(self):
        yield "a", 1
        yield "b", self.f


class UnpackNonPairs:
    def json_items(self):
        for key, value in elements_of(self.x):
            yield key, value


class UnpackPairs:
    def json_items(self):
        for key, value in items_of(self.x):
            yield key, value


class GeneratorExpressionAcross:
    def json_items(self):
        value = self.x
        if package_instance(value, Other):
            later = (value.f for _ in elements_of(self.y))
            yield "a", 1
            yield "b", later


class GeneratorExpressionFirstIterable:
    def json_items(self):
        value = self.x
        if package_instance(value, Other):
            yield "a", (1 for _ in elements_of(value.f))


class NarrowAcrossWhileYield:
    def json_items(self):
        value = self.x
        if package_instance(value, Other):
            count = 0
            while count < 2:
                count = count + 1
                yield "a", value.f


class YieldInTheCondition:
    def json_items(self):
        value = self.x
        if package_instance(value, Other) and (yield "a", 1) is None:
            yield "b", value.f
'''


def _synthetic_package(root):
    package = root / "scripts" / "function_tracer_pcode"
    (package / "core").mkdir(parents=True)
    (package / "core" / "live_values.py").write_text(_STUB_LIVE_VALUES)
    (package / "core" / "json_encoding.py").write_text(_STUB_JSON_ENCODING)
    (package / "core" / "read_limits.py").write_text(_STUB_READ_LIMITS)
    (package / "cases.py").write_text(_CASES)
    return package


def test_the_audit_requires_checked_narrowing_that_does_not_survive_suspension(tmp_path):
    """J19 の監査は、実行時の確かめが及ぶ形だけを通す: package の型への絞り込みは `package_instance`（型の信頼を
    確かめる）、絞り込んだ値は `yield` の後に使わない（loop の次の繰り返しを含む）、walker の receiver は yield をまたいで
    よいが新しい generator へ渡すと絞り込んだ値と同じ、組でない要素は unpack しない。"""

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as flow

    violations, _analyzed, _index, _missing = flow.audit(_synthetic_package(tmp_path), entry_roots=())
    flagged = {qual.split(".")[0] for module, qual, _line, _message in violations if module == "cases"}
    flagged |= {qual for module, qual, _line, _message in violations if module == "cases" and "." not in qual}
    assert {
        "NarrowWithoutTrust", "NarrowAcrossYield", "NarrowAcrossLoopYield", "helper", "UnpackNonPairs",
        "GeneratorExpressionAcross", "YieldInTheCondition", "NarrowAcrossWhileYield",
    } <= flagged, sorted(violations)
    assert not {
        "NarrowChecked", "ReceiverAcrossYield", "ReceiverDelegated", "UnpackPairs", "GeneratorExpressionFirstIterable",
    } & flagged, sorted(violations)


def test_entry_roots_that_narrow_run_inside_an_activation():
    """J19 の entry root のうち、辿る関数のどれかが `package_instance` で絞り込むものは `live_values.audited_entry`
    （呼ぶ間 activation を積む: 絞り込みを外の code の後に確かめ直す対象にする）。絞り込まない root は宣言しない
    （宣言の集合は辿る関数から決まる: 絞り込みを足せば宣言が要る）。"""

    import ast
    import collections
    import pathlib

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as flow

    root = pathlib.Path(json_encoding.__file__).resolve().parents[1]
    _violations, _analyzed, index, _missing = flow.audit(root)
    callees = collections.defaultdict(set)
    for callee, callers in flow.audit.last.callers.items():
        for caller in callers:
            callees[caller].add(callee)

    def calls_package_instance(key):
        node = index.functions.get(key)
        return node is not None and any(
            isinstance(sub, ast.Call)
            and (getattr(sub.func, "id", None) == "package_instance" or getattr(sub.func, "attr", None) == "package_instance")
            for sub in ast.walk(node)
        )

    def declared(key):
        node = index.functions[key]
        return any(
            getattr(d, "id", None) == "audited_entry" or getattr(d, "attr", None) == "audited_entry"
            for d in node.decorator_list
        )

    mismatched = []
    for module, qual, _params in flow.ENTRY_ROOTS:
        key = (flow.PKG + "." + module, qual)
        seen, stack = set(), [key]
        while stack:
            current = stack.pop()
            if current not in seen:
                seen.add(current)
                stack.extend(callees.get(current, ()))
        if any(calls_package_instance(k) for k in seen) != declared(key):
            mismatched.append(f"{module}.{qual}")
    assert mismatched == []


def test_audited_entry_records_narrowings_and_rechecks_them_after_foreign_code():
    """`audited_entry` の中の絞り込みは activation に入り、外の code の区間を抜けるときに確かめ直す（型を書き換えれば
    判定不能）。入る前と出た後は activation が無い。"""

    @dataclasses.dataclass
    class Narrowed:
        field: int

    value = Narrowed(1)

    @live_values.audited_entry
    def entry():
        assert live_values.package_instance(value, Narrowed)
        with live_values.outside_audit():
            Narrowed.field = _foreign_getter(2)
        return value.field

    HOOKS.clear()
    assert live_values.reliance().active == []
    try:
        with pytest.raises(live_values.UndecidableComparison):
            entry()
    finally:
        del Narrowed.field
    assert live_values.reliance().active == []
    assert HOOKS == []


def test_the_trust_memo_ends_with_the_audited_code_and_holds_nothing():
    """`package_instance` の型の確かめの記録は、監査済みの code の間（activation がある間）だけ使う: stack が空になれば
    捨てる（監査済みの code の外の書き換えは外の code の区間を通らない）。絞り込んだ値を生かし続けない。"""

    import gc
    import weakref

    @dataclasses.dataclass
    class Narrowed:
        field: int

    value = Narrowed(1)
    probe = weakref.ref(value)

    @live_values.audited_entry
    def entry(item):
        return live_values.package_instance(item, Narrowed)

    assert entry(value) is True
    assert live_values.reliance().trusted == {} and live_values.reliance().active == []
    del value
    gc.collect()
    assert probe() is None
    rewritten = Narrowed(2)
    Narrowed.field = _foreign_getter(3)  # 監査済みの code の外の書き換え（外の code の区間を通らない）
    HOOKS.clear()
    try:
        with pytest.raises(live_values.UndecidableComparison):
            entry(rewritten)
    finally:
        del Narrowed.field
    assert HOOKS == []


@pytest.mark.parametrize("value", [b'"injected"', [1, b"]"], {"k": b"x"}], ids=["bytes", "bytes-in-list", "bytes-in-dict"])
def test_a_live_bytes_value_is_not_written_as_the_digest_walker_s_own_bytes(value):
    """同根（walker 自身の印と live な値を同じ stack で型で見分けていた）: `canonical_fingerprint` の stack は byte 列の
    印を `type(x) is bytes` で見分けていたので、値の中の bytes を digest の byte 列としてそのまま流した。期待値は基準の
    digest（`json.dumps` の形）と同じく、bytes は canonical な形を持たない（`TypeError`）。"""

    import json

    from scripts.function_tracer_pcode.core.canonical_digest import canonical_fingerprint

    with pytest.raises(TypeError):
        json.dumps(value)
    with pytest.raises(TypeError):
        canonical_fingerprint(value, work=json_encoding.JsonBudget(1 << 20))



def test_scalar_record_dict_walks_what_json_items_returns_like_the_walker():
    """独立 review 第 11 回 C2: `scalar_record_dict`（walker の外の組の読み）は `json_items` の返す列を walker と同じ規則で辿る:
    上書きした `__iter__` を持つ list の subclass は値の code を呼ぶ前に拒む。"""

    class Rows(list):
        def __iter__(self):
            HOOKS.append("iter")
            return super().__iter__()

    class Record:
        def json_items(self):
            return Rows([("a", 1)])

    HOOKS.clear()
    for read in (json_encoding.scalar_record_dict, _prepare):
        with pytest.raises((TypeError, JsonValueRejected)):
            read(Record())
    assert HOOKS == []


def test_a_declared_generator_returned_by_json_items_resumes_with_its_record_checked():
    """独立 review 第 11 回 P1（と最終 review の receiver の束縛）: `json_items` が宣言した監査済みの generator を返すとき、
    その generator の receiver は generator の第 1 引数（ここでは `params`。record ではない）。止まっている間に record の型を
    書き換えても、generator は record を読まない: 双子（書き換えの無い record）と同じ組で、hook は呼ばない（receiver の
    型を書き換える形は `test_a_declared_generator_of_another_object_returned_by_json_items_rechecks_that_object`）。"""

    from scripts.function_tracer_pcode.core import signature

    @dataclasses.dataclass(frozen=True)
    class Record:
        params: object
        probe: int = 1

        def json_items(self):
            return signature._parameter_descriptor_pairs(self.params)

    twin = _prepare(Record(params={"first": _record_with_rewriting_child(type("Other", (), {}), "probe", 999), "second": 2}))
    record = Record(params={"first": _record_with_rewriting_child(Record, "probe", 999), "second": 2})
    HOOKS.clear()
    try:
        assert _refused(lambda: _prepare(record)) == twin
    finally:
        if "probe" in Record.__dict__ and type(Record.__dict__["probe"]) is property:
            Record.probe = 1
    assert HOOKS == []



def test_a_scan_rechecks_the_reducer_before_result_after_its_last_values_ran_foreign_code():
    """`_Scan` の `result` も、引いた後に外の code（最後の値の後の generator の続き）が走れば呼ぶ前に引き直して確かめる。"""

    HOOKS.clear()
    original = _Total.__dict__["count"]

    def values():
        yield 1
        _Total.count = _foreign_getter(999)  # 最後の要素の後（StopIteration の前）

    try:
        result = _refused(lambda: _prepare(json_encoding.scan(values(), _Total())))
    finally:
        _Total.count = original
    assert result == "refused"
    assert HOOKS == []


class _Rewriting:
    """比べられる・hash されると `target.name` を外の property に変える外の値。"""

    def __init__(self, target, name):
        self.target, self.name = target, name

    def __eq__(self, other):
        setattr(self.target, self.name, _foreign_getter(999))
        return False

    def __hash__(self):
        setattr(self.target, self.name, _foreign_getter(999))
        return 1


class _Comparing(json_encoding.Reducer):
    """test の reducer: `add` / `result` の中で owner の比較を呼び（外の code が走る）、その後に自分の field を読む。"""

    __slots__ = ("count", "probe")

    def __init__(self, probe):
        self.count = 0
        self.probe = probe

    def add(self, element, *, work):
        live_values.equal(self.probe, element)
        self.count = self.count + 1

    def result(self, *, work):
        live_values.equal(self.probe, 0)
        return self.count


@pytest.mark.parametrize("when", ["add", "result"])
def test_a_reducer_does_not_continue_after_foreign_code_inside_its_own_call_rewrote_its_type(when):
    """reducer の `add` / `result` の 1 回の呼び出しの中で外の code が reducer の型を書き換えれば、外の code の区間を
    抜けるときに判定不能（reducer は呼ぶ間の receiver として記録する）。"""

    HOOKS.clear()
    original = _Comparing.__dict__["count"]
    reducer = _Comparing(_Rewriting(_Comparing, "count") if when == "add" else 0)
    if when == "result":
        reducer = _Comparing(0)
        object.__setattr__(reducer, "probe", _Rewriting(_Comparing, "count"))  # add は外の値に触れない
        values = []
    else:
        values = [1]
    try:
        result = _refused(lambda: _prepare(json_encoding.scan(values, reducer)))
    finally:
        _Comparing.count = original
    assert result == "refused"
    assert HOOKS == []


@pytest.mark.parametrize("hashing", ["hash_tree", "contains"])
def test_a_record_does_not_continue_after_a_foreign_hash_rewrote_its_type(hashing):
    """同根（比べる側の契約の外の hash）: record の `json_items` が owner の hash（`hash_tree`・dict の key の探索の
    `contains`）を呼び、外の `__hash__` が record の型を書き換える。外の hash も外の code の区間で走る: 抜けるときに判定不能。"""

    HOOKS.clear()

    @dataclasses.dataclass(frozen=True)
    class Record:
        probe: object
        second: int

        def json_items(self):
            if hashing == "hash_tree":
                live_values.hash_tree(self.probe)
            else:
                live_values.contains({2: 2}, self.probe)  # hash だけが走る（key の比較は無い）
            yield "second", self.second

    try:
        result = _refused(lambda: _prepare(Record(probe=_Rewriting(Record, "second"), second=7)))
    finally:
        if "second" in Record.__dict__:
            delattr(Record, "second")
    assert result == "refused"
    assert HOOKS == []


def test_the_trust_memo_ends_at_foreign_code_even_without_a_recorded_narrowing():
    """`package_instance` の型の確かめの記録は、外の code の区間を抜ければ使わない（その時に頼る絞り込みが残っていなくても:
    次の絞り込みは型を確かめ直す）。"""

    @dataclasses.dataclass
    class Narrowed:
        field: int

    first, second = Narrowed(1), Narrowed(2)

    @live_values.audited_entry
    def entry():
        with live_values.relying_on():
            assert live_values.package_instance(first, Narrowed)
        with live_values.outside_audit():
            Narrowed.field = _foreign_getter(3)
        live_values.package_instance(second, Narrowed)
        return second.field

    HOOKS.clear()
    try:
        with pytest.raises(live_values.UndecidableComparison):
            entry()
    finally:
        del Narrowed.field
    assert HOOKS == []


def test_receiver_items_calls_only_a_declared_audited_generator_of_a_package_type():
    """`receiver_items` の method は package の型の、宣言した監査済みの generator だけ（宣言していない generator は監査の
    外の code: walker が区間の中で record を receiver として進めない）。"""

    calls = []

    class Record:
        def _items(self):
            calls.append("called")
            yield "a", 1

    with pytest.raises(JsonValueRejected):
        _prepare(json_encoding.receiver_items(Record(), "_items"))
    assert calls == []


def test_a_receiver_items_walk_does_not_resume_its_record_after_a_child_rewrote_the_record_type():
    """反例 A の `receiver_items` の経路: 宣言した監査済みの generator が止まっている間（子を辿る間）に、子の外の code が
    record の型へ外の property を足す。再開すれば区間の中で getter を呼ぶ。frame の receiver（record）を出口で確かめ、
    getter の前に判定不能。双子（書き換えの無い子）は同じ組。"""

    HOOKS.clear()

    @dataclasses.dataclass(frozen=True)
    class Record:
        first: object
        second: int

        def _items(self):
            yield "first", self.first
            yield "second", self.second

    json_encoding.audited_generator(Record._items)
    try:
        assert _prepare(json_encoding.receiver_items(Record(first=[1], second=7), "_items")) == {"first": [1], "second": 7}
        record = Record(first=_record_with_rewriting_child(Record, "second", 999), second=7)
        assert _refused(lambda: _prepare(json_encoding.receiver_items(record, "_items"))) == "refused"
    finally:
        json_encoding._AUDITED_GENERATORS.pop(id(Record._items.__code__), None)
    assert HOOKS == []


def test_audited_code_called_by_foreign_code_does_not_reuse_trust_judged_before_the_section():
    """独立 review: 外の code（区間の中）が class を書き換えてから監査済みの code を呼べば、区間の前に確かめた型の信頼
    （`_Reliance.trusted`）を使ってはいけない。中の絞り込みは書き換えた後の型を確かめて判定不能（getter の前）、区間を
    抜けるときも外側の記録を確かめ直して判定不能。"""

    HOOKS.clear()

    @dataclasses.dataclass(frozen=True)
    class Record:
        second: int

    record = Record(second=7)
    seen = {}
    state = live_values.begin_activation()
    try:
        assert live_values.package_instance(record, Record)
        with pytest.raises(live_values.UndecidableComparison):
            with live_values.outside_audit():
                setattr(Record, "second", _foreign_getter(999))
                seen["trusted"] = live_values.package_type(Record)
                inner = live_values.begin_activation()
                try:
                    seen["narrowed"] = _refused(lambda: live_values.package_instance(record, Record))
                finally:
                    live_values.end_activation(inner)
    finally:
        live_values.end_activation(state)
    assert seen == {"trusted": False, "narrowed": "refused"}
    assert HOOKS == []


def test_trust_judged_by_audited_code_inside_a_section_does_not_outlive_later_foreign_code():
    """区間の中で呼ばれた監査済みの code が確かめた型の信頼は、その後に同じ区間の外の code が型を書き換えれば使えない:
    区間を抜けるときにも epoch を数え、外側の確かめ直しは書き換えた後の型を確かめて判定不能（getter の前）。"""

    HOOKS.clear()

    @dataclasses.dataclass(frozen=True)
    class Record:
        second: int

    record = Record(second=7)
    seen = {}
    state = live_values.begin_activation()
    try:
        assert live_values.package_instance(record, Record)
        try:
            with live_values.outside_audit():
                inner = live_values.begin_activation()
                try:
                    seen["inner"] = live_values.package_instance(record, Record)
                finally:
                    live_values.end_activation(inner)
                setattr(Record, "second", _foreign_getter(999))
            seen["exit"] = "continued"
        except live_values.UndecidableComparison:
            seen["exit"] = "refused"
    finally:
        live_values.end_activation(state)
    assert seen == {"inner": True, "exit": "refused"}
    assert HOOKS == []


def _scalar_dict_twice_around_a_rewrite(record_type, record, results):
    """未宣言の generator（walker は 1 歩を外の code の区間で進める）: 1 歩の中で、監査済みの code（`scalar_record_dict`）を
    呼ぶ → record の型へ外の getter を足す → もう一度呼ぶ。結果は `results` に記録する。"""

    def child():
        results.append(_refused_or_raised(lambda: json_encoding.scalar_record_dict(record)))
        setattr(record_type, "second", _foreign_getter(999))
        results.append(_refused_or_raised(lambda: json_encoding.scalar_record_dict(record)))
        yield 1

    return child()


def _refused_or_raised(operation):
    try:
        return operation()
    except (live_values.UndecidableComparison, JsonValueRejected, TypeError):
        return "refused"


def test_audited_code_reentered_twice_from_one_foreign_step_does_not_reuse_trust_across_the_foreign_code_between():
    """第 12 回の反例: 外側の walker の activation が残る状態で、未宣言の generator の 1 回の実行（外の code の区間）の中で
    `scalar_record_dict(record)` → record の型へ外の getter を足す → `scalar_record_dict(record)`。2 回目は 1 回目が確かめた
    型の信頼を使い回して getter を呼び 7 を 999 にしていた。外の code の区間の寿命と外の code が実際に走る期間は同じでない:
    監査済みの code へ入るたび・外の code へ戻るたびに、その間に頼った事実は失効する。2 回目は getter の前に拒む。record は
    監査済みの code の外で作る。"""

    HOOKS.clear()

    @dataclasses.dataclass(frozen=True)
    class Record:
        first: int
        second: int

        def json_items(self):
            # 監査済みの code が receiver を絞り込む（型の信頼を確かめて memo に残す: 1 回目の呼び出しの中）
            if not live_values.package_instance(self, Record):
                raise TypeError("not a Record")
            yield "first", self.first
            yield "second", self.second

    record = Record(first=1, second=7)
    results = []
    holder = type("Holder", (), {"__module__": __name__})()
    holder_items = lambda self: iter((("child", _scalar_dict_twice_around_a_rewrite(Record, record, results)),))
    type(holder).json_items = holder_items
    try:
        _refused(lambda: _prepare(holder))
    finally:
        if isinstance(Record.__dict__.get("second"), property):
            delattr(Record, "second")
    assert results == [{"first": 1, "second": 7}, "refused"]
    assert HOOKS == []


def _self_narrowing_record_type():
    """receiver を絞り込む（型の信頼を memo に残す）json_items と sized leaf の protocol を持つ record の型。"""

    @dataclasses.dataclass(frozen=True)
    class Record:
        first: int
        second: int

        def json_items(self):
            if not live_values.package_instance(self, Record):
                raise TypeError("not a Record")
            yield "first", self.first
            yield "second", self.second

    return Record


@live_values.audited_entry
def _audited_read(record):
    """監査済みの entry root（test の）: record を絞り込んで field を読む。"""

    if not live_values.package_instance(record, type(record)):
        raise TypeError("unexpected")
    second = record.second
    if type(second) is not int:
        raise TypeError("second is not an int")
    return {"first": record.first, "second": second}


_ENTRIES = {
    "scalar_record_dict": lambda record: json_encoding.scalar_record_dict(record),
    "walker": lambda record: _prepare(record),
    "audited_entry": _audited_read,
}


def _reliance_state():
    state = live_values.reliance()
    return (len(state.active), getattr(state, "floor", 0), list(getattr(state, "floors", ())), len(state.walks),
            dict(state.trusted))


@pytest.mark.parametrize("entry", sorted(_ENTRIES))
@pytest.mark.parametrize("outer", ["none", "activation", "walk"])
@pytest.mark.parametrize("shape", ["same-section", "nested-sections", "exception-exit"])
def test_every_entry_reentered_from_foreign_code_rechecks_trust_after_the_foreign_code_between(entry, outer, shape):
    """境界の組み合わせ: 外の code（区間の中）が監査済みの code（入口ごと）を呼ぶ → 外の code が record の型へ外の getter
    を足す → もう一度呼ぶ。1 回目は双子と同じ値、2 回目は getter の前に拒む（hook 0 回）。外側（何も無い / activation /
    walk）・区間の形（同じ区間で 2 回 / 2 回目は入れ子の区間の中 / 1 回目が例外で終わる）に依らない。終わった後、
    reliance の状態（activation・floor・walk・型の信頼の記録）は始める前と同じ。"""

    HOOKS.clear()
    Record = _self_narrowing_record_type()
    record = Record(first=1, second=7)
    call = _ENTRIES[entry]
    results = []
    before = _reliance_state()

    def foreign_step():
        with live_values.outside_audit():
            if shape == "exception-exit":
                # 1 回目は監査済みの code の中（絞り込んで型の信頼を確かめた後）の例外で終わる
                results.append(_refused_or_raised(lambda: call(Record(first=1, second=object()))))
            else:
                results.append(_refused_or_raised(lambda: call(record)))
            setattr(Record, "second", _foreign_getter(999))
            if shape == "nested-sections":
                with live_values.outside_audit():
                    results.append(_refused_or_raised(lambda: call(record)))
            else:
                results.append(_refused_or_raised(lambda: call(record)))

    try:
        if outer == "none":
            _refused_or_raised(foreign_step)
        elif outer == "activation":
            state = live_values.begin_activation()
            try:
                live_values.package_instance(record, Record)
                _refused_or_raised(foreign_step)
            finally:
                live_values.end_activation(state)
        else:
            holder = type("Holder", (), {"__module__": __name__})()
            type(holder).json_items = lambda self: iter((("child", _call_in_a_step(foreign_step)),))
            _refused_or_raised(lambda: _prepare(holder))
    finally:
        if isinstance(Record.__dict__.get("second"), property):
            delattr(Record, "second")
    assert results[-1] == "refused"
    if shape == "exception-exit":
        assert results[0] == "refused"
    elif outer == "walk" and entry == "walker":
        # walk の中で別の walk の作業量を始めない（既存の契約: 何かを走らせる前に拒む）
        assert results[0] == "refused"
    else:
        assert results[0] == {"first": 1, "second": 7}
    assert HOOKS == []
    assert _reliance_state() == before


_SEQUENCE_SEEDS = range(200)


@pytest.mark.parametrize("seed", _SEQUENCE_SEEDS)
def test_any_sequence_of_switches_never_lets_audited_code_trust_a_type_foreign_code_rewrote(seed):
    """外の code ⇄ 監査済みの code の切り替えの任意の列（区間に入る・出る、監査済みの code へ入る・戻る、絞り込む、外の
    code が型を書き換える。入れ子・同じ区間の中の再入・例外での終わりを含む）で: 外の code が型を書き換えた後の、監査済み
    の code の中の絞り込みはどれも判定不能（getter を呼ばない）。書き換えの前は双子と同じ（絞り込める）。列を終えると
    reliance の状態は始める前と同じ。"""

    import random

    HOOKS.clear()
    rng = random.Random(seed)

    @dataclasses.dataclass(frozen=True)
    class Record:
        second: int

    record = Record(second=7)
    before = _reliance_state()
    stack = []  # "section" / "audited"
    rewritten = False
    log = []
    sections = []  # 区間ごとの {"narrowed", "rewritten"}（同じ区間の中の再入を数える）

    try:
        for _step in range(rng.randint(10, 40)):
            ops = ["audited", "section", "narrow", "narrow", "leave"]
            if not stack or stack[-1][0] == "section":
                ops.append("rewrite")  # 外の code（区間の中・監査済みの code の外）だけが書き換える
            op = rng.choice(ops)
            if op == "audited":
                stack.append(("audited", live_values.begin_activation()))
            elif op == "section":
                section = live_values.outside_audit()
                section.__enter__()
                stack.append(("section", section))
                sections.append({"narrowed": False, "rewritten": False})
            elif op == "rewrite":
                if not rewritten:
                    setattr(Record, "second", _foreign_getter(999))
                    rewritten = True
                    if sections:
                        sections[-1]["rewritten"] = True
            elif op == "narrow" and stack and stack[-1][0] == "audited":
                outcome = _refused_or_raised(lambda: live_values.package_instance(record, Record))
                log.append((rewritten, outcome))
                if sections:
                    if sections[-1]["narrowed"] and sections[-1]["rewritten"]:
                        _SEQUENCE_COVERAGE.add("re-entered after a rewrite in the same section")
                    sections[-1]["narrowed"] = True
            elif op == "leave" and stack:
                kind, handle = stack.pop()
                if kind == "section":
                    sections.pop()
                try:
                    if kind == "audited":
                        live_values.end_activation(handle)
                    else:
                        handle.__exit__(None, None, None)
                except live_values.UndecidableComparison:
                    log.append((rewritten, "refused at exit"))
        while stack:
            kind, handle = stack.pop()
            try:
                if kind == "audited":
                    live_values.end_activation(handle)
                else:
                    handle.__exit__(None, None, None)
            except live_values.UndecidableComparison:
                pass
    finally:
        if isinstance(Record.__dict__.get("second"), property):
            delattr(Record, "second")
    for was_rewritten, outcome in log:
        if outcome == "refused at exit":
            assert was_rewritten
        else:
            assert outcome == ("refused" if was_rewritten else True), log
    assert HOOKS == []
    assert _reliance_state() == before
    _SEQUENCE_COVERAGE.update(outcome for was_rewritten, outcome in log if was_rewritten)


_SEQUENCE_COVERAGE: set = set()


def test_switch_sequences_reached_narrowing_after_a_rewrite():
    """上の列の test が、書き換えの後の絞り込みと区間の出口での拒否の両方に届いたこと（seed の選び方の確かめ）。"""

    for seed in _SEQUENCE_SEEDS:
        test_any_sequence_of_switches_never_lets_audited_code_trust_a_type_foreign_code_rewrote(seed)
    assert {"refused", "refused at exit", "re-entered after a rewrite in the same section"} <= _SEQUENCE_COVERAGE


def _call_in_a_step(function):
    """未宣言の generator（walker は 1 歩を外の code の区間で進める）の 1 歩で `function` を呼ぶ。"""

    def child():
        function()
        yield 1

    return child()


def test_a_declared_generator_of_another_object_returned_by_json_items_rechecks_that_object():
    """独立 review: generator でない `json_items` が別の object（`inner`）の宣言した監査済みの generator を返すとき、止まって
    いる generator が頼るのは `inner`（generator の self）。子の外の code が `inner` の型へ外の property を足せば、再開の前に
    判定不能（getter の前）。双子（書き換えの無い子）は同じ組。"""

    HOOKS.clear()

    @dataclasses.dataclass(frozen=True)
    class Inner:
        first: object
        second: int

        def _items(self):
            yield "first", self.first
            yield "second", self.second

    class Outer:
        def __init__(self, inner):
            self.inner = inner

        def json_items(self):
            return self.inner._items()

    json_encoding.audited_generator(Inner._items)
    try:
        assert _prepare(Outer(Inner(first=[1], second=7))) == {"first": [1], "second": 7}
        assert json_encoding.scalar_record_dict(Outer(Inner(first=1, second=7))) == {"first": 1, "second": 7}
        outer = Outer(Inner(first=_record_with_rewriting_child(Inner, "second", 999), second=7))
        assert _refused(lambda: _prepare(outer)) == "refused"
    finally:
        json_encoding._AUDITED_GENERATORS.pop(id(Inner._items.__code__), None)
        if "second" in Inner.__dict__ and isinstance(Inner.__dict__["second"], property):
            delattr(Inner, "second")
    assert HOOKS == []


def test_canonical_cause_tuple_reads_the_same_fields_as_json_items():
    """`canonical_cause_tuple` は field を dataclass の field の表から読む（`json_items` の generator を持たない: yield を
    またぐ絞り込みを作らない）。読む名前と値が `json_items` の組と同じであること（2 つの源がずれない）。"""

    from scripts.function_tracer_pcode.proof.cause_identity import (
        ExecutionCauseKey, RelationalCauseKey, UnaryCauseKey, canonical_cause_tuple,
    )

    keys = [
        UnaryCauseKey(cause_kind="k", binary_content_identity=("b",), function_ir_identity=("f", 1),
                      semantic_object_identity=("o",)),
        RelationalCauseKey(cause_kind="k", comparison_domain=("d",), left_semantic_object=("l",),
                           right_semantic_object=("r",), correspondence_contract=("c",)),
        ExecutionCauseKey(cause_kind="k", comparison_domain=("d",), logical_query_identity=("q",),
                          execution_semantics_identity=("e",)),
    ]
    for key in keys:
        names = [name for name, _value in canonical_cause_tuple(key)]
        assert names == sorted(name for name, _value in key.json_items()), type(key).__name__


def test_a_zip_is_walked_only_when_every_zipped_iterator_is_builtin():
    """`zip` は、包んだ iterator が全部組み込みの容器の iterator のときだけ組み込みの iterator（`zip` の C の実装が組み込みの
    tuple を作るだけ）。generator・上書きした容器の iterator を包む `zip` は辿らない（値の code を呼ぶ前に拒む）。"""

    HOOKS.clear()
    assert _prepare(json_encoding.pairs_of(zip(("a", "b"), (1, 2)))) == {"a": 1, "b": 2}

    def produced():
        HOOKS.append("generator")
        yield 1

    with pytest.raises(JsonValueRejected):
        _prepare(json_encoding.each(zip(produced(), (1,))))
    assert HOOKS == []


def test_every_audited_root_runs_inside_an_activation():
    """監査済みの code（J19 の root）は、どれも owner が積んだ activation の中で走る（`package_instance` が型の信頼を確かめ、
    外の code の後に確かめ直す前提）: record の `json_items`・reducer・converter・`readable_property`・entry root。"""

    seen = {}

    def observe(name):
        seen[name] = bool(live_values.reliance().active)

    class Record:
        def json_items(self):
            observe("json_items")
            yield "a", 1

    class Counting(json_encoding.Reducer):
        __slots__ = ()

        def add(self, element, *, work):
            observe("add")

        def result(self, *, work):
            observe("result")
            return 0

    class Holder:
        __slots__ = ()

        @live_values.readable_property
        def label(self):
            observe("property")
            return "x"

    @live_values.audited_entry
    def entry():
        observe("entry")

    _prepare(Record())
    _prepare(json_encoding.scan([1], Counting()))
    live_values.attribute(Holder(), "label")
    entry()
    from scripts.function_tracer_pcode.core import signature

    _prepare(json_encoding.each([{"name": "p"}], signature.parameter_descriptor_source))
    assert seen == {"json_items": True, "add": True, "result": True, "property": True, "entry": True}
    assert live_values.reliance().active == []


def test_package_instance_checks_trust_inside_audited_code_and_identity_outside():
    """`package_instance` は監査済みの code の中（activation がある）で型の信頼を確かめる（書き換えた型は判定不能）。外
    （analysis の code が同じ関数を呼ぶとき）は契約の外: 型の identity だけ（`type(x) is C` と同じ）。"""

    @dataclasses.dataclass
    class Narrowed:
        field: int

    value = Narrowed(1)
    Narrowed.field = _foreign_getter(2)
    try:
        assert live_values.package_instance(value, Narrowed) is True
        assert live_values.package_instance(value, int) is False
        with live_values.relying_on():
            with pytest.raises(live_values.UndecidableComparison):
                live_values.package_instance(value, Narrowed)
    finally:
        del Narrowed.field
