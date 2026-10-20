# -*- coding: utf-8 -*-
"""Issue #242（第 5 回のレビュー）: 依存先の読み・例外の文字列化の状態・1 回の呼び出しの走査量。

- 依存先: opaque な object（Ghidra の DataType）を読んだことを、その先で API から取得する値の安全の根拠にしない。
  `call_target` から到達する `core/signature` の関数は、API の戻り値（scalar のとき・object から後で読むとき）を
  reader で読む。guard は到達した package の module の関数を同じ規則で検査する（`test_issue242_construction_guard`）。
- 例外: 組み込みの `__str__` が読む状態（`args` の外の `filename` / `filename2` などを含む）のどれか 1 つだけが
  scalar の subclass でも、文字列は双子と同じで、subclass の code を呼ばない。
- 走査量: ref の層の 1 回の呼び出し（入口・key の出口）の中では、確かめ済みの変わらない木を再び辿らない。深さ・
  共有・変わる入力・例外・並行の実行で、走査の数と結果を固定する。
"""

from __future__ import annotations

import dataclasses
import threading
from typing import Any, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import HOOK_CALLS, Liar, LiarStr, view


# ---------------------------------------------------------------------------
# 依存先（core/signature）: API の戻り値を後で読む経路
# ---------------------------------------------------------------------------


class FakeManager:
    def __init__(self, floats):
        self.floats = floats

    def getFloatDataTypes(self):
        return self.floats


class FakeDataType:
    """Ghidra の DataType の代わり（ghidra の module が無い環境の fallback の経路を通る）。値は `wrap` で包んで返す。"""

    def __init__(self, wrap, name, length, *, equivalent=0, undefined=0, manager=None, signed=1):
        self.wrap, self.name, self.length = wrap, name, length
        self.equivalent, self.undefined, self.manager, self.signed = equivalent, undefined, manager, signed

    def getName(self):
        return self.wrap(self.name)

    def getLength(self):
        return self.wrap(self.length)

    def isEquivalent(self, other):
        return self.wrap(self.equivalent)

    def isUndefined(self):
        return self.wrap(self.undefined)

    def isSigned(self):
        return self.wrap(self.signed)

    def getDataTypeManager(self):
        return self.manager


def _lying(value):
    return {int: Liar, str: LiarStr}.get(type(value), lambda v: v)(value)


def _honest(value):
    return value


class FakeFunction:
    def __init__(self, return_type):
        self.return_type = return_type

    def getReturnType(self):
        return self.return_type

    def getName(self):
        return "f"

    def isExternal(self):
        return False

    def isThunk(self):
        return False

    def getEntryPoint(self):
        return 4096


def _declared(wrap, length, equivalent):
    float_candidate = FakeDataType(wrap, "float", 4, equivalent=equivalent)
    manager = FakeManager([float_candidate])
    return FakeDataType(wrap, "int", length, equivalent=equivalent, manager=manager)


@pytest.mark.parametrize(
    "length, equivalent",
    [
        pytest.param(4, 0, id="int_not_float"),  # 基底型なら浮動小数点でない（偽る subclass の真偽は True）
        pytest.param(4, 1, id="float_equivalent"),
        pytest.param(0, 0, id="void_length_zero"),  # 基底型なら void として候補から除く
    ],
)
def test_declared_return_types_read_api_values_obtained_from_objects_later(length, equivalent):
    """P1: object（DataType）を渡した先の `core/signature` が後で取得する `getLength()` / `isEquivalent()` も
    基底型の値で読む。浮動小数点の判定・void の除外が双子と同じで、偽る型の code を呼ばない。"""

    from scripts.function_tracer_pcode.core import call_target

    def run(wrap):
        ref = call_target.CallTargetRef.from_function(FakeFunction(_declared(wrap, length, equivalent)))
        declarations = call_target.call_target_declared_return_data_types(ref)
        return call_target.call_target_returns_floating_value(ref), len(declarations)

    twin = run(_honest)
    HOOK_CALLS.clear()
    built = run(_lying)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert built == twin


@pytest.mark.parametrize("length", [4, 0, -1])
def test_signature_readers_reached_from_refs_read_api_results_on_base_values(length):
    from scripts.function_tracer_pcode.core import signature

    def run(wrap):
        data_type = _declared(wrap, length, 0)
        return (
            signature.get_data_type_display_name(data_type),
            signature.get_declared_type_size_bytes(data_type),
            signature.get_declared_type_signedness(data_type),
            signature.is_void_data_type(data_type),
            signature.is_undefined_data_type(data_type),
            signature.is_floating_data_type(data_type),
            signature.normalize_type_name(wrap("  Int ")),
        )

    twin = run(_honest)
    HOOK_CALLS.clear()
    built = run(_lying)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)


def test_api_returning_a_scalar_directly_is_read_like_its_twin():
    """API の戻り値が scalar そのもの（宣言の型が文字列）のとき。"""

    from scripts.function_tracer_pcode.core import call_target

    def run(wrap):
        ref = call_target.CallTargetRef.from_function(FakeFunction(wrap("double")))
        return call_target.call_target_returns_floating_value(ref), view(call_target.call_target_declared_return_data_types(ref))

    twin = run(_honest)
    HOOK_CALLS.clear()
    assert run(_lying) == twin
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


# ---------------------------------------------------------------------------
# 例外の文字列化: args の外の状態
# ---------------------------------------------------------------------------


def _exception_cases():
    return [
        pytest.param(lambda s, i: OSError(2, "missing", s("/tmp/file")), id="oserror_filename_only"),
        pytest.param(lambda s, i: OSError(2, "missing", "/a", None, s("/b")), id="oserror_filename2_only"),
        pytest.param(lambda s, i: OSError(2, s("missing")), id="oserror_strerror_only"),
        pytest.param(lambda s, i: OSError(i(2), "missing"), id="oserror_errno_only"),
        pytest.param(lambda s, i: FileNotFoundError(2, "missing", s("/tmp/file")), id="oserror_subclass"),
        pytest.param(lambda s, i: UnicodeDecodeError("utf-8", b"x", 0, 1, s("why")), id="unicode_reason_only"),
        pytest.param(lambda s, i: SyntaxError("bad", (s("f.py"), 1, 2, "x", 1, 3)), id="syntax_filename_only"),
        pytest.param(lambda s, i: KeyError(s("k")), id="key_error"),
        pytest.param(lambda s, i: ValueError("m", i(3)), id="args_only"),
        pytest.param(lambda s, i: SystemExit(s("bye")), id="system_exit_code"),
        pytest.param(lambda s, i: RuntimeError(), id="no_state"),
    ]


@pytest.mark.parametrize("make", _exception_cases())
def test_error_text_reads_every_state_the_builtin_str_reads(make):
    """P2: 組み込みの `__str__` が読む状態のどれか 1 つだけが subclass でも、文字列は双子と同じ。"""

    from scripts.function_tracer_pcode.core.call_target import _error_text

    twin = _error_text(make(str, int))
    error = make(LiarStr, Liar)  # 作るときの hash（`OSError` の errno の表）は入力の側
    HOOK_CALLS.clear()
    assert _error_text(error) == twin == str(make(str, int))
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_error_text_of_a_user_subclass_without_its_own_str_uses_the_builtin_state():
    from scripts.function_tracer_pcode.core.call_target import _error_text

    class Failure(OSError):
        pass

    twin = _error_text(Failure(2, "missing", "/tmp/file"))
    error = Failure(2, "missing", LiarStr("/tmp/file"))
    HOOK_CALLS.clear()
    assert _error_text(error) == twin
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_error_text_does_not_guess_when_the_state_cannot_be_rebuilt():
    """閉路を持つ状態（組み込みの木にできない）は推測した文にせず、文字列化できない例外の印にする。"""

    from scripts.function_tracer_pcode.core.call_target import _JVM_NOT_RUNNING_MESSAGES, _error_text

    cycle: list = [Liar(1)]
    cycle.append(cycle)
    HOOK_CALLS.clear()
    text = _error_text(ValueError(cycle))
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert text == "<unprintable ValueError object>" and text not in _JVM_NOT_RUNNING_MESSAGES


def test_error_paths_of_from_function_read_the_exception_state_on_base_values():
    """P2（入口の経路）: API の属性の読みが投げる例外の文字列を JVM の停止の判定に使う経路。"""

    from scripts.function_tracer_pcode.core import call_target

    class Raising:
        def __init__(self, text):
            self.text = text

        def __getattr__(self, name):
            raise OSError(2, "missing", self.text("/tmp/file"))

    def run(text):
        try:
            call_target.CallTargetRef.from_function(Raising(text))
        except OSError as error:
            return ("raised", type(error).__name__, call_target._error_text(error))
        return ("ok",)

    twin = run(str)
    HOOK_CALLS.clear()
    built = run(LiarStr)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert built == twin


# ---------------------------------------------------------------------------
# 1 回の呼び出しの走査量（深さ・共有・変わる入力・例外・並行）
# ---------------------------------------------------------------------------


def _composed_chain(depth, current=None):
    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef, LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    base = LoopSummaryRef(**corpus.BASES[LoopSummaryRef]())
    value: Any = base
    for index in range(depth):
        value = ComposedLoopSummaryRef(prior=value, current=current or base, handoff_proof_key=("handoff", index))
    return value


def _visits(call):
    live_values._TREE_VISITS[0] = 0
    result = call()
    return live_values._TREE_VISITS[0], result


@pytest.mark.parametrize("method", ["stable_key", "semantic_key"])
def test_nested_key_exits_walk_each_subtree_once_per_call(method):
    """P3: 入れ子の key の出口と子の key の読みが同じ部分木を辿り直すと、深さに対して二乗で増えていた。
    1 回の呼び出しの中では確かめ済みの変わらない木を辿らない: 走査の数は深さに比例する（数を固定する）。"""

    counts = {}
    for depth in (8, 16, 32, 64):
        counts[depth], key = _visits(getattr(_composed_chain(depth), method))
        # 走査の数は key の別々の容器の数以上（本体が組み直す途中の子の key も読む）。key の形は python の版で違う:
        # 数そのものは固定せず、段に比例することを固定する（等しさは下の `stable_key` の test）
        assert counts[depth] >= len(_distinct_containers(key))
    per_level = (counts[64] - counts[8]) / 56
    for depth in (16, 32, 64):
        assert counts[depth] == pytest.approx(counts[8] + per_level * (depth - 8), abs=2)  # 段に比例
    assert counts[64] < 8.5 * counts[8]


def test_the_walk_is_quadratic_without_the_scope(monkeypatch):
    """検査の検出力: scope を無効にすると同じ鎖の走査は深さの二乗で増える（上の test が落ちる）。"""

    monkeypatch.setattr(live_values, "_active_memo", lambda: None)
    small = _visits(_composed_chain(8).stable_key)[0]
    large = _visits(_composed_chain(64).stable_key)[0]
    assert large > 20 * small


def _distinct_containers(value, seen=None):
    seen = set() if seen is None else seen
    kind = type(value)
    if kind in (tuple, list, frozenset, set, dict) and id(value) not in seen:
        seen.add(id(value))
        for item in (value if kind is not dict else [*value.keys(), *value.values()]):
            _distinct_containers(item, seen)
    return seen


@pytest.mark.parametrize("depth", [8, 64])
def test_each_container_of_a_key_is_walked_once_per_call(depth):
    """走査の数 = 1 回の呼び出しで作った key の、別々の容器の数（入れ子の出口・子の key の読みが辿り直さない）。"""

    visits, key = _visits(_composed_chain(depth).stable_key)
    assert visits == len(_distinct_containers(key))


def test_shared_subtrees_are_walked_once_per_call():
    """同じ object の部分木は 1 度だけ辿る。同じ値でも別に作った部分木（key の計算を 2 回した結果）は別の容器。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef

    shared_key = (("leaf", 1), ("leaf", 2))

    class Same:
        def stable_key(self):
            return ("same", shared_key, shared_key)  # 同じ object を 2 度持つ DAG

    same_visits, same = _visits(ComposedLoopSummaryRef(prior=Same(), current=Same()).stable_key)
    assert same_visits == len(_distinct_containers(same))
    chain = _composed_chain(16)
    wide_visits, wide = _visits(ComposedLoopSummaryRef(prior=chain, current=chain, handoff_proof_key=("w",)).stable_key)
    assert wide_visits == len(_distinct_containers(wide))


@pytest.mark.parametrize(
    "prior_key",
    [
        pytest.param(lambda shared: ("prior", shared), id="already_plain"),
        # 写しが要る（遅い経路で作り直す）木が、写さない list をそのまま持つ
        pytest.param(lambda shared: ("prior", shared, Liar(3)), id="rebuilt_around_the_list"),
    ],
)
def test_mutable_containers_are_checked_again_after_foreign_code_changes_them(prior_key):
    """変わる容器は memo に入れない: 子の key の後に外の method が list に偽る値を足しても、出口が読む。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef

    shared: list = [1]
    first = prior_key(shared)

    class Prior:
        def stable_key(self):
            return first

    class Current:
        def stable_key(self):
            shared.append(Liar(2))  # 子の key を読んだ後に、外の code が同じ list を変える
            return ("current",)

    HOOK_CALLS.clear()
    key = ComposedLoopSummaryRef(prior=Prior(), current=Current()).stable_key()
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)

    def plain(value):
        kind = type(value)
        if kind in (tuple, list):
            return all(plain(item) for item in value)
        return value is None or kind in (int, str, bool, float)

    assert plain(key), key


def test_the_scope_ends_with_the_outermost_call_even_on_exceptions():
    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef

    class Broken:
        def stable_key(self):
            raise RuntimeError("broken key")

    with pytest.raises(RuntimeError):
        ComposedLoopSummaryRef(prior=Broken(), current=Broken()).stable_key()
    assert (live_values._active_memo() is None and not live_values._verified_trees().nodes)
    _composed_chain(4).stable_key()
    assert (live_values._active_memo() is None and not live_values._verified_trees().nodes)


def test_concurrent_calls_keep_their_own_scopes():
    chains = [_composed_chain(depth) for depth in (6, 12, 24, 48)]
    expected = [chain.stable_key() for chain in chains]
    results: dict = {}
    errors: list = []

    def worker(index):
        try:
            for _ in range(20):
                results.setdefault(index, []).append(chains[index % 4].stable_key())
        except Exception as error:  # pragma: no cover - 失敗の報告
            errors.append(error)

    threads = [threading.Thread(target=worker, args=(index,)) for index in range(8)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    assert errors == []
    for index, keys in results.items():
        assert all(key == expected[index % 4] for key in keys)
    assert (live_values._active_memo() is None and not live_values._verified_trees().nodes)


def test_the_scope_does_not_change_results_for_lying_and_honest_inputs():
    """scope の memo は結果を変えない: 双子（scope の外で作った key）と同じ。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef

    class Keyed:
        def __init__(self, wrap):
            # 入力（偽る値を持つ key）は数える前に作る: 作るときの hash は入力の側
            self.key = ("k", (wrap(1), (wrap("x"),)), frozenset({wrap(2)}), [wrap(3)])

        def stable_key(self):
            return self.key

    def build(wrap):
        prior, current = Keyed(wrap), Keyed(wrap)
        HOOK_CALLS.clear()
        return ComposedLoopSummaryRef(prior=prior, current=current, handoff_proof_key=("h", 1)).stable_key()

    twin = build(_honest)
    built = build(_lying)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)


def test_pcode_ordinals_compare_api_objects_without_their_scalar_code():
    """API の iterator が返す object と op の等しさ: どちらかが scalar の subclass でも `__eq__` を呼ばない。"""

    from scripts.function_tracer_pcode.core.runtime_refs import pcode

    class Iterator:
        def __init__(self, items):
            self.items = list(items)

        def hasNext(self):
            return bool(self.items)

        def next(self):
            return self.items.pop(0)

    class Parent:
        def __init__(self, items):
            self.items = items

        def getIterator(self):
            return Iterator(self.items)

    class Op:
        def __init__(self, items):
            self.parent = Parent(items)

        def getParent(self):
            return self.parent

    def run(wrap):
        op = Op([])
        op.parent.items = [wrap(5), wrap(6), op]
        return pcode._local_op_ordinal_from_parent(op)

    twin = run(_honest)
    HOOK_CALLS.clear()
    assert run(_lying) == twin
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_pcode_ordinal_scan_reads_the_target_op_once_and_only_when_needed(monkeypatch):
    """親の block の走査は候補ごとに `pcode_op` を読み直さない（走査の量: 候補の数 + 1）。読む順は候補が先。"""

    from scripts.function_tracer_pcode.core.runtime_refs import pcode

    class Iterator:
        def __init__(self, items):
            self.items = list(items)

        def hasNext(self):
            return bool(self.items)

        def next(self):
            return self.items.pop(0)

    class Parent:
        def __init__(self):
            self.items = []

        def getIterator(self):
            return Iterator(self.items)

    class Op:
        def __init__(self, opcode):
            self.parent = Parent()
            self.opcode = opcode

        def getParent(self):
            return self.parent

        def getOpcode(self):
            return self.opcode  # 候補ごとに違う signature（signature の一致で止まらない）

    reads = []
    real = pcode.exact_tree

    def counting(value):
        reads.append(value)
        return real(value)

    monkeypatch.setattr(pcode, "exact_tree", counting)
    for count in (0, 1, 10, 100):
        op = Op(-1)
        candidates = [Op(index) for index in range(count)]
        op.parent.items = candidates + [op]
        reads.clear()
        assert pcode._local_op_ordinal_from_parent(op) == count
        objects = [value for value in reads if type(value) is Op]  # op の読み（signature の比べる値の読みは除く）
        assert sum(1 for value in objects if value is op) == (1 if count else 0)
        assert len(objects) == count + (1 if count else 0)
        if count:
            assert objects[0] is candidates[0] and objects[1] is op  # 候補の読みが先（`x == y` の左辺から）


def test_error_text_of_aliased_builtin_str_uses_the_builtin_slot():
    """`__str__ = ValueError.__str__` のような別名は組み込みの slot（`__objclass__` の型で作り直す）。"""

    from scripts.function_tracer_pcode.core.call_target import _error_text

    class Alias(ValueError):
        __str__ = ValueError.__str__

    class AliasKey(KeyError):
        __str__ = KeyError.__str__

    for kind in (Alias, AliasKey):
        twin = _error_text(kind("a"))
        error = kind(LiarStr("a"))
        HOOK_CALLS.clear()
        assert _error_text(error) == twin == str(kind("a"))
        assert HOOK_CALLS == {}, dict(HOOK_CALLS)


@pytest.mark.skipif(not hasattr(__builtins__ if isinstance(__builtins__, dict) else __builtins__, "ExceptionGroup")
                    and "ExceptionGroup" not in dir(__import__("builtins")), reason="ExceptionGroup は python 3.11 から")
def test_error_text_of_exception_groups_rebuilds_read_only_fields():
    from scripts.function_tracer_pcode.core.call_target import _error_text

    group = getattr(__import__("builtins"), "ExceptionGroup")
    twin = _error_text(group("msg", [ValueError("a")]))
    error = group(LiarStr("msg"), [ValueError("a")])
    HOOK_CALLS.clear()
    assert _error_text(error) == twin == "msg (1 sub-exception)"
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_reached_signature_functions_read_their_own_name_parameters():
    from scripts.function_tracer_pcode.core import signature

    class Program:
        def getDataTypeManager(self):
            return None

    data_type = FakeDataType(_honest, None, 4)

    def run(wrap):
        return (
            signature.is_void_data_type(None, wrap("int"), program=Program()),
            view(signature.resolve_type_spec(wrap("int"), data_type_obj=data_type).to_dict()),
            signature.get_data_type_display_name(None, wrap("int")),
        )

    twin = run(_honest)
    HOOK_CALLS.clear()
    assert run(_lying) == twin
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_mutable_containers_in_keys_are_read_at_every_exit_that_holds_them():
    """変わる容器は読むたびに確かめる（外の code が途中で変え得る: memo に入れない）。各段に新しい list を持つ鎖では、
    list を含む祖先の tuple も変わらない木ではないので、出口ごとに読み直す: 走査は段の 2 乗（数を固定する）。
    これは健全さのための上限で、production の鎖（`ComposedLoopSummaryRef` の loop summary の key）は tuple だけ
    （上の test: 段に比例）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef

    class Current:
        def __init__(self, index):
            self.index = index

        def stable_key(self):
            return ("current", ["c", self.index])

    def chain(depth):
        value: Any = None
        for index in range(depth):
            value = ComposedLoopSummaryRef(prior=value, current=Current(index), handoff_proof_key=("h", index))
        return value

    counts = {}
    for depth in (8, 16, 32):
        counts[depth], key = _visits(chain(depth).stable_key)
        assert counts[depth] > len(_distinct_containers(key))  # 変わる容器を含む部分木は出口ごとに読み直す
    # 段の 2 乗: 増え方そのものが段とともに増える（段に比例する鎖の上の test と対）
    assert (counts[32] - counts[16]) > 3 * (counts[16] - counts[8])
    # 結果は双子と同じ組み込みの木（memo に入れない変わる容器も、出口ごとに確かめた値）
    key = chain(4).stable_key()
    assert key[2] == ("stable", ("current", ["c", 3])) and type(key[2][1][1]) is list


# ---------------------------------------------------------------------------
# 独立 review（第 5 回の対応の 2 巡目）の反例
# ---------------------------------------------------------------------------


def _key_methods(cls):
    import inspect

    return [
        name for name, member in vars(cls).items()
        if inspect.isfunction(getattr(member, "__func__", member)) and not name.startswith("_")
        and (name.endswith("_key") or name == "key") and len(inspect.signature(member).parameters) == 1
    ]


def test_keys_read_type_violating_containers_in_scalar_fields_like_their_twins():
    """F1: scalar / bool / record の注釈の field に置かれた容器（型の誤り）の葉を owner が写す。出口で写さない key
    （`proven=True`）を含む、すべての公開の key が双子と同じ値で、偽る型の code を呼ばない。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import _field_hints, _kind_of
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    checked = 0
    for cls, make in corpus.BASES.items():
        hints = _field_hints(cls)
        names = _key_methods(cls)
        for item in dataclasses.fields(cls):
            if not item.init or _kind_of(hints[item.name]) not in ("scalar", "bool", "record"):
                continue
            for shape in (lambda w: (w("x"),), lambda w: [w(1), (w("y"),)]):
                def build(wrap):
                    return cls(**{**make(), item.name: shape(wrap)})

                try:
                    twin = build(_honest)
                    twin_keys = {name: getattr(twin, name)() for name in names}
                except (TypeError, ValueError, AttributeError):
                    continue
                value = shape(_lying)
                HOOK_CALLS.clear()
                built = cls(**{**make(), item.name: value})
                keys = {name: getattr(built, name)() for name in names}
                assert HOOK_CALLS == {}, (cls.__name__, item.name, dict(HOOK_CALLS))
                assert view(keys) == view(twin_keys), (cls.__name__, item.name)
                # 出力の保証そのもの: key と field の値に scalar の subclass の葉が残らない（受け取った側が比べても
                # subclass の code を呼ばない）
                stored = object.__getattribute__(built, item.name)
                assert not live_values.holds_scalar_subclass(tuple(keys.values())), (cls.__name__, item.name)
                assert not live_values.holds_scalar_subclass(stored), (cls.__name__, item.name)
                checked += 1
    assert checked >= 20


class _SlotError(OSError):
    __slots__ = ("extra",)

    def __str__(self):
        return f"{OSError.__str__(self)} [{self.extra}]"


class _DictError(ValueError):
    def __str__(self):
        return f"{self.args[0]}:{self.note}"


class _NewError(ValueError):
    def __new__(cls, *args):
        return super().__new__(cls, *args)


def _slot_error(s, i):
    error = _SlotError(2, s("missing"))
    error.extra = s("x")
    return error


def _dict_error(s, i):
    error = _DictError(s("a"))
    error.note = s("n")
    return error


@pytest.mark.parametrize(
    "make",
    [
        pytest.param(lambda s, i: type("R", (ValueError,), {"__str__": BaseException.__repr__})(s("x")), id="str_aliases_repr"),
        pytest.param(lambda s, i: type("O", (ValueError,), {"__str__": object.__str__})(s("x")), id="str_aliases_object_str"),
        pytest.param(lambda s, i: ValueError(ValueError(s("x"))), id="nested_exception"),
        pytest.param(lambda s, i: ValueError(KeyError(s("x")), s("y")), id="nested_key_error"),
        pytest.param(lambda s, i: OSError(2, ValueError(s("x")), s("f")), id="nested_in_strerror"),
        pytest.param(lambda s, i: KeyError(ValueError(s("x"))), id="key_error_of_exception"),
        pytest.param(_slot_error, id="user_slots_and_str"),
        pytest.param(_dict_error, id="user_dict_and_str"),
    ],
)
def test_error_text_copies_the_exception_as_its_own_type(make):
    """F2: 文字列化の dispatch（別名の slot・自前の `__str__`）と中の例外の状態も、双子と同じ。"""

    from scripts.function_tracer_pcode.core.call_target import _error_text

    twin_error = make(str, int)
    twin = _error_text(twin_error)
    error = make(LiarStr, Liar)
    HOOK_CALLS.clear()
    assert _error_text(error) == twin
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert twin == str(twin_error)


def test_error_text_does_not_copy_exception_types_with_their_own_new():
    from scripts.function_tracer_pcode.core.call_target import _error_text

    assert _error_text(_NewError("a")) == "a"  # subclass が無ければ `str(error)`
    error = _NewError(LiarStr("a"))
    HOOK_CALLS.clear()
    assert _error_text(error) == "<unprintable _NewError object>"
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


@pytest.mark.skipif("ExceptionGroup" not in dir(__import__("builtins")), reason="ExceptionGroup は python 3.11 から")
def test_error_text_of_exception_groups_with_replaced_args():
    from scripts.function_tracer_pcode.core.call_target import _error_text

    group = getattr(__import__("builtins"), "ExceptionGroup")

    def make(wrap):
        error = group("m", [ValueError("a")])
        error.args = (wrap("x"),)
        return error

    twin = _error_text(make(_honest))
    error = make(_lying)
    HOOK_CALLS.clear()
    assert _error_text(error) == twin == "m (1 sub-exception)"
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_flat_lists_returned_by_key_exits_are_not_memoized():
    """変わる容器は平らでも memo に入れない: 内側の出口が返した list を外の code が変えても、外の出口が読む。"""

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_key

    shared: list = ["x"]

    @runtime_ref_key
    def inner():
        return shared

    @runtime_ref_key
    def outer():
        first = inner()
        shared.append(Liar(2))  # 外の code が同じ list を変える
        return ("outer", first)

    HOOK_CALLS.clear()
    key = outer()
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert type(key[1][1]) is int


def test_entry_scopes_are_emptied_when_the_outermost_entry_returns():
    from scripts.function_tracer_pcode.core.runtime_refs.loops import compare_loop_summaries

    compare_loop_summaries(_composed_chain(3), _composed_chain(4))
    assert live_values._active_memo() is None and not live_values._verified_trees().nodes


class _ChainError(ValueError):
    def __str__(self):
        return f"c:{self.__cause__}:{self.__context__!r}"


class _NoteError(ValueError):
    def __str__(self):
        return f"{self.args[0] if self.args else ''}:{getattr(self, 'note', '')}"


class _DictSubclass(dict):
    pass


class _MultiBase(KeyError, OSError):
    pass


def _chain_error(s, i):
    error = _ChainError("a")
    error.__cause__ = ValueError(s("x"))
    error.__context__ = KeyError(s("y"))
    return error


def _note_only(s, i):
    error = _NoteError("a")  # args は exact: 状態の scalar の subclass は `__dict__` だけ
    error.note = s("n")
    return error


def _dict_subclass_state(s, i):
    error = _NoteError("a")
    error.__dict__ = _DictSubclass({"note": s("n")})
    return error


def _subclass_key_in_dict(s, i):
    error = _NoteError("a")
    error.__dict__[s("k")] = 5
    error.note = s("n")
    return error


@pytest.mark.parametrize(
    "make",
    [
        pytest.param(_chain_error, id="cause_and_context"),
        pytest.param(_note_only, id="instance_dict_only"),
        pytest.param(_dict_subclass_state, id="dict_subclass_state"),
        pytest.param(_subclass_key_in_dict, id="subclass_key_in_dict"),
        pytest.param(lambda s, i: _MultiBase(i(2), s("s"), s("f")), id="several_builtin_bases"),
    ],
)
def test_error_text_copies_every_instance_state_a_user_str_may_read(make):
    from scripts.function_tracer_pcode.core.call_target import _error_text

    twin_error = make(str, int)
    twin = _error_text(twin_error)
    error = make(LiarStr, Liar)
    HOOK_CALLS.clear()
    assert _error_text(error) == twin == str(twin_error)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def _signature_op_variants():
    """seq / target / opcode / mnemonic の読みの形（値・None・例外・scalar の subclass）を組み合わせた fake の op。"""

    import itertools

    class Boom(Exception):
        pass

    def getter(value):
        def read():
            if value is Boom:
                raise Boom("read")
            return value
        return read

    class Space:
        def __init__(self, name):
            self.getName = getter(name)

    class Address:
        def __init__(self, space, offset):
            self.getAddressSpace = getter(space)
            self.getOffset = getter(offset)

    class Seq:
        def __init__(self, target, time, order):
            self.getTarget = getter(target)
            self.getTime = getter(time)
            self.getOrder = getter(order)

    class Op:
        def __init__(self, seq, opcode, mnemonic):
            self.getSeqnum = getter(seq)
            self.getOpcode = getter(opcode)
            self.getMnemonic = getter(mnemonic)

    targets = [None, Boom, Address(Space("ram"), 0x10), Address(Space(LiarStr("ram")), Liar(0x10)),
               Address(Boom, 0x10), Address(Space("ram"), -1)]
    seqs = [None, Boom] + [Seq(target, time, order) for target, time, order in itertools.product(
        targets[:4], (None, 1, Liar(1), Boom), (0, Liar(0), 2, Boom))]
    ops = [Op(seq, opcode, mnemonic) for seq, opcode, mnemonic in itertools.product(
        seqs, (None, 7, Liar(7), "COPY", Boom), (None, "COPY", LiarStr("COPY"), Boom))]
    return ops


def test_lazy_ordinal_signature_match_agrees_with_the_full_signature_comparison():
    """候補の比較（最初に違う field で止まる）は、6 つの field の tuple の比較と同じ真偽。subclass の code を呼ばない。"""

    from scripts.function_tracer_pcode.core.runtime_refs import pcode

    ops = _signature_op_variants()
    signatures = [pcode._pcode_op_ordinal_signature(op) for op in ops]
    targets = list({signature: None for signature in signatures})
    HOOK_CALLS.clear()
    for op, signature in zip(ops, signatures):
        for target in targets:
            assert (pcode._pcode_op_ordinal_signature(op, target) is not None) is (signature == target), (signature, target)
            assert pcode._pcode_op_ordinal_signature(op, target) in (None, signature)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_lazy_ordinal_signature_match_stops_at_the_first_differing_field():
    """同じ block の他の op（order が違う）は、seq と order を読んだところで止まる（走査の量: 候補ごとに 2 つの API）。"""

    from scripts.function_tracer_pcode.core.runtime_refs import pcode

    reads = []

    class Seq:
        def __init__(self, order):
            self.order = order

        def getOrder(self):
            reads.append("order")
            return self.order

        def __getattr__(self, name):
            reads.append(name)
            raise AttributeError(name)

    class Op:
        def __init__(self, order):
            self.seq = Seq(order)

        def getSeqnum(self):
            reads.append("seq")
            return self.seq

        def __getattr__(self, name):
            reads.append(name)
            raise AttributeError(name)

    target = pcode._pcode_op_ordinal_signature(Op(5))
    reads.clear()
    assert pcode._pcode_op_ordinal_signature(Op(6), target) is None
    assert reads == ["seq", "order"]
    reads.clear()
    assert pcode._pcode_op_ordinal_signature(Op(5), target) == target
    assert reads[:2] == ["seq", "order"] and len(reads) > 2


def test_owner_reads_fields_without_the_types_attribute_hooks():
    """owner の field の読み（1 回の C の読みを含む）は、型が上書きした `__getattribute__` / `__getattr__` を通らない
    （`object.__getattribute__` と同じ読み）。書き直しの検出と写しも上書きの無い型と同じ値。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    field_reads = []

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Plain:
        name: Optional[str] = None
        size: Optional[int] = None
        parts: Tuple[int, ...] = ()

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Hooked:
        name: Optional[str] = None
        size: Optional[int] = None
        parts: Tuple[int, ...] = ()

        def __getattribute__(self, attr):
            if attr in ("name", "size", "parts"):
                field_reads.append(attr)
            return object.__getattribute__(self, attr)

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Fallback:
        name: Optional[str] = None
        size: Optional[int] = None
        parts: Tuple[int, ...] = ()

        def __getattr__(self, attr):
            field_reads.append(attr)
            raise AttributeError(attr)

    for values in ({"name": "a", "size": 1}, {"name": LiarStr("a"), "size": Liar(1), "parts": (Liar(2), 3)}):
        twin = Plain(**values)
        for cls in (Hooked, Fallback):
            field_reads.clear()
            built = cls(**values)
            assert field_reads == [], (cls.__name__, field_reads)
            for name in ("name", "size", "parts"):
                value = object.__getattribute__(built, name)
                assert type(value) is type(object.__getattribute__(twin, name))
                assert value == object.__getattribute__(twin, name)


def test_owner_reader_rechecks_attribute_hooks_added_after_first_use():
    """1 度に読む reader の判断は使うたびに確かめる: 構築した後で型に `__getattribute__` を足しても、owner は
    その hook で field を読まない（独立 review の反例）。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    field_reads = []

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Late:
        a: Optional[int] = None
        b: Optional[int] = None

        def __post_init__(self):
            pass

    Late(1, 2)

    def hook(self, attr):
        if attr in ("a", "b"):
            field_reads.append(attr)
        return object.__getattribute__(self, attr)

    Late.__getattribute__ = hook
    built = Late(Liar(1), 2)
    assert field_reads == []
    assert type(object.__getattribute__(built, "a")) is int


def test_owner_reader_cache_does_not_hash_the_type():
    """reader の cache は型の `id` で引く: metaclass の `__hash__` が呼ぶたびに変わる型でも構築が壊れない（独立
    review の反例: 型を 2 回 key にして引くと `KeyError`）。"""

    import dataclasses
    import random

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    draw = random.Random(0)

    class Unstable(type):
        def __hash__(cls):
            return draw.randrange(3)

        def __eq__(cls, other):
            return cls is other

    for trial in range(100):
        @dataclasses.dataclass(frozen=True)
        @runtime_ref_record
        class Record(metaclass=Unstable):
            a: Optional[int] = None
            b: Optional[int] = None

        for index in range(20):
            assert Record(index, Liar(index)).b == index


def test_ordinal_signature_target_of_another_shape_never_matches():
    """`target` が 6 つの field の tuple でなければ、`signature == target` と同じく一致しない（呼ぶ側が渡す値）。"""

    from scripts.function_tracer_pcode.core.runtime_refs import pcode

    class Op:
        def getOpcode(self):
            return 7

    signature = pcode._pcode_op_ordinal_signature(Op())
    assert pcode._pcode_op_ordinal_signature(Op(), signature) == signature
    for target in (signature + (None,), signature[:5], list(signature), ()):
        assert (signature == target) is False
        assert pcode._pcode_op_ordinal_signature(Op(), target) is None


def test_owner_rewrites_only_the_fields_the_validation_rewrote():
    """class 自身の検証が書き直した field（先頭でない field を含む）だけを写し直す。他の field の値は変えない
    （書き直した field の部分集合を、型の field 全部の読みと取り違えない）。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Rewrites:
        name: Optional[str] = None
        size: Optional[int] = None
        parts: Tuple[int, ...] = ()

        def __post_init__(self):
            object.__setattr__(self, "parts", (Liar(self.size), 2))
            object.__setattr__(self, "size", Liar(self.size + 1))

    for name in ("n", LiarStr("n")):
        HOOK_CALLS.clear()
        built = Rewrites(name, 3)
        assert HOOK_CALLS == {}, dict(HOOK_CALLS)
        assert object.__getattribute__(built, "name") == "n" and type(object.__getattribute__(built, "name")) is str
        assert object.__getattribute__(built, "size") == 4 and type(object.__getattribute__(built, "size")) is int
        parts = object.__getattribute__(built, "parts")
        assert parts == (3, 2) and type(parts) is tuple and all(type(item) is int for item in parts)
