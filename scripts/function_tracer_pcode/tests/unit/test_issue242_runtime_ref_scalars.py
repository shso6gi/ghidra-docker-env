# -*- coding: utf-8 -*-
"""Issue #242: runtime ref の scalar の field を組み込みの型そのものにする（`core/runtime_ref_record`）。

- golden: 変更前（main `5c1e8240`。#253 の merge 後）で録った観測（`tests/fixtures/runtime_ref_golden/baseline.json`）と、
  今の tree の観測を比べる。ref の表現・式の表現・fingerprint・構造 key は変わらず、差は意図した差
  D1〜D3（`intended_difference`）だけで、その値は main で双子（型規則で写した入力）から作った値と同じ。
  正規化そのもの（field の型・subclass の code の呼び出し・写せるか）は main の双子と同じになる（D4 を含む）。
- 型規則の表（計画 v3 §4.3）の各行・構築の経路（`replace`・自前の `__init__`・検証の書き直し）・継承・
  `slots=True`・分類を class ごとに 1 度だけ決めること・`package_type` を直接確かめる。
"""

from __future__ import annotations

import dataclasses
import enum
import json
import pathlib
from typing import Any, Dict, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import live_values, runtime_ref_record
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, _safe_offset
from scripts.function_tracer_pcode.core.runtime_ref_record import (
    exact_field_value,
    field_kinds,
    is_runtime_ref_record,
    runtime_ref_record as record_decorator,
)
from scripts.function_tracer_pcode.core.runtime_refs.call_arguments import AbiArgumentSlotRef
from scripts.function_tracer_pcode.core.runtime_refs.locations import (
    AddressValueRef,
    CanonicalLocation,
    LocationBaseRef,
    LocationStep,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef
from scripts.function_tracer_pcode.core.semantic_freeze import _capture_runtime_ref
from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus
from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden.corpus import (
    IE,
    SE,
    SUBCLASS_CALLS,
    Integer,
    JBoolean,
    JByte,
    JDouble,
    JInt,
    JLong,
    JShort,
    JString,
    Weird,
)
from scripts.function_tracer_pcode.tests.tools import record_runtime_ref_golden as recorder

FIXTURE = pathlib.Path(__file__).resolve().parents[1] / "fixtures" / "runtime_ref_golden" / "baseline.json"
#: golden を録った commit（ref の code が変わったら録り直し、ここも変える）
RECORDED_AT = "5c1e82409f2f7009752e9f0cf678f331c2431aee"


@pytest.fixture(scope="module")
def golden() -> Dict[str, Any]:
    return json.loads(FIXTURE.read_text())


@pytest.fixture(scope="module")
def current() -> Dict[str, Any]:
    return recorder.record()


# ---------------------------------------------------------------------------
# golden（#242 AC2）
# ---------------------------------------------------------------------------


def _variant_of(case_id: str) -> corpus.Variant:
    return {variant.case_id: variant for variant in corpus.variants()}[case_id]


def _contains(value: Any, kind: type) -> bool:
    if type(value) is tuple:
        return any(_contains(item, kind) for item in value)
    return type(value) is kind


def intended_difference(case_id: str, item: str) -> Optional[str]:
    """main の観測と変わってよい (variant, 項目) の意図した差の ID（計画 v3 §4.3）。それ以外は `None`。"""

    variant = _variant_of(case_id)
    if variant.field is None:
        return None
    value = variant.make_value()
    kind = corpus.field_kinds(variant.cls)[variant.field]
    if type(value) is Weird and item in ("eq_twin", "hash_eq_twin"):
        # D1: 独自の `__eq__` / `__hash__` を持つ int の subclass は int の値で比べる
        return "D1"
    if kind == "bool" and isinstance(value, int) and type(value) not in (int, bool) and not isinstance(value, enum.Enum):
        # D3: bool の field の int の subclass は bool（JSON が `true`、`stable_key` の分岐が bool に従う）
        return "D3"
    if _contains(value, JBoolean):
        # D2: bool でない field（tuple の葉を含む）の JBoolean は int（`repr` が `'True'` → `'1'`）
        return "D2"
    return None


def test_golden_fixture_is_bound_to_the_recording_commit(golden):
    assert golden["recorded_at_commit"] == RECORDED_AT
    assert golden["tracked_tree_clean"] is True
    assert set(golden["cases"]) == {variant.case_id for variant in corpus.variants()}


def test_invariant_items_match_main_except_the_intended_differences(golden, current):
    unexplained = []
    seen: Dict[str, int] = {}
    for case_id, recorded in golden["cases"].items():
        now = current["cases"][case_id]["input"]
        for item in recorder.INVARIANT_ITEMS:
            if now.get(item) == recorded["input"].get(item):
                continue
            difference = intended_difference(case_id, item)
            # 意図した差は main で双子から作った値と同じ（変わり方まで固定する）
            if difference is not None and now.get(item) == recorded["twin"].get(item):
                seen[difference] = seen.get(difference, 0) + 1
                continue
            unexplained.append((case_id, item, recorded["input"].get(item), now.get(item)))
    assert unexplained == []
    # 列挙した差は実際に起きる（列挙が空回りしていない）
    assert set(seen) == {"D1", "D2", "D3"}, seen


def test_normalized_items_equal_main_twin(golden, current):
    # field の型・subclass の code の呼び出し（D4）・写せるか: 入力から作っても main の双子と同じ
    mismatched = []
    for case_id, recorded in golden["cases"].items():
        now = current["cases"][case_id]["input"]
        for item in recorder.NORMALIZED_ITEMS:
            if now.get(item) != recorded["twin"].get(item):
                mismatched.append((case_id, item, recorded["twin"].get(item), now.get(item)))
    assert mismatched == []


def test_twins_are_unchanged_from_main(golden, current):
    # 双子（exact な値・Enum の member・写さない値だけの入力）の観測は全項目で main と同じ
    changed = [
        (case_id, item)
        for case_id, recorded in golden["cases"].items()
        for item in set(recorded["twin"]) | set(current["cases"][case_id]["twin"])
        if recorded["twin"].get(item) != current["cases"][case_id]["twin"].get(item)
    ]
    assert changed == []


def test_d4_main_called_subclass_code_and_the_normalized_build_does_not(golden, current):
    called_on_main = [
        case_id for case_id, recorded in golden["cases"].items()
        if recorded["input"]["subclass_calls"] and not recorded["twin"]["subclass_calls"]
    ]
    assert any(case_id.startswith("locations.LocationBaseRef|parameter_index|") for case_id in called_on_main)
    for case_id in called_on_main:
        assert current["cases"][case_id]["input"]["subclass_calls"] == [], case_id


def test_ac1_main_left_jint_refs_unsealable_and_they_are_sealable_now(golden, current):
    case_id = "locations.LocationBaseRef|parameter_index|jint"
    assert golden["cases"][case_id]["input"]["sealable"] is False
    assert golden["cases"][case_id]["input"]["field_types"] == {
        "parameter_index": f"{JInt.__module__}.JInt"
    }
    assert current["cases"][case_id]["input"]["sealable"] is True
    assert current["cases"][case_id]["input"]["field_types"] == {}


def test_sort_orders_match_main_or_its_twin_for_d2_only(golden, current):
    for label, orders in golden["sort_orders"].items():
        now = current["sort_orders"][label]
        assert now["twin"] == orders["twin"], label
        if now["input"] != orders["input"]:
            # repr で並べる site の順が変わるのは JBoolean の repr（D2 / D3）だけ: main の双子の順と同じ
            assert now["input"] == orders["twin"], label
            moved = [
                case_id for case_id in now["input"]
                if _variant_of(case_id).field is not None
                and _contains(_variant_of(case_id).make_value(), JBoolean)
            ]
            assert moved, label


def test_equality_matrix_d1(golden, current):
    assert current["equality"]["twin"] == golden["equality"]["twin"]
    differences = {
        (left, right)
        for left, row in golden["equality"]["input"].items()
        for right, value in row.items()
        if current["equality"]["input"][left][right] != value
    }
    # main は `Weird` の偶奇の `__eq__` で別の番地を等しいとした（誤った同一視）。今は int の値で比べる
    assert ("addr_weird_4096", "addr_weird_4098") in differences
    for left, right in differences:
        assert "weird" in left or "weird" in right
        assert current["equality"]["input"][left][right] == golden["equality"]["twin"][left][right]


# ---------------------------------------------------------------------------
# owner の適用範囲
# ---------------------------------------------------------------------------


def _package_ref_classes():
    import importlib
    import pkgutil

    import scripts.function_tracer_pcode.core.runtime_refs as runtime_refs
    from scripts.function_tracer_pcode.core import call_target

    modules = [
        importlib.import_module(f"{runtime_refs.__name__}.{info.name}")
        for info in pkgutil.iter_modules(runtime_refs.__path__)
    ] + [call_target]
    found = set()
    for module in modules:
        for value in vars(module).values():
            if isinstance(value, type) and dataclasses.is_dataclass(value) and value.__module__ == module.__name__:
                found.add(value)
    return found


def test_every_runtime_ref_class_goes_through_the_owner_and_is_in_the_corpus():
    classes = _package_ref_classes()
    assert len(classes) == 36  # PR #253 の `LoopBinderScope` を含む
    assert {cls for cls in classes if not is_runtime_ref_record(cls)} == set()
    # 新しい ref の class は corpus（golden）にも足す
    assert classes == set(corpus.REF_CLASSES)


@pytest.mark.parametrize("cls", sorted(_package_ref_classes(), key=lambda cls: cls.__qualname__))
def test_ref_classes_stay_package_types_and_classify_their_fields(cls):
    # owner が class の namespace に置くのは包んだ `__post_init__` / `__init__` だけ: 信頼する型のまま
    assert live_values.package_type(cls)
    # 注釈（前方参照を含む）が解決でき、分類は dataclass の field の部分集合
    kinds = dict(field_kinds(cls))
    assert set(kinds) <= {item.name for item in dataclasses.fields(cls)}
    assert set(kinds.values()) <= {"scalar", "bool", "tuple", "record"}


def test_decorator_must_be_below_dataclass():
    with pytest.raises(TypeError, match="below @dataclass"):
        @record_decorator
        @dataclasses.dataclass(frozen=True)
        class _Wrong:
            value: int = 0


# ---------------------------------------------------------------------------
# 型規則の表（計画 v3 §4.3）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("make", [JInt, JLong, JShort, JByte, Integer, Weird])
def test_int_subclasses_become_exact_int_without_calling_their_code(make):
    SUBCLASS_CALLS.clear()
    ref = AddressValueRef(address_offset=make(4096), source="ram", program_id=make(7), object_size=make(8))
    assert type(ref.address_offset) is int and ref.address_offset == 4096
    assert type(ref.program_id) is int and type(ref.object_size) is int
    assert SUBCLASS_CALLS == {}


def test_bool_field_takes_bool_and_other_fields_take_the_value_base_type():
    SUBCLASS_CALLS.clear()
    ref = AddressValueRef(
        address_offset=JBoolean(1), source=JString("ram"), is_initialized=JBoolean(1), can_read=JBoolean(0),
        can_write=JInt(2), space_name=JInt(3), object_size=JDouble(8.0),
    )
    assert ref.is_initialized is True and ref.can_read is False and ref.can_write is True
    # 注釈と値の基底型が違っても、値の基底型に写す（注釈に合わせた変換はしない）
    assert type(ref.address_offset) is int and ref.address_offset == 1
    assert type(ref.source) is str and ref.source == "ram"
    assert type(ref.space_name) is int and ref.space_name == 3
    assert type(ref.object_size) is float and ref.object_size == 8.0
    assert SUBCLASS_CALLS == {}


def test_exact_values_enum_members_and_other_objects_are_kept_as_is():
    class Foreign:
        pass

    foreign = Foreign()
    key = ("register", 8, (IE.SEVEN, SE.SYM, True, 1, None, 1.5, "x"))
    ref = AddressValueRef(
        address_offset=IE.SEVEN, source=SE.SYM, is_initialized=1, can_read=True, block_name=foreign,
    )
    assert ref.address_offset is IE.SEVEN and ref.source is SE.SYM
    assert ref.is_initialized == 1 and type(ref.is_initialized) is int
    assert ref.can_read is True and ref.block_name is foreign
    base = LocationBaseRef(kind="storage", storage_identity_key=key)
    # 葉がどれも変わらない tuple は同じ object のまま
    assert base.storage_identity_key is key
    assert exact_field_value(key, "tuple") is key


def test_tuple_fields_walk_exact_tuples_only():
    nested = (JInt(8), (JBoolean(1), JString("s"), (JDouble(1.5),)), IE.ONE, "x")
    base = LocationBaseRef(kind="storage", storage_identity_key=("register",) + nested)
    key = base.storage_identity_key
    assert key == ("register", 8, (1, "s", (1.5,)), IE.ONE, "x")
    assert [type(item) for item in (key[1], key[2][0], key[2][1], key[2][2][0])] == [int, int, str, float]
    assert key[3] is IE.ONE
    # list の容器は辿らない（検証が tuple に書き直したときは、書き直した field を写し直す）
    slot = AbiArgumentSlotRef(ordinal=0, storage_identity_key=[JInt(8), (JInt(4),)])
    assert slot.storage_identity_key == (8, (4,))
    assert [type(slot.storage_identity_key[0]), type(slot.storage_identity_key[1][0])] == [int, int]


@pytest.mark.parametrize(
    "value, expected",
    [
        (JInt(2**31 - 1), 2**31 - 1),
        (JInt(-(2**31)), None),
        (JLong(2**63 - 1), 2**63 - 1),
        (JLong(2**64 - 1), 2**64 - 1),
        (JInt(0), 0),
        (JInt(-1), None),  # 負の parameter index は None（既存の規則）
    ],
)
def test_parameter_index_boundaries(value, expected):
    SUBCLASS_CALLS.clear()
    ref = LocationBaseRef(kind="parameter", parameter_index=value)
    assert ref.parameter_index == expected
    assert expected is None or type(ref.parameter_index) is int
    assert SUBCLASS_CALLS == {}


# ---------------------------------------------------------------------------
# 構築の経路
# ---------------------------------------------------------------------------


def test_replace_frozen_and_custom_init_paths():
    ref = LocationBaseRef(kind="parameter", parameter_index=1)
    replaced = dataclasses.replace(ref, parameter_index=JInt(3))
    assert type(replaced.parameter_index) is int and replaced.parameter_index == 3
    with pytest.raises(dataclasses.FrozenInstanceError):
        replaced.parameter_index = JInt(4)  # type: ignore[misc]

    SUBCLASS_CALLS.clear()
    location = CanonicalLocation(base_ref=ref, offset=JInt(8), size=JLong(4), steps=(LocationStep("offset", JInt(4)),))
    assert (type(location.offset), type(location.size), type(location.steps[0].value)) == (int, int, int)
    assert SUBCLASS_CALLS == {}
    moved = dataclasses.replace(location, offset=JInt(16))
    assert type(moved.offset) is int and moved.offset == 16


def test_call_target_offsets_and_external_flag():
    SUBCLASS_CALLS.clear()
    assert type(_safe_offset(JLong(0x100))) is int and _safe_offset(JLong(-1)) is None
    target = CallTargetRef(
        kind="function", function_name="f", entry_offset=JLong(0x100), is_external=JBoolean(1), library_name="libc",
    )
    assert type(target.entry_offset) is int and target.is_external is True
    assert SUBCLASS_CALLS == {}


def test_main_left_unsealable_refs_and_now_they_seal():
    ref = PcodeOpRef(address_offset=JLong(0x1000), binary_id="B1")
    assert _capture_runtime_ref(LocationBaseRef(kind="parameter", parameter_index=JInt(1))) is not None
    assert _capture_runtime_ref(ref) is not None


def test_field_kinds_are_decided_once_per_class(monkeypatch):
    @dataclasses.dataclass(frozen=True)
    @record_decorator
    class _Counted:
        value: int = 0

    calls = []
    original = runtime_ref_record._field_hints

    def counting(cls):
        calls.append(cls)
        return original(cls)

    monkeypatch.setattr(runtime_ref_record, "_field_hints", counting)
    for value in (JInt(1), JInt(2), 3):
        assert type(_Counted(value).value) is int
    assert calls == [_Counted]


def test_inheritance_runs_each_validation_once_and_normalizes_the_subclass_fields():
    checked = []

    @dataclasses.dataclass(frozen=True)
    @record_decorator
    class _Base:
        value: int = 0

        def __post_init__(self):
            checked.append(type(self.value))

    @dataclasses.dataclass(frozen=True)
    @record_decorator
    class _Child(_Base):
        flag: bool = False

    @dataclasses.dataclass(frozen=True)
    class _Plain(_Base):
        extra: int = 0

    child = _Child(JInt(1), JBoolean(1))
    assert (type(child.value), child.flag) == (int, True)
    plain = _Plain(JInt(2), JInt(3))
    assert (type(plain.value), type(plain.extra)) == (int, int)
    # 基底の検証は 1 度ずつ、写した後の値を見る
    assert checked == [int, int]


def test_slots_and_init_vars():
    @dataclasses.dataclass(frozen=True, slots=True)
    @record_decorator
    class _Slotted:
        value: int = 0
        key: Tuple[Any, ...] = ()

    slotted = _Slotted(JInt(5), (JInt(1),))
    assert type(slotted.value) is int and type(slotted.key[0]) is int
    assert not hasattr(slotted, "__dict__")

    seen = []

    @dataclasses.dataclass(frozen=True)
    @record_decorator
    class _WithInitVar:
        value: int = 0
        hint: dataclasses.InitVar[Optional[str]] = None

        def __post_init__(self, hint):
            seen.append((type(self.value), hint))

    _WithInitVar(JInt(1), "h")
    assert seen == [(int, "h")]


#: golden の中で、同じ入力から 2 度作った観測が違った項目（main の LEGACY の表現が frozenset の object の id を写す:
#: process ごとに変わる）。比べない項目はこれだけ: 増えれば（新しい非決定な表現・ref の比べ方の揺れ）落ちる
KNOWN_UNSTABLE_ITEMS = [
    ("loops.LoopBinderScope|base", "expression_fingerprint"),
    ("loops.LoopBinderScope|base", "expression_to_dict"),
    ("loops.LoopBinderScope|binders|mixed", "expression_fingerprint"),
    ("loops.LoopBinderScope|binders|mixed", "expression_to_dict"),
]


def test_golden_items_left_uncompared_are_only_the_known_process_local_ones(golden, current):
    """golden で比べない項目（`recorder.UNSTABLE`）は、process の中の identity を写すと分かっている項目だけ。今の観測でも
    同じ項目だけが不安定（main と head の両方で決まらない表現）。"""

    def unstable(record):
        return sorted({
            (case_id, item)
            for case_id, sides in record["cases"].items()
            for side in ("input", "twin")
            for item, value in sides[side].items()
            if value == recorder.UNSTABLE
        })

    assert unstable(golden) == KNOWN_UNSTABLE_ITEMS
    assert unstable(current) == KNOWN_UNSTABLE_ITEMS
