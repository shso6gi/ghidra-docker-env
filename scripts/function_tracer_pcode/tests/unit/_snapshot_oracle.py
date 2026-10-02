# -*- coding: utf-8 -*-
"""再利用の test の oracle: 2 つの snapshot が「同じ snapshot」か（Issue #219 PR-219-B）。

production の witness・正規化・digest を使わず、snapshot そのものの比べ方から決める:

* field の値は、snapshot の等しさ（dataclass の `==`。容器は要素ごとに `a is b or a == b`）で比べる。
  そのうえで、`==` が隠す型の違い（list / tuple、bool / int、容器の型）も違いとする
* snapshot が参照で持つ値（`snapshot_id` の要素。`create` は写さない）は、後で変わり得るなら、同じ
  object であることまで求める。変わらない値は等しさで足りる（NaN は等しさの側で、同じ object でなければ違う）
* `diagnostic_refs` の値（`function_ref` などの object）は同じ object であること

repr・digest の一致で代用しない（NaN の repr は等しいが、別の NaN どうしは `==` でない）。
"""

from __future__ import annotations

from types import MappingProxyType
from typing import Any, List, Tuple

_PLAIN = (str, int, bool, bytes)


def _deeply_immutable(value: Any) -> bool:
    """作った後で変わり得ない値か（組み込みの不変な scalar と、それだけから成る tuple / frozenset）。

    値として同一視できるか（`==` が成り立つか）とは別の問い: NaN は不変だが、別の NaN の object どうしは
    等しくない。等しさは `same_value` が要素ごとに（`is` か `==` で）確かめる。
    """

    kind = type(value)
    if value is None or kind in _PLAIN or kind is float:
        return True
    if kind is tuple or kind is frozenset:
        return all(_deeply_immutable(item) for item in value)
    return False


def same_retained(a: Any, b: Any, path: str, problems: List[str]) -> None:
    """参照で持つ値: 変わり得る object（不変な tuple / frozenset と scalar 以外）は同じ object であること。

    不変な容器は要素ごとに辿る（中の変わり得る object が同じなら、外の tuple は別の object でよい）。
    """

    if a is b or _deeply_immutable(a):
        return
    if type(a) is tuple and type(b) is tuple and len(a) == len(b):
        for index, (left, right) in enumerate(zip(a, b)):
            same_retained(left, right, f"{path}[{index}]", problems)
        return
    problems.append(f"{path}: a retained {type(a).__name__} is another object")


def same_value(a: Any, b: Any, path: str, problems: List[str]) -> None:
    """snapshot の等しさ（容器の要素は `is` か `==`）に、型の厳しさを足した比べ方。"""

    if a is b:
        return
    if type(a) is not type(b):
        problems.append(f"{path}: type {type(a).__name__} != {type(b).__name__}")
        return
    if isinstance(a, (tuple, list)):
        if len(a) != len(b):
            problems.append(f"{path}: length {len(a)} != {len(b)}")
            return
        for index, (left, right) in enumerate(zip(a, b)):
            same_value(left, right, f"{path}[{index}]", problems)
        return
    if isinstance(a, (dict, MappingProxyType)):
        if len(a) != len(b):
            problems.append(f"{path}: size {len(a)} != {len(b)}")
            return
        for key, left in a.items():
            if key not in b:
                problems.append(f"{path}: key {key!r} missing")
                continue
            same_value(left, b[key], f"{path}[{key!r}]", problems)
        return
    if isinstance(a, (set, frozenset)):
        if a != b:
            problems.append(f"{path}: set {a!r} != {b!r}")
        return
    if not (a == b):
        problems.append(f"{path}: {a!r} != {b!r}")


def snapshot_problems(hit: Any, built: Any) -> List[str]:
    """2 つの snapshot の違い（空なら同じ snapshot）。"""

    problems: List[str] = []
    same_value(hit.snapshot_id, built.snapshot_id, "snapshot_id", problems)
    for index, (left, right) in enumerate(zip(hit.snapshot_id, built.snapshot_id)):
        # `create` は `snapshot_id` の要素を写さない: 後で変わり得る object は同じ object であること
        same_retained(left, right, f"snapshot_id[{index}]", problems)
    same_value(dict(hit.semantic_fields), dict(built.semantic_fields), "semantic_fields", problems)
    for name in ("semantic_fingerprint", "comparison_fingerprint", "extraction_schema_version"):
        same_value(getattr(hit, name), getattr(built, name), name, problems)
    hit_refs, built_refs = dict(hit.diagnostic_refs), dict(built.diagnostic_refs)
    if hit_refs.get("function_ref") is not built_refs.get("function_ref"):
        problems.append("diagnostic_refs['function_ref']: another object")
    same_value(hit_refs, built_refs, "diagnostic_refs", problems)
    if not (hit == built):
        problems.append("the snapshots are not == (dataclass equality)")
    return problems


def outcome(call) -> Tuple[Any, ...]:
    """呼び出しの結果: snapshot（そのもの）か、例外の型と予算の種類。"""

    from scripts.function_tracer_pcode.core.errors import AnalysisFailureError

    try:
        return ("ok", call())
    except (AnalysisFailureError, TypeError, ValueError) as exc:
        evidence = tuple(item for item in getattr(exc, "evidence_refs", ()) if item.startswith("budget="))
        return ("raised", type(exc).__name__, evidence)


def outcome_problems(reused: Tuple[Any, ...], built: Tuple[Any, ...]) -> List[str]:
    if reused[0] != built[0]:
        return [f"outcome {reused[:1]} != {built[:1]} ({reused!r} / {built!r})"]
    if reused[0] == "raised":
        return [] if reused == built else [f"raised {reused!r} != {built!r}"]
    return snapshot_problems(reused[1], built[1])
