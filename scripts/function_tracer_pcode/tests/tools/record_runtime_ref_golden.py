# -*- coding: utf-8 -*-
"""Issue #242: runtime ref の観測を **変更前** の commit で golden fixture として録る。

正規化の前後で ref の表現・式の表現・fingerprint・構造 key が変わらないこと（#242 AC2）を確かめるには、
変更前の出力が要る。変更前の commit でこの生成器を回し、`tests/fixtures/runtime_ref_golden/corpus.py`
の全 variant について、入力から作った ref と双子（型規則で写した入力）から作った ref の観測を固定する。
class を外から差し替えず、変更前の source を別名で import もしない（package の外の code は
`live_values.package_type` の判定で信頼されないので、観測が変わる）。

録り直し方（ref の code が変わったら録り直す。fixture は録った commit の SHA を持つ）:

```bash
git worktree add /tmp/ref-golden <base commit>
cp -r scripts/function_tracer_pcode/tests/fixtures/runtime_ref_golden /tmp/ref-golden/scripts/function_tracer_pcode/tests/fixtures/
cp scripts/function_tracer_pcode/tests/tools/record_runtime_ref_golden.py /tmp/ref-golden/scripts/function_tracer_pcode/tests/tools/
cd /tmp/ref-golden && python3 -B -m scripts.function_tracer_pcode.tests.tools.record_runtime_ref_golden \
  --output <repo>/scripts/function_tracer_pcode/tests/fixtures/runtime_ref_golden/baseline.json
```
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import pathlib
import subprocess
from typing import Any, Callable, Dict, List

from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import materialize
from scripts.function_tracer_pcode.core.semantic_freeze import _capture_runtime_ref
from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec
from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

#: 観測の項目。`INVARIANT_ITEMS` は正規化の前後で変わらない項目（差は corpus の意図した差だけ）。
#: `NORMALIZED_ITEMS` は正規化そのものの結果（変更後は双子の観測と同じになる）。
INVARIANT_ITEMS = (
    "construct",
    "stable_key_repr",
    "analysis_key_repr",
    "canonical_atom",
    "materialize_json",
    "snapshot_digest",
    "expression_to_dict",
    "expression_fingerprint",
    "expression_structural_key",
    "eq_twin",
    "hash_eq_twin",
)
NORMALIZED_ITEMS = ("field_types", "subclass_calls", "sealable")


def _digest(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8", "surrogatepass")).hexdigest()[:24]


#: process の中でだけ identity になる token の tag（`core/structural.py` の説明。通し番号と nonce を持つ）
_PROCESS_LOCAL_TOKENS = ("exact_tail_unidentified", "process_object")


def _without_unidentified_tokens(key: Any) -> Any:
    """構造 key の process 内だけの token（通し番号と nonce）を、その 2 つを除いた印にする。

    通し番号は同じ process の前の仕事の量で変わり、nonce は token ごとの乱数なので、run の間で比べ
    られない。印の種類（tag と、識別できない理由）は残す（識別できる値と識別できない値の差は消さない）。
    """

    if type(key) is tuple:
        if key and key[0] in _PROCESS_LOCAL_TOKENS:
            return key[:-2] + ("<serial>", "<nonce>")
        return tuple(_without_unidentified_tokens(item) for item in key)
    return key


def _attempt(fn: Callable[[], Any]) -> Any:
    try:
        return fn()
    except Exception as error:  # 観測できないことも観測の結果（変更前後で同じ例外になること）
        return f"<raised {type(error).__name__}>"


def _key_method(ref: Any, name: str) -> Any:
    method = getattr(type(ref), name, None)
    if method is None:
        return "<absent>"
    return _attempt(lambda: repr(method(ref)))


def _construct(cls: type, kwargs: Dict[str, Any]) -> Any:
    corpus.SUBCLASS_CALLS.clear()
    try:
        ref = corpus.build(cls, kwargs)
    except Exception as error:
        return None, f"<raised {type(error).__name__}>", dict(corpus.SUBCLASS_CALLS)
    return ref, "ok", dict(corpus.SUBCLASS_CALLS)


def observe(cls: type, kwargs: Dict[str, Any], twin: Any) -> Dict[str, Any]:
    ref, constructed, calls = _construct(cls, kwargs)
    row: Dict[str, Any] = {"construct": constructed, "subclass_calls": sorted(calls.items())}
    if ref is None:
        return row
    # 組み込みの型（`builtins`）でない値を持つ field だけ（正規化した後は scalar の field から消える）
    row["field_types"] = {
        item.name: f"{type(value).__module__}.{type(value).__qualname__}"
        for item in dataclasses.fields(ref)
        for value in (getattr(ref, item.name, None),)
        if type(value).__module__ != "builtins"
    }
    row["stable_key_repr"] = _key_method(ref, "stable_key")
    row["analysis_key_repr"] = _key_method(ref, "analysis_key")
    stable_key = getattr(type(ref), "stable_key", None)
    row["canonical_atom"] = (
        _attempt(lambda: _digest(repr(canonical_atom(stable_key(ref))))) if stable_key else "<absent>"
    )
    row["materialize_json"] = _attempt(lambda: _digest(json.dumps(materialize(ref), sort_keys=True)))
    row["snapshot_digest"] = _attempt(lambda: _digest(SnapshotFingerprintCodec.digest(ref)))
    expression = _attempt(lambda: Expression.unknown("u", runtime_ref=ref))
    if isinstance(expression, Expression):
        row["expression_to_dict"] = _attempt(lambda: _digest(json.dumps(expression.to_dict(), sort_keys=True)))
        row["expression_fingerprint"] = _attempt(lambda: _digest(SnapshotFingerprintCodec.digest(expression)))
        row["expression_structural_key"] = _attempt(lambda: _digest(repr(_without_unidentified_tokens(expression.structural_key()))))
    else:
        row["expression_to_dict"] = expression
    row["sealable"] = _attempt(lambda: _capture_runtime_ref(ref) is not None)
    if twin is not None:
        row["eq_twin"] = _attempt(lambda: ref == twin)
        row["hash_eq_twin"] = _attempt(lambda: hash(ref) == hash(twin))
    return row


#: 同じ入力から 2 度作った観測が違う項目の印（process の中だけの identity（object の id など）を写す表現。main の
#: 表現そのものが決まらない: 比べない）
UNSTABLE = "<unstable>"


def _stable(variant: Any, make_kwargs: Callable[[], Dict[str, Any]], twin_ref: Any) -> Dict[str, Any]:
    """`observe` を同じ入力から 2 度作って行い、2 度で違う不変の項目を `UNSTABLE` にする（golden に決まらない値を
    書かない。どの class・項目かに依らない規則）。"""

    first = observe(variant.cls, make_kwargs(), twin_ref)
    second = observe(variant.cls, make_kwargs(), twin_ref)
    for item in INVARIANT_ITEMS:
        if item in first and first.get(item) != second.get(item):
            first[item] = UNSTABLE
    return first


def record() -> Dict[str, Any]:
    cases: Dict[str, Any] = {}
    orders: Dict[str, Any] = {}
    by_class: Dict[str, List[Any]] = {}
    for variant in corpus.variants():
        twin_ref, _status, _calls = _construct(variant.cls, variant.twin_kwargs())
        observed = _stable(variant, variant.kwargs, twin_ref)
        twin_observed = _stable(variant, variant.twin_kwargs, twin_ref)
        cases[variant.case_id] = {"input": observed, "twin": twin_observed}
        by_class.setdefault(corpus.class_label(variant.cls), []).append(variant)
    # sort の site（`repr(stable_key())` で並べる）と同じ key で、class ごとの variant を並べた順
    for label, members in by_class.items():
        for side, make_kwargs in (("input", "kwargs"), ("twin", "twin_kwargs")):
            keyed = []
            for variant in members:
                ref, status, _calls = _construct(variant.cls, getattr(variant, make_kwargs)())
                if ref is None or getattr(type(ref), "stable_key", None) is None:
                    continue
                key = _attempt(lambda: repr(ref.stable_key()))
                keyed.append((key, variant.case_id))
            orders.setdefault(label, {})[side] = [case_id for _key, case_id in sorted(keyed)]
    equality: Dict[str, Any] = {}
    for side in ("input", "twin"):
        probes = []
        for name, cls, make in corpus.EQUALITY_PROBES:
            kwargs = make() if side == "input" else corpus.twin_kwargs_of(cls, make())
            probes.append((name, corpus.build(cls, kwargs)))
        equality[side] = {
            name: {other: _attempt(lambda: left == right) for other, right in probes} for name, left in probes
        }
    return {"cases": cases, "sort_orders": orders, "equality": equality}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    head = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    dirty = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"], capture_output=True, text=True, check=True,
    ).stdout.strip()
    payload = {"recorded_at_commit": head, "tracked_tree_clean": not dirty, **record()}
    pathlib.Path(args.output).write_text(dump(payload))


def dump(payload: Dict[str, Any]) -> str:
    """1 行 1 case の JSON（差分を case ごとに読める）。"""

    def compact(value: Any) -> str:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

    lines = ["{"]
    tops = sorted(payload)
    for position, top in enumerate(tops):
        value = payload[top]
        tail = "," if position + 1 < len(tops) else ""
        if isinstance(value, dict):
            lines.append(f" {compact(top)}:{{")
            items = sorted(value.items())
            for index, (key, item) in enumerate(items):
                lines.append(f"  {compact(key)}:{compact(item)}" + ("," if index + 1 < len(items) else ""))
            lines.append(" }" + tail)
        else:
            lines.append(f" {compact(top)}:{compact(value)}{tail}")
    lines.append("}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    main()
