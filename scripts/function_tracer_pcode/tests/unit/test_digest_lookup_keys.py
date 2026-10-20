# -*- coding: utf-8 -*-
"""digest（と型を落とす再符号化）を lookup / 束ねの key にする箇所の棚卸し（Issue #218、計画 v4 PR-D review r4）。

identity の一致は digest でなく厳密比較で決める（計画 v4 §6.4 の 1）。owner（`core.structural` の
`exact_value_key` / `exact_occurrence_key` / `dedupe_exact` / `ExactRecordIntern`、`authority.contracts` の
`authority_identity_key`）が厳密な identity を作っても、consumer が自分で digest や JSON の文字列にして集合・
dict の key に使うと、digest の衝突や再符号化で別の値が 1 つになる（PR #259 review: call effect の引数の束ね・
call の bucket・P-code の census・signal の重複の除去・前提の束ね・共有 Z3 session の formula で起きていた）。

`_digest_lookup_scan.scan` が見つける node を、baseline（`tests/fixtures/digest_lookup_keys/baseline.json`）と
完全に一致させる。新しい node も、消えた entry も不合格（baseline は縮むだけ）。entry は role を持つ:

* `seal_registry`: 封印された object を自分の digest で引き、object（`is`・seal）を確かめる
* `seal_verification`: 記録した digest を同じ内容の再計算と比べる
* `diagnostic`: 判定に入らない証拠・件数
* `identity_non_decisive`: 同一性を digest で決めるが、併合しても判定の値を作らない（blocker が残る・UNKNOWN /
  TIMEOUT / ERROR の event だけ・静的な入力）
* `identity_follow_up`: 衝突で確定した判定に届き得る、PR-D の範囲外の identity（`owner` に後続を書く）

新しい identity の判定はここに足さず、owner の API を使う。この test の通過は安全性の証明ではない（安全性は
`test_pr_d_identity_consumers.py` の強制衝突の反例が示す）。
"""

from __future__ import annotations

import ast
import collections
import json
from pathlib import Path

from scripts.function_tracer_pcode.tests.unit._digest_lookup_scan import scan

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
BASELINE_PATH = PACKAGE_ROOT / "tests" / "fixtures" / "digest_lookup_keys" / "baseline.json"
ROLES = frozenset({
    "seal_registry", "seal_verification", "diagnostic", "identity_non_decisive", "identity_follow_up",
})


def _baseline():
    return json.loads(BASELINE_PATH.read_text(encoding="utf-8"))["scanned"]


def _hand_recorded():
    return json.loads(BASELINE_PATH.read_text(encoding="utf-8"))["hand_recorded"]


def test_digest_lookup_keys_match_the_baseline_exactly():
    found = scan(PACKAGE_ROOT)
    pinned = collections.Counter(
        {(entry["path"], entry["function"], entry["kind"]): entry["count"] for entry in _baseline()}
    )
    new = sorted((found - pinned).elements())
    stale = sorted((pinned - found).elements())
    assert not new, (
        "a digest (or a type-dropping re-encoding) is used as a lookup / dedupe key: decide identity by exact "
        "comparison (core.structural.exact_value_key / exact_occurrence_key / dedupe_exact / ExactRecordIntern, "
        "authority.contracts.authority_identity_key), or classify it in the baseline: " + repr(new)
    )
    assert not stale, "baseline entries that no longer exist: remove them: " + repr(stale)


def test_every_baseline_entry_has_a_role_a_reason_and_an_owner_when_it_is_a_follow_up():
    for entry in _baseline():
        assert entry["role"] in ROLES, entry
        assert entry.get("why"), entry
        if entry["role"] == "identity_follow_up":
            assert entry.get("owner"), entry
        else:
            assert "owner" not in entry, entry


def test_hand_recorded_digest_equalities_still_exist_where_recorded():
    # 走査しない形（2 つの digest の ==）で見つけた同一性の判定: 場所が消えたら baseline から外す
    for entry in _hand_recorded():
        assert entry["role"] == "identity_follow_up" and entry.get("owner") and entry.get("why"), entry
        source = (PACKAGE_ROOT / entry["path"]).read_text(encoding="utf-8")
        functions = [
            node for node in ast.walk(ast.parse(source))
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == entry["function"]
        ]
        assert functions, entry
        body = "\n".join(ast.get_source_segment(source, node) or "" for node in functions)
        # 記録した比較の source そのもの（直したら場所が消えて、この test が baseline の掃除を求める）
        assert entry["form"] in body, entry


def test_the_scan_finds_the_forms_a_digest_keyed_identity_takes(tmp_path):
    # 走査の検出力: 過去に実際にあった形（束ね・属性の digest の key・sorted の比較・JSON の文字列）を見つける
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "m.py").write_text(
        "import json\n"
        "def dedupe(values):\n"
        "    seen = set()\n"
        "    for value in values:\n"
        "        key = _digest(value)\n"
        "        if key in seen:\n"
        "            continue\n"
        "        seen.add(key)\n"
        "def by_formula(queries):\n"
        "    return {query.contract.formula_digest: query for query in queries}\n"
        "def census(left, right):\n"
        "    return sorted(_digest(item) for item in left) == sorted(_digest(item) for item in right)\n"
        "def by_text(values):\n"
        "    return {json.dumps(value): value for value in values}\n"
        "def by_map(left, right):\n"
        "    return set(map(_digest, left)) == set(map(_digest, right))\n"
        "def keys(values):\n"
        "    return dict.fromkeys(_digest(value) for value in values)\n"
        "def nested(values):\n"
        "    def inner(value, seen):\n"
        "        key = repr(value)\n"
        "        return key in seen\n"
        "    return inner\n"
    )
    found = scan(package)
    assert found[("m.py", "dedupe", "in")] == 1 and found[("m.py", "dedupe", "add")] == 1
    assert found[("m.py", "by_formula", "dict_comp_key")] == 1
    assert found[("m.py", "census", "collection_eq")] == 1
    assert found[("m.py", "by_text", "dict_comp_key")] == 1
    assert found[("m.py", "by_map", "set_of")] == 2
    assert found[("m.py", "keys", "fromkeys")] == 1
    # 入れ子の関数は自分の scope で 1 回だけ数える
    assert found[("m.py", "inner", "in")] == 1 and ("m.py", "nested", "in") not in found
