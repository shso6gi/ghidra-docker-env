# -*- coding: utf-8 -*-
"""digest を lookup の key にする箇所の棚卸し（Issue #218、計画 v4 PR-D review r4）。

identity の一致は digest でなく厳密比較で決める（計画 v4 §6.4 の 1）。owner（`core.structural` の
`exact_value_key` / `dedupe_exact` / `ExactRecordIntern`、authority の `authority_canonical_text`）が厳密な
identity を作っても、consumer が自分で digest にして集合・dict の key に使うと、digest の衝突で別の値が
1 つになる（PR #259 review: call effect の引数の束ね・call の bucket・P-code の census・signal の重複の除去・
共有 Z3 session の formula で起きていた）。

この test は「`*digest*` という名前の関数の結果（とそれを代入した名前）が `in` / `.add` / `.get` /
`.setdefault` / `.pop` / `[...]` / dict の key に使われる」node を AST で探し、baseline と完全に一致させる。
新しい node は不合格（厳密な identity を使うか、封印・表示の用途なら理由を書いて baseline に足す）。消えた
entry も不合格（baseline は縮むだけ）。

baseline の各 entry は、digest の衝突が確定した判定に届かない理由を持つ。この test の通過は安全性の証明では
ない（安全性は `test_pr_d_identity_consumers.py` の強制衝突の反例が示す）。
"""

from __future__ import annotations

import ast
import collections
from pathlib import Path

PACKAGE_ROOT = Path(__file__).resolve().parents[2]

LOOKUP_METHODS = frozenset({"add", "setdefault", "get", "pop"})

#: (path, 関数, 使い方) → 件数と理由
BASELINE = {
    ("authority/process/operational_extraction.py", "capture_attempt_observation", "subscript"): (
        1, "receipt の digest で観測を引き、同じ receipt の object であることも `is` で確かめる（封印された receipt の参照）",
    ),
    ("authority/sites/runtime.py", "buffer_signal_intents", "get"): (
        2, "Phase 7 の活性化の封印（signal digest）。衝突は同じ site の活性化の取り違えか例外（判定の値を作らない）。"
           "authority 層の digest identity として後続に記録",
    ),
    ("authority/sites/runtime.py", "buffer_signal_intents", "pop"): (2, "同上"),
    ("authority/sites/runtime.py", "record_pre_emission_activation", "get"): (1, "同上"),
    ("authority/sites/runtime.py", "record_pre_emission_activation", "setdefault"): (2, "同上"),
}


def _is_digest_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    name = func.attr if isinstance(func, ast.Attribute) else func.id if isinstance(func, ast.Name) else ""
    return "digest" in name.lower()


def scan(root: Path = PACKAGE_ROOT) -> collections.Counter:
    found: collections.Counter = collections.Counter()
    for path in sorted(root.rglob("*.py")):
        relative = path.relative_to(root)
        if relative.parts[0] == "tests":
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for function in ast.walk(tree):
            if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            tainted = {
                target.id
                for node in ast.walk(function)
                if isinstance(node, ast.Assign) and _is_digest_call(node.value)
                for target in node.targets
                if isinstance(target, ast.Name)
            }

            def digest_valued(node: ast.AST) -> bool:
                return _is_digest_call(node) or (isinstance(node, ast.Name) and node.id in tainted)

            for node in ast.walk(function):
                kind = None
                if isinstance(node, ast.Compare) and any(isinstance(op, (ast.In, ast.NotIn)) for op in node.ops):
                    if digest_valued(node.left):
                        kind = "in"
                elif (
                    isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                    and node.func.attr in LOOKUP_METHODS and node.args and digest_valued(node.args[0])
                ):
                    kind = node.func.attr
                elif isinstance(node, ast.Subscript) and digest_valued(node.slice):
                    kind = "subscript"
                elif isinstance(node, ast.Dict) and any(key is not None and digest_valued(key) for key in node.keys):
                    kind = "dict_key"
                if kind:
                    found[(str(relative), function.name, kind)] += 1
    return found


def test_digest_lookup_keys_match_the_baseline_exactly():
    found = scan()
    pinned = collections.Counter({key: count for key, (count, _why) in BASELINE.items()})
    new = sorted((found - pinned).elements())
    stale = sorted((pinned - found).elements())
    assert not new, (
        "a digest is used as a lookup / dedupe key: decide identity by exact comparison "
        "(core.structural.exact_value_key / dedupe_exact / ExactRecordIntern, authority_canonical_text), "
        "or record why it is a seal: " + repr(new)
    )
    assert not stale, "baseline entries that no longer exist: remove them: " + repr(stale)


def test_every_baseline_entry_has_a_reason():
    for key, (count, why) in BASELINE.items():
        assert count > 0 and why, key


def test_the_scan_finds_a_digest_keyed_dedupe(tmp_path):
    # 走査そのものの検出力（dedupe を digest で書いた module を見つける）
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "m.py").write_text(
        "def _dedupe(values):\n"
        "    seen = set()\n"
        "    for value in values:\n"
        "        key = _digest(value)\n"
        "        if key in seen:\n"
        "            continue\n"
        "        seen.add(key)\n"
    )
    assert scan(package) == collections.Counter({("m.py", "_dedupe", "in"): 1, ("m.py", "_dedupe", "add"): 1})
