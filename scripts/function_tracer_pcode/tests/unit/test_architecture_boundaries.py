# -*- coding: utf-8 -*-
"""layer test では表せない module 単位の境界（計画 §4.8）。

`test_import_layers.py` が層どうしの向き（`core < ... < cli`）を固定するのに
対して、ここは **同じ層の中で責務 owner を分けたことが崩れていないか** を見る。
どちらも AST の import / 参照を読むだけで、新しい lint 機構は作らない。

PR-22-B が置く境界:

* 意味 snapshot は authority / CLI / checker / config / env を読まない。
  失敗の台帳（`core.errors` の `record_internal_bug` 等）も読まない — 内部バグを
  記録するのは freeze 境界の責務。
* candidate hash で「一致」を決めてよいのは structural identity の owner だけ。
  他所で `structural_hash() == ...` を等価判定に使うと、衝突がそのまま誤判定に
  なる。
* 意味 consumer（identity / renderer / solver query）は凍結済みの式から生の
  runtime object を読み直さない。

後続 PR（budget policy / solver backend / output envelope）が足す境界も、
`_BANNED_IMPORTS` / `_BANNED_ATTRIBUTE_READS` に 1 行足して表現する。
"""

from __future__ import annotations

import ast
import pathlib
from typing import Dict, Iterable, List, Tuple

import pytest


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
PACKAGE_PREFIX = "scripts.function_tracer_pcode."

#: module（package からの相対 path）→ import してはいけない module 接頭辞。
_BANNED_IMPORTS: Dict[str, Tuple[str, ...]] = {
    "core/semantic_snapshot.py": (
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "os",
    ),
    "core/semantic_freeze.py": (
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "os",
    ),
    "core/structural.py": (
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "os",
    ),
}

#: 意味 snapshot が **台帳** へ依存しないこと（例外型の import は許す）。
_LEDGER_NAMES = frozenset(
    {
        "record_internal_bug",
        "raise_limitation",
        "pair_failure_scope",
        "current_pair_ledger",
        "pending_pair_failure",
        "adopt_pair_failure",
        "PairFailureLedger",
        "PairExecutionControl",
    }
)
_LEDGER_FREE_MODULES = ("core/semantic_snapshot.py", "core/structural.py")

#: candidate hash / graph digest で等価を決めてよい唯一の module。
_STRUCTURAL_IDENTITY_OWNER = "core/structural.py"
#: 常に構造 identity を指す名前。
_CANDIDATE_HASH_NAMES = frozenset(
    {"structural_hash", "candidate_hash", "compose_candidate_digest"}
)
#: 構造 identity の API を import している module でだけ構造 identity を指す名前
#: （無関係な module にも同名の局所変数があるため、名前だけでは判断しない）。
_CONTEXTUAL_CANDIDATE_HASH_NAMES = frozenset({"candidate_digest"})
_IDENTITY_API_MODULES = (
    "scripts.function_tracer_pcode.core.semantic_snapshot",
    "scripts.function_tracer_pcode.core.structural",
)

#: 凍結済みの式から読み直してはいけない生 object（意味 consumer 側）。
_RAW_SEMANTIC_ATTRIBUTES = frozenset({"data_type_obj"})
_SNAPSHOT_ONLY_MODULES = (
    "core/render_smt/widths.py",
    "core/render_smt/unknowns.py",
)


def _module_files() -> Iterable[pathlib.Path]:
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT)
        if relative.parts and relative.parts[0] == "tests":
            continue
        yield path


def _relative(path: pathlib.Path) -> str:
    return path.relative_to(PACKAGE_ROOT).as_posix()


def _parse(path: pathlib.Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _imported_modules(tree: ast.Module) -> List[Tuple[str, int]]:
    names: List[Tuple[str, int]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                names.append((alias.name, node.lineno))
        elif isinstance(node, ast.ImportFrom):
            if node.level:
                # 相対 import はこの package では使っていない（絶対 import 規約）。
                continue
            if node.module:
                names.append((node.module, node.lineno))
    return names


def _imported_names(tree: ast.Module) -> List[Tuple[str, int]]:
    names: List[Tuple[str, int]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            for alias in node.names:
                names.append((alias.name, node.lineno))
    return names


@pytest.mark.parametrize("module_path", sorted(_BANNED_IMPORTS))
def test_banned_imports_are_absent(module_path):
    path = PACKAGE_ROOT / module_path
    assert path.exists(), module_path
    banned = _BANNED_IMPORTS[module_path]
    offenders = [
        f"{module_path}:{lineno} imports {name}"
        for name, lineno in _imported_modules(_parse(path))
        for prefix in banned
        if name == prefix or name.startswith(prefix + ".")
    ]
    assert offenders == [], offenders


@pytest.mark.parametrize("module_path", _LEDGER_FREE_MODULES)
def test_semantic_representation_does_not_use_the_failure_ledger(module_path):
    """表現層は「失敗をどう記録するか」を知らない。

    知らせると、意味の表現を変えるたびに実行制御まで巻き込むことになる。内部
    バグを記録するのは freeze 境界 (`core/semantic_freeze.py`) だけ。
    """

    path = PACKAGE_ROOT / module_path
    offenders = [
        f"{module_path}:{lineno} imports {name}"
        for name, lineno in _imported_names(_parse(path))
        if name in _LEDGER_NAMES
    ]
    assert offenders == [], offenders


def test_only_the_structural_owner_decides_equality_from_a_candidate_hash():
    """candidate hash は候補の絞り込み専用。

    他所で `a.structural_hash() == b.structural_hash()` のように書くと、衝突が
    そのまま誤った「同じ式」になる。等価は `structural_equals` が完全比較で
    決める。
    """

    offenders: List[str] = []
    for path in _module_files():
        relative = _relative(path)
        if relative == _STRUCTURAL_IDENTITY_OWNER:
            continue
        tree = _parse(path)
        banned = set(_CANDIDATE_HASH_NAMES)
        if any(
            name in _IDENTITY_API_MODULES for name, _lineno in _imported_modules(tree)
        ):
            banned |= _CONTEXTUAL_CANDIDATE_HASH_NAMES
        for node in ast.walk(tree):
            if not isinstance(node, ast.Compare):
                continue
            if not any(isinstance(op, (ast.Eq, ast.NotEq)) for op in node.ops):
                continue
            for side in [node.left, *node.comparators]:
                name = _identity_name(side)
                if name in banned:
                    offenders.append(f"{relative}:{node.lineno} compares {name}")
    assert offenders == [], offenders


def _identity_name(node: ast.AST):
    if isinstance(node, ast.Call):
        return _identity_name(node.func)
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Name):
        return node.id
    return None


@pytest.mark.parametrize("module_path", _SNAPSHOT_ONLY_MODULES)
def test_semantic_consumers_read_the_projection_not_the_raw_objects(module_path):
    """SMT 側の意味 consumer は凍結済みの投影を読む。

    生の `data_type_obj`（JVM object）をここで読み直すと、凍結後にその object が
    変わったときに幅や宣言だけが黙って変わってしまう。
    """

    path = PACKAGE_ROOT / module_path
    offenders = []
    for node in ast.walk(_parse(path)):
        if isinstance(node, ast.Attribute) and node.attr in _RAW_SEMANTIC_ATTRIBUTES:
            offenders.append(f"{module_path}:{node.lineno} reads .{node.attr}")
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "getattr"
            and len(node.args) >= 2
            and isinstance(node.args[1], ast.Constant)
            and node.args[1].value in _RAW_SEMANTIC_ATTRIBUTES
        ):
            offenders.append(f"{module_path}:{node.lineno} reads {node.args[1].value!r}")
    assert offenders == [], offenders


def test_identity_kinds_are_not_merged_into_one_type():
    """structural identity を万能 identity にしない。

    同じ式でも solver 宣言や rewrite 文脈が違えば別物なので、片方の都合で
    他方の一致条件を動かせる形（1 つの class が全部を返す）にはしない。
    """

    from scripts.function_tracer_pcode.core import structural

    identity = structural.StructuralIdentity
    exposed = {name for name in vars(identity) if not name.startswith("_")}
    assert exposed == {"candidate_hash", "equals", "key", "identity_digest"}, exposed
    for forbidden in ("solver_query", "rewrite", "authority_digest", "query_identity"):
        assert not hasattr(identity, forbidden), forbidden
