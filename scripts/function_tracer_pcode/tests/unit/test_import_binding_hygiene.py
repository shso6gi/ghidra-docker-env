"""Import-binding hygiene guardrail (Issue #51).

Issue #51 で除去した「同じ module-level 名が 2 回以上 bind される」状態の再発を
防ぐための test。対象はそれだけで、import surface 全体を仕様化はしない。

重複 binding は挙動を変えないが、読み手には「どちらの import 元が有効なのか」が
見えない。`analysis/returns/_api` の late-binding wrapper と `_shared` の実クラスの
ように **source が違って object も違う**組み合わせでは、最後に評価された binding が
勝つという Python の規則を知らないと取り違える。Issue #51 の整理では、
module 実行後に有効な binding を保存したまま shadow 側だけを消した。

対象範囲は `ast.Module.body` **直下**の `Import` / `ImportFrom` のみ。

* 同じ 1 つの import 文の中で同じ alias を 2 回書いた場合も検出する。
* 関数内 / class 本体内の import は対象外。循環回避のための意図的な遅延 import で
  あり、層依存の追跡は `test_import_layers.py` が担当する。
* `if TYPE_CHECKING:` 内の型注釈用 import や `try: ... except ImportError:` の
  代替 import も対象外。これらは「runtime 用と型注釈用」「本命と fallback」という
  別の意図を持つ binding であり、Issue #51 が問題にした「同じ import ブロックが
  重ねて貼られて後の binding が前を shadow する」状態とは別物。
"""
from __future__ import annotations

import ast
from collections import defaultdict
from pathlib import Path

PACKAGE_ROOT = Path(__file__).resolve().parents[2]


def _package_modules():
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts:
            continue
        yield path


def _bound_names(stmt):
    """(bind される名前, 読みやすい source 表記) を列挙する。"""
    if isinstance(stmt, ast.Import):
        for alias in stmt.names:
            yield alias.asname or alias.name.split(".")[0], f"import {alias.name}"
    elif isinstance(stmt, ast.ImportFrom):
        module = ("." * (stmt.level or 0)) + (stmt.module or "")
        for alias in stmt.names:
            if alias.name == "*":
                continue
            yield alias.asname or alias.name, f"from {module} import {alias.name}"


def _duplicate_bindings(path):
    """`Module.body` 直下の import 文だけを見て、重複 binding を返す。"""
    tree = ast.parse(path.read_text(encoding="utf-8"))
    seen = defaultdict(list)
    for stmt in tree.body:
        if not isinstance(stmt, (ast.Import, ast.ImportFrom)):
            continue
        for name, source in _bound_names(stmt):
            seen[name].append((stmt.lineno, source))
    return {name: places for name, places in seen.items() if len(places) > 1}


def test_no_module_level_import_binds_the_same_name_twice():
    offenders = []
    for path in _package_modules():
        for name, places in sorted(_duplicate_bindings(path).items()):
            trail = " -> ".join(f"L{lineno} ({source})" for lineno, source in places)
            offenders.append(f"{path.relative_to(PACKAGE_ROOT)}: {name}: {trail}")
    assert offenders == [], (
        "module-level duplicate import bindings found; keep the binding that is in "
        "effect after the module finishes executing and delete the shadowed one "
        "(Issue #51):\n" + "\n".join(offenders)
    )


def test_the_duplicate_detector_sees_aliases_repeated_inside_one_statement(tmp_path):
    """同一文内の重複も検出する（整理前の `analysis/recurrence/summarizer.py` の形）。"""
    sample = tmp_path / "sample.py"
    sample.write_text(
        "from os import path as p, sep, path as p\n",
        encoding="utf-8",
    )
    duplicates = _duplicate_bindings(sample)
    assert set(duplicates) == {"p"}
    assert [lineno for lineno, _ in duplicates["p"]] == [1, 1]


def test_the_duplicate_detector_ignores_function_and_class_local_imports(tmp_path):
    sample = tmp_path / "sample.py"
    sample.write_text(
        "from os import sep\n"
        "def f():\n"
        "    from os import sep\n"
        "    return sep\n"
        "class C:\n"
        "    from os import sep\n",
        encoding="utf-8",
    )
    assert _duplicate_bindings(sample) == {}


def test_the_duplicate_detector_ignores_module_level_conditional_blocks(tmp_path):
    """`if TYPE_CHECKING:` / `try ... except ImportError` は別の意図の binding。"""
    sample = tmp_path / "sample.py"
    sample.write_text(
        "from typing import TYPE_CHECKING\n"
        "from os import sep\n"
        "if TYPE_CHECKING:\n"
        "    from os import sep\n"
        "try:\n"
        "    from os import sep\n"
        "except ImportError:\n"
        "    sep = '/'\n",
        encoding="utf-8",
    )
    assert _duplicate_bindings(sample) == {}


# --------------------------------------------------------------------------
# checker/checker.py の seam pin
#
# Issue #51 で未使用 import を 25 名削除したので、「残すと決めた名前」だけを
# 限定列挙して固定する。checker.checker の現在の import surface 全体を仕様化は
# しない（それをすると以後の整理が毎回この test の変更を要求する）。
# --------------------------------------------------------------------------

# 「Re-exports kept for callers ...」ブロックの明示的 re-export。
# module 内で未使用のものもここに含む。
CHECKER_REEXPORTS = (
    "AbiRetryMixin",
    "BranchCheckContext",
    "PreflightGateMixin",
    "RecoveryProofMixin",
    "RecurrenceStageMixin",
    "RootCauseMixin",
    "SolverResult",
    "assemble_equivalence_result",
    "build_branch_check_context",
    "build_prepared_dispatch_frame",
    "canonical_abi_error_result",
    "complete_recurrence_promotion_signals",
    "prepare_preflight_projection",
    "prepare_recurrence_promotion",
    "prepare_strategy_runtime",
    "refine_unknown_reasons",
    "run_legacy_strategy",
    "run_strategy_branch",
    "unsupported_smt_result",
)

# tests が module path 経由で import / patch する名前。
#   EquivalenceChecker / StageID / StageSpec: `from ...checker.checker import ...`
#   TypeFixer:                                `patch("...checker.checker.TypeFixer")`
#   PairwiseStrategy / run_check_from_binaries: `checker_module.<name>` への
#                                             patch.object / monkeypatch.setattr
CHECKER_TEST_SEAMS = (
    "EquivalenceChecker",
    "PairwiseStrategy",
    "StageID",
    "StageSpec",
    "TypeFixer",
    "run_check_from_binaries",
)


def test_checker_module_keeps_its_reexport_and_patch_seams():
    from scripts.function_tracer_pcode.checker import checker as checker_module

    missing = [
        name
        for name in CHECKER_REEXPORTS + CHECKER_TEST_SEAMS
        if not hasattr(checker_module, name)
    ]
    assert missing == [], (
        "checker.checker lost a name that callers or tests reach through this "
        "module path (Issue #51 keeps these): " + ", ".join(missing)
    )
