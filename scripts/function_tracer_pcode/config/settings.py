# -*- coding: utf-8 -*-
"""設定ファイル"""

import importlib
import os
import site
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, MutableMapping, Optional

# Ghidra内で実行されているかどうかを検出
try:
    from ghidra.program.model.listing import Program  # noqa: F401  (import probe: succeeds only inside Ghidra)
    IN_GHIDRA = True
except ImportError:
    IN_GHIDRA = False

@dataclass(frozen=True)
class RuntimeEnvironment:
    """Runtime dependency paths used by the PyGhidra entrypoints."""

    ghidra_install_dir: Optional[str]
    java_home: Optional[str]


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _is_ghidra_install_dir(path: Path) -> bool:
    return path.is_dir() and (path / "ghidraRun").exists() and (path / "support").is_dir()


def _is_java_home(path: Path) -> bool:
    java_names = ("java.exe", "java") if os.name == "nt" else ("java", "java.exe")
    return path.is_dir() and any((path / "bin" / java_name).exists() for java_name in java_names)


def _iter_ghidra_install_candidates(repo_root: Path):
    yield repo_root / ".local-ghidra"

    extracted_root = repo_root / ".local-ghidra-extract"
    if extracted_root.is_dir():
        for child in sorted(extracted_root.iterdir()):
            yield child

    for child in sorted(repo_root.glob("ghidra_*_PUBLIC")):
        yield child

    yield Path("/opt/ghidra")


def _discover_ghidra_install_dir(repo_root: Path) -> Optional[str]:
    for candidate in _iter_ghidra_install_candidates(repo_root):
        if _is_ghidra_install_dir(candidate):
            return str(candidate)
    return None


def _discover_java_home(repo_root: Path) -> Optional[str]:
    candidates = [
        repo_root / ".local-jdk",
        Path("/usr/lib/jvm/default-java"),
        Path("/usr/lib/jvm/java-17-openjdk-amd64"),
        Path("/usr/lib/jvm/java-21-openjdk-amd64"),
    ]
    for candidate in candidates:
        if _is_java_home(candidate):
            return str(candidate)
    return None


def _discover_optional_python_paths(repo_root: Path) -> list[str]:
    candidates: list[str] = []
    seen = set()

    def add_candidate(path: Optional[Path]) -> None:
        if path is None:
            return
        resolved = path.expanduser()
        if not resolved.is_dir():
            return
        if not (resolved / "z3").exists():
            return
        value = str(resolved)
        if value in seen:
            return
        seen.add(value)
        candidates.append(value)

    try:
        add_candidate(Path(site.getusersitepackages()))
    except Exception:
        pass
    add_candidate(Path.home() / f".local/lib/python{sys.version_info.major}.{sys.version_info.minor}/site-packages")
    add_candidate(
        repo_root
        / ".venv-pyghidra"
        / "lib"
        / f"python{sys.version_info.major}.{sys.version_info.minor}"
        / "site-packages"
    )
    return candidates


def discover_runtime_environment(
    repo_root: Optional[Path] = None,
    environ: Optional[Mapping[str, str]] = None,
) -> RuntimeEnvironment:
    """Resolve Ghidra/JDK locations, preferring explicit env vars and repo-local assets."""

    effective_env = environ if environ is not None else os.environ
    base_dir = repo_root if repo_root is not None else _repo_root()

    ghidra_install_dir = effective_env.get("GHIDRA_INSTALL_DIR") or _discover_ghidra_install_dir(base_dir)
    java_home = effective_env.get("JAVA_HOME") or _discover_java_home(base_dir)

    return RuntimeEnvironment(
        ghidra_install_dir=ghidra_install_dir,
        java_home=java_home,
    )


def apply_runtime_environment(
    runtime_env: Optional[RuntimeEnvironment] = None,
    environ: Optional[MutableMapping[str, str]] = None,
) -> RuntimeEnvironment:
    """Backfill runtime env vars for local PyGhidra execution without overriding explicit values."""

    target_env = environ if environ is not None else os.environ
    resolved_env = runtime_env if runtime_env is not None else discover_runtime_environment(environ=target_env)

    if resolved_env.ghidra_install_dir and "GHIDRA_INSTALL_DIR" not in target_env:
        target_env["GHIDRA_INSTALL_DIR"] = resolved_env.ghidra_install_dir
    if resolved_env.java_home and "JAVA_HOME" not in target_env:
        target_env["JAVA_HOME"] = resolved_env.java_home
    if resolved_env.java_home and "JAVA_HOME_OVERRIDE" not in target_env:
        target_env["JAVA_HOME_OVERRIDE"] = resolved_env.java_home
    if resolved_env.java_home:
        java_bin = str(Path(resolved_env.java_home) / "bin")
        current_path = target_env.get("PATH", "")
        path_entries = current_path.split(os.pathsep) if current_path else []
        if java_bin not in path_entries:
            target_env["PATH"] = os.pathsep.join([java_bin, *path_entries]) if path_entries else java_bin

    pythonpath_entries = (
        target_env.get("PYTHONPATH", "").split(os.pathsep)
        if target_env.get("PYTHONPATH")
        else []
    )
    updated_pythonpath = list(pythonpath_entries)
    for candidate in _discover_optional_python_paths(_repo_root()):
        if candidate not in updated_pythonpath:
            updated_pythonpath.append(candidate)
        if candidate not in sys.path:
            sys.path.append(candidate)
    if updated_pythonpath:
        target_env["PYTHONPATH"] = os.pathsep.join(updated_pythonpath)
    for module_name in ("z3",):
        try:
            importlib.import_module(module_name)
        except Exception:
            pass

    return resolved_env


_RUNTIME_ENV = discover_runtime_environment()

# PyGhidra用設定
GHIDRA_INSTALL_DIR = _RUNTIME_ENV.ghidra_install_dir
JAVA_HOME = _RUNTIME_ENV.java_home

# デフォルトの解析対象関数
TARGET_FUNCTIONS = ["add", "subtract", "multiply", "divide", "modulo", "combined_arithmetic"]
# TARGET_FUNCTIONS = ["bitwise_and", "bitwise_or", "bitwise_xor", "bitwise_not", "left_shift", "right_shift_logical", "right_shift_arithmetic", "xor_shift", "extract_bits", "flip_bits"]

# デフォルトの出力ファイル
OUTPUT_FILE = os.environ.get(
    "FUNCTION_TRACER_OUTPUT_FILE",
    str(_repo_root() / "output" / "cate2_branch_return_trace_output.txt"),
)

# 出力形式: "text", "json", "smt", "detailed"
OUTPUT_FORMAT = "text"

# トレースの最大深度（無限ループ防止）
MAX_TRACE_DEPTH = 100

# デバッグモード
DEBUG_MODE = False  # Trueにするとデバッグ出力が有効になる

# 等価性判定戦略: "monolithic" (単一の大きなite式) or "pairwise" (分岐ペア分割)
EQUIVALENCE_CHECK_STRATEGY = "pairwise"

# Pairwise戦略の各クエリのタイムアウト（秒）
PAIRWISE_PER_QUERY_TIMEOUT = 5

# Pairwise戦略の難しいクエリの再試行タイムアウト（秒）
PAIRWISE_PER_QUERY_TIMEOUT_HARD = 30

# UNKNOWNクエリを保存するか
PAIRWISE_SAVE_UNKNOWN_QUERIES = False

# Bounded fallback: unresolved call summary unfolding
BOUNDED_CALL_REFINEMENT_ENABLED = True
BOUNDED_CALL_UNROLL_LIMIT = 2
BOUNDED_CALL_MAX_CASES = 128

# Expander safeguards for optimized loop/recur cases
EXPANDER_MAX_OPERATION_CASES = 64
EXPANDER_MAX_COMBINATION_ATTEMPTS = 512


def _positive_int_setting(name: str, default: int, environ=None) -> int:
    """正の整数設定を環境変数から読む（不正値は既定へ戻す）。

    0 や負値をそのまま slice 上限に使うと「全件破棄」「制限解除」といった意図しない
    挙動になるため、正の整数以外は採用しない。
    """

    source = environ if environ is not None else os.environ
    raw = source.get(name)
    if raw is None or str(raw).strip() == "":
        return int(default)
    try:
        value = int(str(raw).strip(), 10)
    except (TypeError, ValueError):
        return int(default)
    if value < 1:
        return int(default)
    return value


def _bool_setting(name: str, default: bool, environ=None) -> bool:
    """真偽設定を環境変数から読む（``1``/``0`` のみ受け付け、他は既定へ戻す）。

    解析の意味を変えない run 単位の切り替え用。曖昧な綴りを推測で解釈すると
    「有効にしたつもりで無効」が起きるので、認識できない値は既定値を使う。
    """

    source = environ if environ is not None else os.environ
    raw = source.get(name)
    if raw is None:
        return bool(default)
    text = str(raw).strip().lower()
    if text in {"1", "true", "yes", "on"}:
        return True
    if text in {"0", "false", "no", "off"}:
        return False
    return bool(default)


# Issue #47 (PR-B): bound が semantic analysis を変えないと静的に確認できる external
# placeholder callee について、束縛ゼロ scope の解析を再利用するか。
CALLEE_UNBOUND_REUSE_ENABLED = _bool_setting("FT_CALLEE_UNBOUND_REUSE", True)

# 再利用した解析と従来の bound-sensitive 解析を両方走らせて比較する regression
# validation（shadow）。既定は無効。有効にすると再利用による削減は起きない。
CALLEE_UNBOUND_REUSE_SHADOW = _bool_setting("FT_CALLEE_UNBOUND_REUSE_SHADOW", False)


# Issue #107 (PR-B): 型仮説を適用した retry phase の「変更側 fresh 再解析」を、P0 の raw
# 解析 snapshot の複製 + 累積仮説の replay で置き換えるか。無効にすると base snapshot の
# 作成も含めて再利用機構を一切動かさず、従来どおり毎回 ``analyze_function_by_name()`` を
# やり直す（kill switch）。設定が読めない場合も無効側に倒す。
RETRY_ANALYSIS_REUSE_ENABLED = _bool_setting("FT_RETRY_ANALYSIS_REUSE", True)

# 再利用ビューと従来の fresh 再解析を両方構成して semantic fingerprint を比較する
# shadow validation。**既定は有効**で、fresh 側を authoritative にするため再利用による
# 削減は起きない。無効にすると再利用のみを構成する（reuse mode）。
#
# **reuse mode はまだ検証を通っていない。既定を無効側へ倒さないこと。**
# 固定 subset を reuse mode で流すと、outcome は不変だが `dart/test` の 3 pair で
# 最終 UNKNOWN reason 集合から `outcome_same_kind_consistency_unproven` が消える。
# 原因は、比較に使う `AnalysisSnapshot.from_function_analysis()` が
# `to_dict()` → `parameters_without_runtime_objects()` を通るため
# `data_type_obj` を落とすのに対し、P4-A の適用判定
# (`checker/arch/mips64.py` の `_get_param_type_string` / `_get_param_size`) は
# その `data_type_obj` を先に読むこと。semantic fingerprint が一致していても
# phase の適用可否が変わり得るので、この指紋だけでは reuse の等価性を保証できない。
RETRY_ANALYSIS_REUSE_SHADOW = _bool_setting("FT_RETRY_ANALYSIS_REUSE_SHADOW", True)


# 共通 dedup のケース数上限（Issue #131）。既定値は従来の
# ``ExpressionExpander.MAX_CASES_PER_MULTIEQUAL`` と同じ 16。調査用に下げられるが、
# 通常実行の既定値は変えない。明示 limit を渡す呼び出し
# （``EXPANDER_MAX_OPERATION_CASES``）はこの設定の対象外。
EXPANDER_DEDUP_CASE_LIMIT = _positive_int_setting("FT_EXPANDER_DEDUP_CASE_LIMIT", 16)
