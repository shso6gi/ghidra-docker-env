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


# 共通 dedup のケース数上限（Issue #131）。既定値は従来の
# ``ExpressionExpander.MAX_CASES_PER_MULTIEQUAL`` と同じ 16。調査用に下げられるが、
# 通常実行の既定値は変えない。明示 limit を渡す呼び出し
# （``EXPANDER_MAX_OPERATION_CASES``）はこの設定の対象外。
EXPANDER_DEDUP_CASE_LIMIT = _positive_int_setting("FT_EXPANDER_DEDUP_CASE_LIMIT", 16)


# ---------------------------------------------------------------------------
# 式の大きさの予算（Issue #22 PR-22-D）
# ---------------------------------------------------------------------------
#
# **既定値の唯一の置き場**。値を変えるときに触るのはこの表と policy test だけで、
# 数える側（expander / renderer / 出力の準備）も authority も変わらない
# （`core/budget_policy.BudgetPolicy` が typed な値を運ぶ。深い module は環境変数も
# この module も読まない）。値の根拠（U-1 の実測）は PR-22-D の本文に残す。
#
# 環境変数で個別に上書きできる。正の整数はその値、`off` / `none` / `unlimited` /
# `0` はその予算だけ無効（制限しない）、それ以外（空・不正値）は既定値。runner は
# これらを渡さない（run 単位の調査用）。無効にしても出力の準備は authority の契約の上限
# （結果の preimage、`checker/output_preparation.output_contract_policy`）を超えない。

#: (BudgetPolicy の field 名, 環境変数, 既定値)。既定値 `None` は無制限。
#:
#: 値の根拠（U-1、PR-22-D 時点の実測。固定 subset 144 pair・recorded corpus・
#: `ell/ellProgram` B12_B16 の 11 関数・subset の TIMEOUT 5 pair を予算無しで流し、
#: kill された pair は stage journal の観測値を読んだ）:
#:
#: * 観測した最大値はどれも小さい — 展開の distinct node < 2048
#:   （`ellProgram/snippet`。EQ / NOT_EQ に届いた pair では最大 84）、展開 case
#:   < 32、solver へ渡す描画 14,485 B、木表現 545 KB、結果 JSON 2.45 MB
#:   （うち authority 確定後の field + 診断 2.39 MB、準備した payload 277 KB）、
#:   snapshot 1 つ分の木表現 836 KB / distinct node 438。
#: * kill された 12 pair はすべて条件簡約（CNF / 構造比較 / oracle）か solver の
#:   区間にいて、式の大きさで止まっていない（#105 / #106 の担当）。
#:
#: したがって予算は「指数的な膨張に対する安全上限」で、TIMEOUT を狙って値を
#: 下げない（下げても正しい判定を削るだけで、時間の原因には届かない）。既定値は
#: 観測の最大値に対して 8〜290 倍の余裕を取った 2 の冪。`serialization_nodes` は
#: `expression_nodes` 以上にしてある（展開の予算が許した式は直列化できる）。
#: 値を変えるときはこの表だけを変え、根拠の実測を PR に残す。
EXPRESSION_BUDGET_DEFAULTS = (
    ("expression_nodes", "FT_EXPRESSION_NODE_BUDGET", 1 << 14),       # 16,384
    ("expansion_cases", "FT_EXPANSION_CASE_BUDGET", 1 << 10),         # 1,024
    ("render_bytes", "FT_RENDER_BYTES_BUDGET", 1 << 22),              # 4 MiB
    ("serialization_bytes", "FT_SERIALIZATION_BYTES_BUDGET", 1 << 26),  # 64 MiB
    ("serialization_nodes", "FT_SERIALIZATION_NODE_BUDGET", 1 << 16),  # 65,536
    ("envelope_headroom_bytes", "FT_ENVELOPE_HEADROOM_BYTES", 1 << 25),  # 32 MiB
    # Issue #105 PR-105-B: 条件簡約の fallback の予算（超えても限界・UNKNOWN の reason に
    # しない。その問いに答えない = 元の条件を残す / oracle 無し）。値の根拠（PR-105-A merge 後の
    # main で固定 subset 144 pair（Eq 64 + Neq 80）+ `ell/ellProgram` B12_B16 を予算無しで流した分布）:
    #
    # * DPLL の決定（最上位の判定 1 回あたり）: max 2・p99 1（subset）、ellpi 3、kill された
    #   ell snippet の下限 4。時間の掛かる pair はどれも決定回数では止まっていない（kill 位置は
    #   identity の構築・描画・凍結）ので、値は指数的な分岐に対する安全上限: 観測の最大の 16 倍。
    # * 条件 oracle の query（pair あたり、solver へ発行した数）: median 22・p90 246・p99 660・
    #   max 886（正しい EQ の pair）。TIMEOUT の ell CheckCond は 4096 以上。正しい pair の最大の
    #   約 4.6 倍の 2 の冪。
    #
    # どちらも既定値で固定 subset・recorded corpus の予算の fallback は 0 件（PR 本文の表）。
    # 値を変えるときはこの表だけを変え、根拠の実測を PR に残す。
    ("dpll_decisions", "FT_CNF_DPLL_DECISION_BUDGET", 1 << 6),       # 64
    ("oracle_queries", "FT_CONDITION_ORACLE_QUERY_BUDGET", 1 << 12),  # 4,096
)

_BUDGET_OFF_WORDS = frozenset({"off", "none", "unlimited", "0"})


def _budget_setting(name: str, default: Optional[int], environ=None) -> Optional[int]:
    """予算 1 つを環境変数から読む（`off` 系は無効、読めない値・1 未満の値は既定値）。

    値 1 つずつの誤りは既定値へ戻す。値どうしの組み合わせの誤りは `expression_budget_policy` が
    起動時に止める（下）。
    """

    source = environ if environ is not None else os.environ
    raw = source.get(name)
    if raw is None or str(raw).strip() == "":
        return default
    text = str(raw).strip().lower()
    if text in _BUDGET_OFF_WORDS:
        return None
    try:
        value = int(text, 10)
    except ValueError:
        return default
    return value if value >= 1 else default


def expression_budget_policy(environ: Optional[Mapping[str, str]] = None):
    """既定値と環境変数から、pair に適用する `BudgetPolicy` を組み立てる。

    値どうしの組み合わせの誤り（`FT_SERIALIZATION_BYTES_BUDGET` が `FT_ENVELOPE_HEADROOM_BYTES`
    以下、など）は既定値へ黙って戻さず、どの環境変数かを示す `ValueError` で起動時に止める（どちらを
    直すべきかは設定した人にしか分からない。pair を 1 つも走らせない fail-fast）。headroom の `off`
    は 0 で、直列化の予算が有限なら出力 schema の最小値を満たさない（`EquivalenceChecker` の構築で
    `EnvelopeHeadroomTooSmall`）。
    """

    from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy

    values = {}
    for field_name, env_name, default in EXPRESSION_BUDGET_DEFAULTS:
        value = _budget_setting(env_name, default, environ)
        if field_name == "envelope_headroom_bytes":
            value = 0 if value is None else value
        values[field_name] = value
    try:
        return BudgetPolicy(**values)
    except ValueError as exc:
        names = ", ".join(f"{env_name}={values[field_name]}" for field_name, env_name, _ in EXPRESSION_BUDGET_DEFAULTS)
        raise ValueError(f"inconsistent expression budget settings ({names}): {exc}") from exc
