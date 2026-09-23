# -*- coding: utf-8 -*-
"""layer test では表せない module 単位の境界（計画 §4.8）。

`test_import_layers.py` が層どうしの向き（`core < ... < cli`）を固定するのに
対して、ここは **同じ層の中で責務 owner を分けたことが崩れていないか** を見る。
どちらも AST の import / 参照を読むだけで、新しい lint 機構は作らない。

PR-22-B が置く境界:

* **生 object を読むのは投影側の 2 module だけ** — `core/semantic_projection.py`
  （`semantic_key()` / `stable_key()` / `storage_identity_key()` / 宣言型）と
  `core/loop_lowering_semantics.py`（loop summary ref の schema）。意味 consumer
  （structural identity / renderer / solver query / loop lowering の描画）は
  どちらの生 object も自分で読まない。読むと、同じ問いに複数の答えが生まれ、
  凍結後に意味が動く。
* 意味の表現（`core/semantic_snapshot.py`）は生 object の読み方を知らない
  （projection owner への一方向）。authority / CLI / checker / config / env も、
  失敗の台帳（`record_internal_bug` 等）も読まない。
* `core/runtime_refs/` の ref は **frozen な value object**。凍結後の consumer が
  ref の構造を辿ってよいのは、これが型で保証されているから。
* 閉路の判定は 1 実装（`traverse_semantic_graph`）。identity API ごとに書かない。
* **公開（producer の宣言）を成立させられるのは公開境界だけ**。identity /
  表現 / 投影 / renderer は検証（`validated`）までしか進められない。1 bit で
  兼ねていると、candidate hash を 1 回取っただけで solver へ渡せる値になる。
* **lifecycle state を進めるのは commit だけ**。`mark_validated` /
  `mark_published` を staging の途中で呼ぶと、失敗した closure の root だけが
  「成功した」状態で残る（partial commit）。再入防止に public state を流用
  しないことも同じ理由で要る。
* **複製・派生は公開の権限を持たない**。lifecycle state を持つ型は `__copy__` /
  `__deepcopy__` を自分で定義して、状態と派生値を落とす（既定の複製は `__dict__`
  を写すので、公開済みを名乗る外側の下に未公開の中身がぶら下がる）。「何を
  引き継がないか」は `core/semantic_lifecycle.py` が 1 箇所で決める。
* **loop lowering の意味は `core/loop_lowering_semantics.py` が所有**。SMT
  renderer は loop summary ref の schema（class も field 名も）を知らず、
  凍結済みの `LoopLoweringSemantics` だけを読む。厳密 lowering の可否は健全性
  に直結するので、判断が renderer 側の `getattr` 既定値に散るとまずい。
* candidate hash で「一致」を決めてよいのは structural identity の owner だけ。
  他所で `structural_hash() == ...` を等価判定に使うと、衝突がそのまま誤判定に
  なる。

後続 PR（budget policy / solver backend / output envelope）が足す境界も、
ここの表に 1 行足して表現する。
"""

from __future__ import annotations

import ast
import enum
import pathlib
from typing import Dict, Iterable, List, Tuple

import pytest


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
PACKAGE_PREFIX = "scripts.function_tracer_pcode."

#: module（package からの相対 path）→ import してはいけない module 接頭辞。
_BANNED_IMPORTS: Dict[str, Tuple[str, ...]] = {
    "core/semantic_projection.py": (
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        # 表現にも identity にも依存しない: 投影は「生 object の読み方」だけを
        # 知っていればよく、読んだ値が何に使われるかは知らない。
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.expression",
        "os",
    ),
    "core/semantic_snapshot.py": (
        # 責務の逆転（表現が identity の private helper を借りる）を禁じる。
        "scripts.function_tracer_pcode.core.structural",
        # 描画（共有方針・束縛名・出力量）を変えても表現は動かない。
        "scripts.function_tracer_pcode.core.render_plan",
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.render_python",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "os",
    ),
    "core/semantic_lifecycle.py": (
        # 状態の定義は何にも依存しない（式も条件も知らない duck typing）。
        "scripts.function_tracer_pcode.core.expression",
        "scripts.function_tracer_pcode.core.condition",
        "scripts.function_tracer_pcode.core.semantic_freeze",
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.semantic_projection",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.analysis",
        "scripts.function_tracer_pcode.semantics",
        "scripts.function_tracer_pcode.proof",
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
        # 描画規則を変えても構造 identity は動かない（`to_string()` を key に
        # しないという契約を import の向きでも固定する）。
        "scripts.function_tracer_pcode.core.render_plan",
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.render_python",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "os",
    ),
    "core/render_smt/loop_lowering.py": (
        # ref の class を知らない = どの lowering かを renderer が判定しない。
        "scripts.function_tracer_pcode.core.runtime_refs",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "os",
    ),
    # --- PR-22-C: 描画層の責務分割 ---------------------------------------
    "core/render_plan.py": (
        # 走査と共有計画は「何を描くか」を知らない（人向けにも SMT にも使う）。
        # 式の型を知り始めると、node 種別が増えるたびにここも触ることになる。
        "scripts.function_tracer_pcode.core.expression",
        "scripts.function_tracer_pcode.core.condition",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.render_python",
        "scripts.function_tracer_pcode.analysis",
        "scripts.function_tracer_pcode.semantics",
        "scripts.function_tracer_pcode.proof",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "os",
    ),
    "core/render_output.py": (
        # 出力口と counter は描画規則も式の型も知らない。
        "scripts.function_tracer_pcode.core.expression",
        "scripts.function_tracer_pcode.core.condition",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.render_plan",
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.render_python",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "os",
    ),
    "core/render_metrics.py": (
        "scripts.function_tracer_pcode.core.expression",
        "scripts.function_tracer_pcode.core.condition",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.render_python",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "os",
    ),
    "core/render_smt/context.py": (
        # 描画文脈は identity でも表現でもない（共有可否だけを決める）。
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.render_smt.render",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "os",
    ),
    "core/render_smt/bindings.py": (
        # 名前空間 owner は式の型も identity も知らない。描画 text だけを見る。
        "scripts.function_tracer_pcode.core.expression",
        "scripts.function_tracer_pcode.core.condition",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.render_smt.render",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "os",
    ),
    "core/render_python.py": (
        # 人向け表示を変えても SMT 側は動かない（逆向きも同じ）。
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "os",
    ),
    "core/loop_lowering_semantics.py": (
        # 意味の owner は描画も identity も知らない（投影 owner から呼ばれる側）。
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.semantic_snapshot",
        "scripts.function_tracer_pcode.core.semantic_projection",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
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
_LEDGER_FREE_MODULES = (
    "core/semantic_snapshot.py",
    "core/semantic_projection.py",
    "core/structural.py",
    # 描画層も失敗の記録は持たない（限界の記録先は呼び出し側の境界）。
    "core/render_plan.py",
    "core/render_output.py",
    "core/render_metrics.py",
    "core/render_python.py",
)

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

#: 凍結済みの式から読み直してはいけない可変な生 object。
_RAW_SEMANTIC_ATTRIBUTES = frozenset({"data_type_obj", "storage_info"})

#: 生 object から identity を作る method。**projection owner だけ**が呼ぶ。
_RAW_IDENTITY_CALLS = frozenset(
    {"semantic_key", "stable_key", "storage_identity_key", "global_object_identity"}
)
_RAW_PROJECTION_OWNER = "core/semantic_projection.py"

#: 閉路を「受理しない」と決めてよい唯一の module（走査そのものを持つ側）。
_CYCLE_JUDGEMENT_OWNER = "core/semantic_snapshot.py"

#: producer の宣言（PUBLISHED）を成立させてよい唯一の module。
_PUBLICATION_OWNER = "core/semantic_freeze.py"
#: 公開を成立させる名前。呼ぶ / import するだけで公開権限を持つことになる。
_PUBLICATION_NAMES = frozenset(
    {
        "publish",
        "publish_expression",
        "publish_condition",
        "publish_semantic_values",
        "mark_published",
    }
)
#: 凍結済みの意味を読む側 + 状態を定義する側。ここが公開を成立させてはいけない。
#: 公開を成立させてはいけない module。`core/condition.py` が入っていないのは
#: 意図的で、`Condition.negate()` だけが宣言を引き継ぐ唯一の派生
#: （式 object をそのまま持つので closure が壊れない）。値の型そのものが公開
#: できないことは `core/expression.py` の側で固定する。
_PUBLICATION_FREE_MODULES = (
    "core/expression.py",
    "core/structural.py",
    "core/semantic_snapshot.py",
    "core/semantic_projection.py",
    "core/semantic_lifecycle.py",
    "core/loop_lowering_semantics.py",
    "core/render_smt/render.py",
    "core/render_smt/widths.py",
    "core/render_smt/unknowns.py",
    "core/render_smt/loop_lowering.py",
    "core/render_smt/intrinsics.py",
    "core/render_smt/bindings.py",
    "core/render_smt/context.py",
    "core/render_smt/attributes.py",
    "core/render_plan.py",
    "core/render_python.py",
)

#: loop lowering の意味を決めてよい唯一の module。
_LOWERING_SEMANTICS_OWNER = "core/loop_lowering_semantics.py"
#: loop summary ref **だけ**が持つ生 field 名。renderer がこれらを名指しで読むと、
#: schema が変わったとき既定値に落ちて厳密 lowering の可否が黙って変わる。
#: `induction_step` などは投影（`LoopLoweringSemantics`）にも同じ名前であり、
#: そちらを読むのは正しいので、ここには入れない（下の assert で照合する）。
_RAW_LOWERING_FIELDS = frozenset(
    {
        "side_effect_profile",
        "transition_cases",
        "transition_expr",
        "state_placeholder",
        "step_expr",
        "loop_summary",
        "requires_effect_proof",
        "requires_path_proof",
        "effect_descriptors",
        "context_descriptors",
    }
)
#: 生 ref そのものを読んではいけない module（凍結後の描画側）。
_RUNTIME_REF_FREE_MODULES = ("core/render_smt/loop_lowering.py",)

#: 描画テキストを **文字列として見て**よい唯一の関数。
#:
#: 子の描画結果は参照 1 個（`RenderedTerm`）なので、その文字を見て分岐すると、
#: 参照が名前になった / 展開されたで判定が変わる。判定に要る性質は型付きの
#: property（`SmtTermProperties`）で運び、text を見るのは「その node 自身の
#: fragment を 1 回だけ分類する」この関数だけにする。
_TEXT_INSPECTION_OWNER = ("core/render_smt/float_theory.py", "_looks_like_fp_expr")
#: 分類器（唯一の呼び出し元）。fragment を見てよいのはこの 2 つだけ。
_FRAGMENT_CLASSIFIER = ("core/render_smt/render.py", "classify_smt_fragment")
_FRAGMENT_READERS = frozenset({_TEXT_INSPECTION_OWNER, _FRAGMENT_CLASSIFIER})
#: 描画テキストを保持していそうな名前。ここに挙げた名前に対する文字列検査と
#: 文字列リテラルとの比較を、body module では 0 件で固定する。
_RENDERED_TEXT_NAMES = (
    "_smt",
    "_str",
    "_text",
    "fragment",
)
_TEXT_INSPECTION_METHODS = frozenset(
    {"startswith", "endswith", "strip", "lstrip", "rstrip", "split", "replace", "find", "index", "count"}
)
#: node 本体を持つ描画 module（ここでの text 検査だけを見る）。
_RENDER_BODY_MODULES = (
    "core/render_smt/render.py",
    "core/render_smt/widths.py",
    "core/render_smt/float_theory.py",
    "core/render_smt/intrinsics.py",
    "core/render_smt/loop_lowering.py",
    "core/render_smt/unknowns.py",
    "core/render_python.py",
)
#: 表示文字列を identity にしてはいけない（書式を変えると判定が動く）。
_RENDERED_TEXT_CALLS = frozenset({"to_string"})

#: 凍結後に意味を読む consumer。ここが生 object を読むと、同じ式の意味が
#: 「いつ読んだか」で変わり得る。
_SNAPSHOT_ONLY_MODULES = (
    "core/structural.py",
    "core/semantic_snapshot.py",
    "core/render_python.py",
    "core/render_smt/attributes.py",
    "core/render_smt/render.py",
    "core/render_smt/widths.py",
    "core/render_smt/unknowns.py",
    "core/render_smt/loop_lowering.py",
    "analysis/condition/smt_oracle.py",
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
    """凍結後に意味を読む consumer は、可変な生 object を読み直さない。

    生の `data_type_obj`（JVM object）や `StorageInfo`（可変 dataclass）をここで
    読み直すと、凍結後にその object が変わったときに幅や宣言だけが黙って変わって
    しまう。

    対象は「凍結済みの意味を読む側」に限る。解析中に Ghidra から descriptor を
    組み立てる層（`analysis/tracer_*` 等）は、まさに生 object を読むのが仕事
    なのでここには入らない — 境界は「構築か消費か」であって「core かどうか」
    ではない。
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


@pytest.mark.parametrize("module_path", _SNAPSHOT_ONLY_MODULES)
def test_semantic_consumers_do_not_build_identity_from_raw_objects(module_path):
    """identity を生 object から作ってよいのは projection owner だけ。

    `semantic_key()` を 4 箇所で別々に呼んでいた頃は、`except` の範囲すら
    3 通りに分かれていた。答えが 1 つになるよう、呼ぶ場所を 1 つにする。
    """

    path = PACKAGE_ROOT / module_path
    offenders = []
    for node in ast.walk(_parse(path)):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Attribute) and func.attr in _RAW_IDENTITY_CALLS:
            offenders.append(f"{module_path}:{node.lineno} calls .{func.attr}()")
    assert offenders == [], offenders


def test_runtime_refs_are_immutable_value_objects():
    """凍結後の consumer が ref の構造を辿ってよい根拠を型で固定する。

    ref が可変だと「凍結済みの式の意味」が ref 経由で動いてしまう。ここが
    崩れたら、consumer 側の読み方ではなく ref の定義を直すのが正しい。
    """

    import dataclasses
    import enum
    import importlib
    import inspect

    #: ref ではないもの（例外・収集器）は対象外。
    allowed_mutable = {"MissingSideDiscriminator", "ExpansionBudgetCollector"}
    offenders = []
    package = PACKAGE_ROOT / "core" / "runtime_refs"
    for path in sorted(package.glob("*.py")):
        module_name = (
            "scripts.function_tracer_pcode.core.runtime_refs."
            + path.stem
        )
        module = importlib.import_module(module_name)
        for name, obj in vars(module).items():
            if not inspect.isclass(obj) or obj.__module__ != module_name:
                continue
            if name in allowed_mutable:
                continue
            if issubclass(obj, BaseException) or issubclass(obj, enum.Enum):
                continue
            if issubclass(obj, tuple):  # NamedTuple
                continue
            if dataclasses.is_dataclass(obj):
                if not obj.__dataclass_params__.frozen:
                    offenders.append(f"{module_name}.{name} is a mutable dataclass")
                continue
            offenders.append(f"{module_name}.{name} is neither frozen nor a value type")
    assert offenders == [], offenders


def test_cycle_detection_has_a_single_implementation():
    """閉路の判定は 1 箇所。

    API ごとに書くと、辺の判定順を 1 行間違えた実装だけが残る（実際それで
    back-edge を取り逃していた）。走査は `traverse_semantic_graph` 1 本で、
    ほかの module は例外型を捕まえる / 通すだけ。
    """

    raising: List[str] = []
    for path in _module_files():
        for node in ast.walk(_parse(path)):
            if not isinstance(node, ast.Raise) or node.exc is None:
                continue
            exc = node.exc
            name = exc.func if isinstance(exc, ast.Call) else exc
            if isinstance(name, ast.Name) and name.id == "ExpressionCycleError":
                raising.append(_relative(path))
    assert raising == [_CYCLE_JUDGEMENT_OWNER], raising


def test_identity_kinds_are_not_merged_into_one_type():
    """structural identity を万能 identity にしない。

    同じ式でも solver 宣言や rewrite 文脈が違えば別物なので、片方の都合で
    他方の一致条件を動かせる形（1 つの class が全部を返す）にはしない。
    """

    from scripts.function_tracer_pcode.core import structural

    identity = structural.StructuralIdentity
    exposed = {name for name in vars(identity) if not name.startswith("_")}
    # 構造 identity の面だけ。solver query / rewrite の一致条件はここに入れない。
    # **PR-22-B が公開した 4 つのまま**: identity 型は PR-22-C の must-not-change
    # なので、renderer の PR が facade を広げない。
    assert exposed == {
        "candidate_hash",
        "equals",
        "key",
        "identity_digest",
    }, exposed
    for forbidden in ("solver_query", "rewrite", "authority_digest", "query_identity"):
        assert not hasattr(identity, forbidden), forbidden


@pytest.mark.parametrize("module_path", _RUNTIME_REF_FREE_MODULES)
def test_the_lowering_renderer_does_not_read_the_raw_runtime_ref(module_path):
    """描画側は `expr.runtime_ref` を読まない。

    読むと「どの lowering か」の答えが描画のたびに作り直され、ref の schema が
    変わったときに renderer だけが古い読み方で残る。種別の判定は凍結時に
    `core/loop_lowering_semantics.py` が 1 回だけ下す。
    """

    path = PACKAGE_ROOT / module_path
    offenders = []
    for node in ast.walk(_parse(path)):
        if isinstance(node, ast.Attribute) and node.attr == "runtime_ref":
            offenders.append(f"{module_path}:{node.lineno} reads .runtime_ref")
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "getattr"
            and len(node.args) >= 2
            and isinstance(node.args[1], ast.Constant)
            and node.args[1].value == "runtime_ref"
        ):
            offenders.append(f"{module_path}:{node.lineno} reads 'runtime_ref'")
    assert offenders == [], offenders


@pytest.mark.parametrize("module_path", _RUNTIME_REF_FREE_MODULES)
def test_exact_lowering_is_not_decided_from_raw_summary_fields(module_path):
    """厳密 lowering の可否を、renderer が生 field から組み立て直さない。

    厳密 lowering は「未解釈関数ではなく閉じた式で表してよい」という健全性の
    判断なので、`getattr(ref, "induction_step", 0)` のような既定値付きの読み方が
    描画側に散ると、schema の変化が黙って判断を変えてしまう。
    """

    path = PACKAGE_ROOT / module_path
    offenders = []
    for node in ast.walk(_parse(path)):
        if isinstance(node, ast.Attribute) and node.attr in _RAW_LOWERING_FIELDS:
            offenders.append(f"{module_path}:{node.lineno} reads .{node.attr}")
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "getattr"
            and len(node.args) >= 2
            and isinstance(node.args[1], ast.Constant)
            and node.args[1].value in _RAW_LOWERING_FIELDS
        ):
            offenders.append(f"{module_path}:{node.lineno} reads {node.args[1].value!r}")
    assert offenders == [], offenders


def test_the_raw_lowering_field_names_are_not_projection_field_names():
    """生 field 名の表が、投影 field 名と衝突していないこと。

    衝突していると「投影を読んでいるだけ」の行まで違反に数えてしまい、
    上の 2 つの guard が意味を失う。
    """

    import dataclasses

    from scripts.function_tracer_pcode.core import loop_lowering_semantics as owner

    projection_fields = {
        field.name for field in dataclasses.fields(owner.LoopLoweringSemantics)
    }
    assert _RAW_LOWERING_FIELDS.isdisjoint(projection_fields), (
        _RAW_LOWERING_FIELDS & projection_fields
    )


def test_the_lowering_semantics_are_an_immutable_value():
    """lowering の意味は凍結された値。consumer が書き換えられない。"""

    import dataclasses

    from scripts.function_tracer_pcode.core import loop_lowering_semantics as owner

    assert dataclasses.is_dataclass(owner.LoopLoweringSemantics)
    assert owner.LoopLoweringSemantics.__dataclass_params__.frozen
    # 種別は列挙で閉じる（文字列比較が各所に散らないように）。
    assert issubclass(owner.LoweringKind, enum.Enum)
    kinds = {member.name for member in owner.LoweringKind}
    assert "NONE" in kinds and len(kinds) >= 5, kinds


def test_only_the_lowering_owner_classifies_loop_summary_refs():
    """どの loop summary ref がどの lowering かを決めるのは owner だけ。

    `isinstance(ref, CountedLoopSummaryRef)` が消費側にも増えると、新しい ref
    種別を足したときに片方だけ更新されて、もう片方が黙って未解釈関数へ落ちる。

    対象は「凍結済みの意味を読む側」。ref を **作る** 側（`analysis` の
    summarizer 等）が自分の作った ref を種別で扱うのは構築であって消費ではない。
    """

    ref_names = {
        "CountedLoopSummaryRef",
        "CountedStateTransitionLoopSummaryRef",
        "ReadonlyReductionRef",
        "StateTransitionLoopSummaryRef",
    }
    offenders = []
    for relative in _SNAPSHOT_ONLY_MODULES:
        path = PACKAGE_ROOT / relative
        for node in ast.walk(_parse(path)):
            if not isinstance(node, ast.Call):
                continue
            if not (isinstance(node.func, ast.Name) and node.func.id == "isinstance"):
                continue
            if len(node.args) < 2:
                continue
            checked = node.args[1]
            candidates = (
                checked.elts if isinstance(checked, (ast.Tuple, ast.List)) else [checked]
            )
            for candidate in candidates:
                name = candidate.id if isinstance(candidate, ast.Name) else None
                if name in ref_names:
                    offenders.append(f"{relative}:{node.lineno} classifies {name}")
    assert offenders == [], offenders


@pytest.mark.parametrize("module_path", _PUBLICATION_FREE_MODULES)
def test_identity_and_consumers_cannot_publish(module_path):
    """identity / 表現 / renderer は producer の宣言を成立させられない。

    `validated()` が「未検証なら凍らせる」のは identity の計算可能性のためで、
    producer の宣言ではない。同じ場所が公開もできると、candidate hash を 1 回
    取っただけの精錬中の値が solver へ渡せるようになる（この PR の blocker）。
    """

    path = PACKAGE_ROOT / module_path
    assert path.exists(), module_path
    offenders = []
    for name, lineno in _imported_names(_parse(path)):
        if name in _PUBLICATION_NAMES:
            offenders.append(f"{module_path}:{lineno} imports {name}")
    for node in ast.walk(_parse(path)):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        called = None
        if isinstance(func, ast.Name):
            called = func.id
        elif isinstance(func, ast.Attribute):
            called = func.attr
        if called in _PUBLICATION_NAMES:
            offenders.append(f"{module_path}:{node.lineno} calls {called}()")
    assert offenders == [], offenders


def test_only_the_publication_owner_marks_a_value_published():
    """`mark_published` を呼ぶ module は 1 つだけ。"""

    callers = set()
    for path in _module_files():
        for node in ast.walk(_parse(path)):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            called = func.id if isinstance(func, ast.Name) else getattr(func, "attr", None)
            if called == "mark_published":
                callers.add(_relative(path))
    assert callers == {_PUBLICATION_OWNER}, callers


def test_the_lifecycle_state_is_owned_by_one_module():
    """状態 field を直接書く場所を増やさない。

    `_frozen` / `_published` を各所で読み書きすると、「published は validated を
    含む」のような不変条件が module ごとに解釈される。読み書きの規則は
    `core/semantic_lifecycle.py` に集め、他の module は名前付きの述語を使う。
    """

    from scripts.function_tracer_pcode.core import semantic_lifecycle as owner

    state_fields = set(owner.LIFECYCLE_STATE_FIELDS)
    assert state_fields == {"_frozen", "_published"}

    allowed = {
        _PUBLICATION_OWNER,
        "core/semantic_lifecycle.py",
        # carrier は class 既定値としてだけ持つ（下の assert で形を固定する）。
        "core/expression.py",
        "core/condition.py",
    }
    offenders = []
    for path in _module_files():
        relative = _relative(path)
        if relative in allowed:
            continue
        for node in ast.walk(_parse(path)):
            if isinstance(node, ast.Constant) and node.value in state_fields:
                offenders.append(f"{relative}:{node.lineno} names {node.value!r}")
    assert offenders == [], offenders


def test_publication_implies_validation_by_construction():
    """`_published` 単独では PUBLISHED にならない（表現の側で閉じている）。"""

    from scripts.function_tracer_pcode.core.semantic_lifecycle import (
        SemanticLifecycle,
        state_of,
    )

    assert state_of({}) is SemanticLifecycle.CONSTRUCTION
    assert state_of({"_published": True}) is SemanticLifecycle.CONSTRUCTION
    assert state_of({"_frozen": True}) is SemanticLifecycle.VALIDATED
    assert (
        state_of({"_frozen": True, "_published": True}) is SemanticLifecycle.PUBLISHED
    )


#: lifecycle state を持つ意味型（carrier）。既定の複製に任せてはいけない。
_LIFECYCLE_VALUE_TYPES = (
    ("core/expression.py", "Expression"),
    ("core/condition.py", "Condition"),
)


def test_every_lifecycle_value_type_defines_its_own_copy():
    """状態を持つ型は `__copy__` / `__deepcopy__` を自分で定義していること。

    既定の複製は `__dict__` をそのまま写すので、`_published` を持った複製が
    できる。複製の中身（式）は作り直されて未公開なので、**外側だけ公開済み**
    という closure を 1 行も書かずに作れてしまう。型を足したときにこの穴が
    再発しないよう、定義の有無を構造で固定する。
    """

    missing = []
    for relative, type_name in _LIFECYCLE_VALUE_TYPES:
        tree = _parse(PACKAGE_ROOT / relative)
        for node in ast.walk(tree):
            if not isinstance(node, ast.ClassDef) or node.name != type_name:
                continue
            defined = {
                inner.name
                for inner in node.body
                if isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef))
            }
            for hook in ("__copy__", "__deepcopy__"):
                if hook not in defined:
                    missing.append(f"{relative}: {type_name} has no {hook}")
            break
        else:  # pragma: no cover - 型名が変わったら test を直す合図
            missing.append(f"{relative}: {type_name} not found")
    assert missing == [], missing


def test_the_fields_a_copy_drops_are_the_fields_validation_writes():
    """複製が捨てる派生値と、検証が書く派生値が同じ表から出ていること。

    2 つの表に分かれていると、派生値を 1 つ足したときに片方だけ直って、
    「未検証なのに digest を持つ複製」ができる。
    """

    from scripts.function_tracer_pcode.core import semantic_lifecycle as owner

    tree = _parse(PACKAGE_ROOT / _PUBLICATION_OWNER)
    derived_keys = set()
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name != "_derive_node_fields":
            continue
        for inner in ast.walk(node):
            if not isinstance(inner, ast.Dict):
                continue
            for key in inner.keys:
                if isinstance(key, ast.Constant) and isinstance(key.value, str):
                    derived_keys.add(key.value)
    assert derived_keys, "_derive_node_fields not found"
    assert derived_keys == set(owner.DERIVED_STATE_FIELDS), derived_keys
    assert set(owner.NON_INHERITED_FIELDS) == set(owner.LIFECYCLE_STATE_FIELDS) | set(
        owner.DERIVED_STATE_FIELDS
    )


def test_only_the_lifecycle_owner_lists_the_fields_a_new_value_drops():
    """引き継がない field の**一覧**を owner 以外が持っていないこと。

    個々の field を読むのは consumer の仕事（`structural_hash()` など）なので
    禁じない。禁じるのは「落とす field はこれ」という表を 2 つ持つこと —
    それをやると、派生値が 1 つ増えたときに片方だけ直って、状態を捨てたつもり
    の複製が digest だけ引き継ぐ。
    """

    from scripts.function_tracer_pcode.core import semantic_lifecycle as owner

    names = set(owner.NON_INHERITED_FIELDS)
    offenders = []
    for path in _module_files():
        relative = _relative(path)
        if relative == "core/semantic_lifecycle.py":
            continue
        for node in ast.walk(_parse(path)):
            if not isinstance(node, (ast.Tuple, ast.Set, ast.List)):
                continue
            literals = [
                element.value
                for element in node.elts
                if isinstance(element, ast.Constant) and isinstance(element.value, str)
            ]
            listed = names.intersection(literals)
            if len(listed) >= 2:
                offenders.append(f"{relative}:{node.lineno} lists {sorted(listed)}")
    assert offenders == [], offenders


#: lifecycle state を進めてよい関数（commit のみ）。
_LIFECYCLE_COMMIT_FUNCTIONS = {"_commit_validation", "_commit_publication"}
#: state を進める呼び出し。
_LIFECYCLE_MARK_NAMES = {"mark_validated", "mark_published"}


def test_lifecycle_state_only_moves_forward_inside_a_commit():
    """`mark_*` は commit の中だけ。staging の途中では state を動かさない。

    途中で動かすと、closure の検証が失敗したときに root だけ VALIDATED で
    残る（partial commit）。「検証中」は operation-local な staging が持つ。
    """

    path = PACKAGE_ROOT / _PUBLICATION_OWNER
    tree = _parse(path)
    offenders = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name in _LIFECYCLE_COMMIT_FUNCTIONS:
            continue
        for inner in ast.walk(node):
            if not isinstance(inner, ast.Call):
                continue
            func = inner.func
            called = func.id if isinstance(func, ast.Name) else getattr(func, "attr", None)
            if called in _LIFECYCLE_MARK_NAMES:
                offenders.append(
                    f"{_PUBLICATION_OWNER}:{inner.lineno} {node.name}() calls {called}()"
                )
    assert offenders == [], offenders


def test_the_commit_functions_exist_and_are_the_only_state_writers():
    """commit 関数が実在し、`mark_*` の呼び出し元が他に無いこと。"""

    callers = set()
    for path in _module_files():
        tree = _parse(path)
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            for inner in ast.walk(node):
                if not isinstance(inner, ast.Call):
                    continue
                func = inner.func
                called = (
                    func.id if isinstance(func, ast.Name) else getattr(func, "attr", None)
                )
                if called in _LIFECYCLE_MARK_NAMES:
                    callers.add(node.name)
    assert callers == _LIFECYCLE_COMMIT_FUNCTIONS, callers


def _rendered_text_name(node: ast.AST):
    if not isinstance(node, ast.Name):
        return None
    return node.id if node.id.endswith(_RENDERED_TEXT_NAMES) else None


@pytest.mark.parametrize("module_path", _RENDER_BODY_MODULES)
def test_no_renderer_body_inspects_rendered_text(module_path):
    """描画テキストを文字列として見る分岐は renderer に **1 つも無い**。

    子の描画結果は参照 1 個なので、その文字を見た分岐は「共有したか」で答えが
    変わる。判定に要る性質は型付きの property で運ぶ（`SmtTermProperties`）。
    この test は種類を列挙して 0 件に固定するので、同種の分岐が後から足されれば
    落ちる。
    """

    path = PACKAGE_ROOT / module_path
    offenders = []
    for function in ast.walk(_parse(path)):
        if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if (module_path, function.name) in _FRAGMENT_READERS:
            continue
        for node in ast.walk(function):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr in _TEXT_INSPECTION_METHODS
                and _rendered_text_name(node.func.value)
            ):
                offenders.append(
                    f"{module_path}:{node.lineno} {function.name} inspects "
                    f"{_rendered_text_name(node.func.value)}.{node.func.attr}()"
                )
            if isinstance(node, ast.Compare):
                operands = [node.left, *node.comparators]
                names = [name for name in map(_rendered_text_name, operands) if name]
                literals = [
                    item
                    for item in operands
                    if isinstance(item, ast.Constant) and isinstance(item.value, str)
                ]
                if names and literals:
                    offenders.append(
                        f"{module_path}:{node.lineno} {function.name} compares "
                        f"{names[0]} with a string literal"
                    )
    assert offenders == [], offenders


def test_the_only_text_inspection_is_reached_from_the_fragment_classifier():
    """text を見る唯一の関数は、分類器からしか呼ばれない。

    分類器は node 自身の fragment を 1 回だけ見て型付きの性質を決める。他所から
    呼べると「子の描画結果を見る」経路が復活する。
    """

    owner_module, owner_function = _TEXT_INSPECTION_OWNER
    classifier_module, classifier_function = _FRAGMENT_CLASSIFIER
    callers = []
    for path in _module_files():
        relative = _relative(path)
        if relative == owner_module:
            continue
        for function in ast.walk(_parse(path)):
            if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            for node in ast.walk(function):
                if (
                    isinstance(node, ast.Call)
                    and isinstance(node.func, ast.Name)
                    and node.func.id == owner_function
                ):
                    callers.append((relative, function.name))
    assert callers == [(classifier_module, classifier_function)], callers


def test_the_typed_term_properties_carry_every_observation_the_renderer_needs():
    """性質は node/fragment から決まり、共有の有無で変わらない。"""

    from scripts.function_tracer_pcode.core.render_smt.render import (
        SmtTermProperties,
        classify_smt_fragment,
    )

    assert set(SmtTermProperties._fields) == {"is_fp_term", "boolean_literal"}
    assert classify_smt_fragment("(fp.add a b)", None, False).is_fp_term is True
    assert classify_smt_fragment("(bvadd a b)", None, False).is_fp_term is False
    assert classify_smt_fragment("true", None, False).boolean_literal is True
    assert classify_smt_fragment("false", None, False).boolean_literal is False
    assert classify_smt_fragment("(ite c a b)", None, False).boolean_literal is None


def test_identity_is_never_built_from_the_human_rendering():
    """`to_string()` の結果を identity / cache key / digest に使わない。

    人向けの表示は読みやすさのために変わる。identity に使うと、書式を直した
    だけで cache の当たり外れと証明の一致条件が動く（PR-22-C で共有参照を
    入れたのがまさにその変更）。
    """

    offenders: List[str] = []
    for path in _module_files():
        relative = _relative(path)
        tree = _parse(path)
        for function in ast.walk(tree):
            if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            name = function.name.lower()
            builds_identity = (
                name.endswith("_key")
                or "identity" in name
                or "digest" in name
                or "fingerprint" in name
            )
            if not builds_identity:
                continue
            for node in ast.walk(function):
                if (
                    isinstance(node, ast.Call)
                    and isinstance(node.func, ast.Attribute)
                    and node.func.attr in _RENDERED_TEXT_CALLS
                ):
                    offenders.append(f"{relative}:{node.lineno} in {function.name}")
    assert offenders == [], offenders


#: 描画を打ち切る / 内部不整合を告げる型。回復 handler に吸わせない。
_RENDER_FAILURE_TYPES = frozenset(
    {
        "RenderOutputLimitExceeded",
        "RenderPlanInvariantError",
        "RenderedTermContractError",
        "RenderGraphCycleError",
    }
)

#: source 側でそれらを再送出するときに書く名前（`render_plan` が唯一の owner）。
_RENDER_FAILURE_TUPLE = "RENDER_FAILURES"


@pytest.mark.parametrize("module_path", _RENDER_BODY_MODULES)
def test_a_render_abort_is_never_swallowed_by_a_recovery_handler(module_path):
    """描画 module の広い `except` は、打ち切りを **必ず** 先に通すこと。

    上限で止めたこと・閉路だったことが「この枝は描けなかった」に化けると、
    予算も閉路検出も効かないまま解析が続き、切り詰めた表現が下流へ出る。

    規則であって一覧ではない: 「子を描く呼び出しを含む `try` だけ」を見ると、
    何が打ち切りを投げ得るかの一覧を持つことになり、投げ得る場所が増えるたび
    （属性の評価が反復 driver を回すようになった、など）に一覧の方が古くなる。
    だからこれらの module では、広い `except` すべてに typed な再送出を課す。
    その `try` が本当に何も描かないなら、再送出は何もしない 1 行で済む — 一覧を
    保守し続けるより安い。`except Exception` を消せるならその方が良い
    （baseline は delete-only）。
    """

    path = PACKAGE_ROOT / module_path
    offenders = []
    for node in ast.walk(_parse(path)):
        if not isinstance(node, ast.Try):
            continue
        broad = [
            index
            for index, handler in enumerate(node.handlers)
            if handler.type is None
            or (isinstance(handler.type, ast.Name) and handler.type.id == "Exception")
        ]
        if not broad:
            continue
        reraises = []
        for index, handler in enumerate(node.handlers):
            names = set()
            if isinstance(handler.type, ast.Name):
                names.add(handler.type.id)
            elif isinstance(handler.type, ast.Tuple):
                names.update(
                    element.id for element in handler.type.elts if isinstance(element, ast.Name)
                )
            if _RENDER_FAILURE_TUPLE in names:
                reraises.append(index)
        if not reraises:
            offenders.append(f"{module_path}:{node.lineno} (nothing lets a render abort through)")
            continue
        if all(index > broad[0] for index in reraises):
            offenders.append(f"{module_path}:{node.lineno} (typed handler comes too late)")
    assert offenders == [], offenders


def test_the_render_failure_types_have_one_owner():
    """再送出する型の一覧が `render_plan.RENDER_FAILURES` 1 箇所であること。

    同じ一覧が module ごとに手書きされると、型を足したときに一部だけが追従して
    「その module では吸われる」状態が静かに残る。
    """

    from scripts.function_tracer_pcode.core import render_plan

    assert {failure.__name__ for failure in render_plan.RENDER_FAILURES} == set(
        _RENDER_FAILURE_TYPES
    )
    for module_path in _RENDER_BODY_MODULES:
        source = (PACKAGE_ROOT / module_path).read_text(encoding="utf-8")
        for node in ast.walk(ast.parse(source)):
            if not isinstance(node, ast.ExceptHandler) or not isinstance(node.type, ast.Tuple):
                continue
            names = {
                element.id for element in node.type.elts if isinstance(element, ast.Name)
            }
            assert not (names & _RENDER_FAILURE_TYPES), (
                f"{module_path}:{node.lineno} spells out the render failure types; "
                f"catch render_plan.{_RENDER_FAILURE_TUPLE} instead"
            )


# ---------------------------------------------------------------------------
# 走査 machinery の owner（`render_plan.ResolutionSchedule`）
#
# 描画 driver と node 属性の評価は同じ形の反復をする。予定・経路・切り替えの
# 規則を両方に書くと片方だけが直る（実際、閉路判定が scheduled を active と
# 数える同じ誤りが両方にあった）。規則は 1 実装に寄せ、借りる側が別実装へ
# 戻ったらここで落ちる。
# ---------------------------------------------------------------------------

#: 走査 machinery を所有する module。
_TRAVERSAL_OWNER = "core/render_plan.py"

#: 反復走査を回す（= 予定表を借りる）module。
_TRAVERSAL_BORROWERS = ("core/render_smt/attributes.py",)


def test_the_cycle_judgement_has_one_implementation():
    """`RenderGraphCycleError` を投げるのは予定表だけであること。

    閉路かどうかを言うには「今の経路に居るか」を知らねばならず、それを知って
    いるのは予定表だけ。別 module が投げているなら、その module が経路を自分で
    持っている（= 2 実装目がある）。
    """

    offenders = []
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT).as_posix()
        if relative.startswith("tests/") or relative == _TRAVERSAL_OWNER:
            continue
        for node in ast.walk(_parse(path)):
            if not isinstance(node, ast.Raise) or node.exc is None:
                continue
            raised = node.exc
            name = None
            if isinstance(raised, ast.Call) and isinstance(raised.func, ast.Name):
                name = raised.func.id
            elif isinstance(raised, ast.Name):
                name = raised.id
            if name == "RenderGraphCycleError":
                offenders.append(f"{relative}:{node.lineno}")
    assert offenders == [], offenders


def test_the_collection_switch_rule_has_one_owner():
    """切り替えの閾値を読むのは予定表だけであること。

    driver 側が閾値を読むと、切り替えの規則が実質 2 つになる。予定表が
    `should_collect_requests()` で答える。
    """

    offenders = []
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT).as_posix()
        if relative.startswith("tests/") or relative == _TRAVERSAL_OWNER:
            continue
        for node in ast.walk(_parse(path)):
            if isinstance(node, ast.Name) and node.id == "DISCOVERY_AFTER_RETRIES":
                offenders.append(f"{relative}:{node.lineno}")
    assert offenders == [], offenders


@pytest.mark.parametrize("module_path", _TRAVERSAL_BORROWERS)
def test_a_borrower_keeps_no_active_path_of_its_own(module_path):
    """予定表を借りる側が、経路の帳簿を自分で持たないこと。

    自前の `on_path` / `active` を持った瞬間に、閉路判定が何を見るかという
    判断が 2 箇所になる。借りる側は `ResolutionSchedule` を使うだけ。
    """

    path = PACKAGE_ROOT / module_path
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source)

    assert "ResolutionSchedule" in source, module_path
    bookkeeping = {"on_path", "active", "_active", "_enter", "_leave", "_enter_path", "_leave_path"}
    offenders = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store) and node.id in bookkeeping:
            offenders.append(f"{module_path}:{node.lineno} assigns {node.id}")
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in bookkeeping:
            offenders.append(f"{module_path}:{node.lineno} defines {node.name}")
    assert offenders == [], offenders


# ---------------------------------------------------------------------------
# 組み立て方: 幅が子の数に比例する本体は、前から 1 回で組み立てること
# ---------------------------------------------------------------------------

#: 可変長の子を 1 つの文字列へ畳んでよい唯一の道。
_FRAGMENT_BUILDER = "fragment"


def _iterates_a_child_collection(node: ast.AST) -> bool:
    """`expr.operands` / `branches` のような **可変長の子**を回しているか。"""

    sources = {"operands", "branches", "value", "cases", "arguments", "args"}
    for inner in ast.walk(node):
        if isinstance(inner, ast.Attribute) and inner.attr in sources:
            return True
        if isinstance(inner, ast.Name) and inner.id in sources:
            return True
    return False


@pytest.mark.parametrize("module_path", _RENDER_BODY_MODULES)
def test_a_wide_body_builds_its_fragment_in_one_pass(module_path):
    """**可変長の子**を後ろから積み直さないこと（規則、一覧ではない）。

    `result = f"(ite … {result})"` のように後ろから積み直すと、文字列 copy が
    branch 数の 2 乗になる。前から置いて最後に 1 回連結すれば線形。

    これは **予算の話ではない**（組み立て中の fragment は speculative なので、
    出力予算では裁かない）。renderer の書き方の問題で、PR-22-C の変更軸そのもの。
    `join` は線形なので禁じない — 禁じるのは 2 乗になる形だけ。

    見るのは「子の集まり（`operands` / `branches` …）を回しているか」。深さや幅で
    決まらない繰り返し（結果幅で決まる `let` の入れ子、固定個数の `concat`）は
    対象にしない。
    """

    path = PACKAGE_ROOT / module_path
    offenders = []
    for loop in ast.walk(_parse(path)):
        if not isinstance(loop, (ast.For, ast.AsyncFor)):
            continue
        if not _iterates_a_child_collection(loop.iter):
            continue
        for node in ast.walk(loop):
            if isinstance(node, ast.Assign) and len(node.targets) == 1:
                target = node.targets[0]
                if isinstance(target, ast.Name) and isinstance(node.value, ast.JoinedStr):
                    reread = any(
                        isinstance(part, ast.FormattedValue)
                        and isinstance(part.value, ast.Name)
                        and part.value.id == target.id
                        for part in node.value.values
                    )
                    if reread:
                        offenders.append(
                            f"{module_path}:{node.lineno} rebuilds {target.id} from itself "
                            "while walking a child collection"
                        )
            if (
                isinstance(node, ast.AugAssign)
                and isinstance(node.op, ast.Add)
                and isinstance(node.target, ast.Name)
                and isinstance(node.value, (ast.JoinedStr, ast.Constant))
                and isinstance(getattr(node.value, "value", ""), str)
            ):
                offenders.append(
                    f"{module_path}:{node.lineno} accumulates a string with += "
                    "while walking a child collection"
                )
    assert offenders == [], offenders


def test_the_render_budget_has_one_meaning_and_one_owner():
    """出力予算を書き出し口以外へ渡さないこと。

    `render_bytes` が意味するのは書き出した byte 数だけ。計画中に作る fragment は
    speculative（本体が要求した子を捨てる、instance が出力に現れない）なので、
    そこへ出力予算を当てると **正しい描画を拒める**。

    予算を受け取ってよいのは `CountingWriter` だけ。計画側が予算引数を持つと、
    「本番では渡さないが test では渡す」形になり、production で成立しない保証を
    test が主張できてしまう。
    """

    import inspect

    from scripts.function_tracer_pcode.core import render_plan

    # 計画側は予算引数を持たない
    parameters = set(inspect.signature(render_plan.build_render_plan).parameters)
    assert not [name for name in parameters if "limit" in name or "budget" in name], parameters

    # 予算を渡す呼び出しは書き出し口だけ
    offenders = []
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT).as_posix()
        if relative.startswith("tests/"):
            continue
        for node in ast.walk(_parse(path)):
            if not isinstance(node, ast.Call):
                continue
            name = None
            if isinstance(node.func, ast.Name):
                name = node.func.id
            elif isinstance(node.func, ast.Attribute):
                name = node.func.attr
            if name in {"CountingWriter", "RenderOutputLimitExceeded"}:
                continue  # 予算の owner と、それが投げる typed failure
            for keyword in node.keywords:
                if keyword.arg and keyword.arg.endswith("limit_bytes"):
                    target = name or "<call>"
                    if target in {
                        "render_smt_term", "render_human_text",
                        "_to_smt_internal", "_condition_to_smt_internal",
                    }:
                        continue  # 入口どうしの受け渡し（最終的に writer へ届く）
                    offenders.append(f"{relative}:{node.lineno} passes {keyword.arg} to {target}")
    assert offenders == [], offenders


def test_the_render_budget_is_not_multiplied_into_a_second_one():
    """出力予算から別の上限を導かないこと。

    以前は「材料の許容量 = 出力予算 × 8」があった。材料と出力の比には普遍的な
    有限上限が無いので、その倍率は原理的に決められない。倍率を書ける形が残ると、
    次に困ったときまた倍率を足す（そして形状に合わせて調整する）ことになる。
    """

    modules = ("core/render_plan.py", "core/render_output.py")
    offenders = []
    for module_path in modules:
        for node in ast.walk(_parse(PACKAGE_ROOT / module_path)):
            if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Mult):
                continue
            names = {
                inner.id
                for inner in ast.walk(node)
                if isinstance(inner, ast.Name)
            } | {
                inner.attr
                for inner in ast.walk(node)
                if isinstance(inner, ast.Attribute)
            }
            if any("limit" in name.lower() or "budget" in name.lower() for name in names):
                offenders.append(f"{module_path}:{node.lineno}")
    assert offenders == [], offenders




# ---------------------------------------------------------------------------
# 式サイズ予算と出力の準備（Issue #22 PR-22-D、計画 §4.8 M-1 / M-3）
#
# 変更軸ごとの owner:
#   予算の既定値・環境変数      config/settings.py（`EXPRESSION_BUDGET_DEFAULTS`）
#   予算の値の型・scope・超過の変換  core/budget_policy.py
#   JSON の書き方と大きさの数え方   core/json_encoding.py（`RESULT_JSON_POLICY`）
#   出力の準備・3 層の合成        checker/output_preparation.py
#   呼び出し順序                authority/lifecycle/production_boundary.py
# 既定値を変える変更が深い module へ波及しないこと、数え方と encoder が 1 つの
# policy を共有すること、boundary が処理本体を抱え込まないことを固定する。
# ---------------------------------------------------------------------------

_BUDGET_OWNER_BANS = {
    "core/budget_policy.py": (
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.reporting",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "scripts.function_tracer_pcode.core.render_plan",
        "scripts.function_tracer_pcode.core.render_python",
        "os",
    ),
    "core/json_encoding.py": (
        "scripts.function_tracer_pcode.authority",
        "scripts.function_tracer_pcode.checker",
        "scripts.function_tracer_pcode.cli",
        "scripts.function_tracer_pcode.config",
        "scripts.function_tracer_pcode.smt",
        "scripts.function_tracer_pcode.core.expression",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.core.render_smt",
        "os",
    ),
    # 出力層は solver の実行・描画・identity・解析に依存しない（読むのは結果の
    # 属性と authority が公開した receipt 表現だけ）。
    "checker/output_preparation.py": (
        "scripts.function_tracer_pcode.smt",
        "scripts.function_tracer_pcode.core.render_smt",
        "scripts.function_tracer_pcode.core.render_python",
        "scripts.function_tracer_pcode.core.render_plan",
        "scripts.function_tracer_pcode.core.structural",
        "scripts.function_tracer_pcode.analysis",
        "scripts.function_tracer_pcode.semantics",
        "scripts.function_tracer_pcode.proof",
        "scripts.function_tracer_pcode.config",
        "os",
    ),
}


@pytest.mark.parametrize("module_path", sorted(_BUDGET_OWNER_BANS))
def test_budget_and_output_owners_point_downward_only(module_path):
    path = PACKAGE_ROOT / module_path
    offenders = [
        f"{module_path}:{lineno} imports {name}"
        for name, lineno in _imported_modules(_parse(path))
        for prefix in _BUDGET_OWNER_BANS[module_path]
        if name == prefix or name.startswith(prefix + ".")
    ]
    assert offenders == [], offenders


def _string_constants(tree: ast.Module) -> Iterable[Tuple[str, int]]:
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            yield node.value, node.lineno


def test_m1_budget_defaults_and_env_names_live_only_in_config():
    """M-1: 既定値を変える変更は config の表と policy の構築だけで閉じる。"""

    from scripts.function_tracer_pcode.config.settings import EXPRESSION_BUDGET_DEFAULTS

    env_names = {env_name for _name, env_name, _default in EXPRESSION_BUDGET_DEFAULTS}
    offenders = []
    builders = []
    for path in _module_files():
        relative = _relative(path)
        tree = _parse(path)
        if relative != "config/settings.py":
            offenders.extend(
                f"{relative}:{lineno} names {value}"
                for value, lineno in _string_constants(tree)
                if value in env_names
            )
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "expression_budget_policy"
            ):
                builders.append(relative)
    assert offenders == [], offenders
    # policy を組み立てるのは入口（checker の構築）だけ。深い module は scope から読む。
    assert builders == ["checker/checker.py"], builders


#: 深い層（core / analysis / semantics / proof）で環境変数・config を直接読む
#: module の **現状**（delete-only）。予算を足しても増えない。
_DEEP_LAYERS = ("core/", "analysis/", "semantics/", "proof/")
_DEEP_ENV_READERS_BASELINE = frozenset({"analysis/returns/expansion_budget.py"})
_DEEP_CONFIG_READERS_BASELINE = frozenset({
    "analysis/limits.py",
    "analysis/returns/callee_unbound_reuse.py",
    "analysis/tracer.py",
    "semantics/transform/expander.py",
})


def test_m1_deep_modules_gain_no_env_or_config_reads():
    env_readers, config_readers = set(), set()
    for path in _module_files():
        relative = _relative(path)
        if not relative.startswith(_DEEP_LAYERS):
            continue
        tree = _parse(path)
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Attribute)
                and node.attr in {"environ", "getenv"}
                and isinstance(node.value, ast.Name)
                and node.value.id == "os"
            ):
                env_readers.add(relative)
        for name, _lineno in _imported_modules(tree):
            if name.startswith("scripts.function_tracer_pcode.config"):
                config_readers.add(relative)
    assert env_readers <= _DEEP_ENV_READERS_BASELINE, env_readers
    assert config_readers <= _DEEP_CONFIG_READERS_BASELINE, config_readers
    # baseline は delete-only（消えた読み手は baseline からも消す）
    assert env_readers == _DEEP_ENV_READERS_BASELINE, env_readers
    assert config_readers == _DEEP_CONFIG_READERS_BASELINE, config_readers


#: 予算の値（policy の field）を **直接** 読んでよい module。どれも「その予算を
#: 数える唯一の場所」。それ以外は `enforce_budget(kind, …)` を通す。
_POLICY_FIELD_READERS = {
    "render_bytes": {"core/render_smt/render.py"},
    "serialization_bytes": {
        "core/budget_policy.py", "core/expression.py", "checker/output_preparation.py",
    },
    # 数える量を予算で打ち切るために読む（比べるのは `enforce_budget`）
    "expression_nodes": {"semantics/transform/expander_multiequal.py"},
    "expansion_cases": set(),
    "serialization_nodes": set(),
    "envelope_headroom_bytes": {"core/budget_policy.py", "checker/output_preparation.py"},
}


def test_each_budget_value_is_read_by_its_one_counting_site():
    readers = {name: set() for name in _POLICY_FIELD_READERS}
    for path in _module_files():
        relative = _relative(path)
        if relative == "config/settings.py":
            continue
        for node in ast.walk(_parse(path)):
            if isinstance(node, ast.Attribute) and node.attr in readers:
                readers[node.attr].add(relative)
    for name, allowed in _POLICY_FIELD_READERS.items():
        assert readers[name] <= allowed | {"core/budget_policy.py"}, (name, readers[name])


def test_the_limitation_is_built_in_one_place_and_raised_from_the_checkpoints():
    constructors, raisers = set(), set()
    for path in _module_files():
        relative = _relative(path)
        for node in ast.walk(_parse(path)):
            if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
                continue
            if node.func.id == "ExpressionSizeBudgetExceeded":
                constructors.add(relative)
            if node.func.id in {
                "enforce_budget",
                "raise_expression_size_budget_exceeded",
                "raise_render_budget_exceeded",
            }:
                raisers.add(relative)
    assert constructors == {"core/budget_policy.py"}, constructors
    assert raisers == {
        "core/budget_policy.py",
        "core/render_smt/render.py",
        "semantics/transform/expander_multiequal.py",
        "checker/output_preparation.py",
    }, raisers


def test_one_json_policy_is_shared_by_the_estimator_encoder_and_cli():
    """見積り・bounded encoder・CLI の出力が同じ policy object を使う。"""

    instantiations, cli_dumps = [], []
    for path in _module_files():
        relative = _relative(path)
        for node in ast.walk(_parse(path)):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "JsonEncodingPolicy"
            ):
                instantiations.append(relative)
            if (
                relative == "cli/commands/equivalence.py"
                and isinstance(node, ast.Attribute)
                and node.attr in {"dumps", "dump"}
            ):
                cli_dumps.append(node.lineno)
    assert instantiations == ["core/json_encoding.py"], instantiations
    # 結果 JSON の文字列は envelope（bounded encoder）からしか来ない
    assert cli_dumps == [], cli_dumps


def test_the_production_boundary_only_orders_the_output_steps():
    """R-A2: boundary は準備と scope の **呼び出し** だけを持つ。"""

    path = PACKAGE_ROOT / "authority/lifecycle/production_boundary.py"
    tree = _parse(path)
    names = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)} | {
        node.attr for node in ast.walk(tree) if isinstance(node, ast.Attribute)
    }
    forbidden = {
        "value_bytes", "encode_bounded", "RESULT_FIELDS", "OutputPreparer",
        "RESULT_JSON_POLICY", "estimate_legacy_dict_bytes", "enforce_budget",
        "serialization_bytes", "render_bytes", "envelope_headroom_bytes",
    }
    assert not (names & forbidden), names & forbidden
    imported = {name for name, _lineno in _imported_names(tree)}
    assert {"prepare_pair_output", "budget_policy_scope"} <= imported


def test_no_budget_is_derived_by_a_multiplier():
    """出力予算・直列化予算から別の上限を倍率で作らない（PR-22-C の規則の延長）。"""

    modules = (
        "core/budget_policy.py",
        "core/json_encoding.py",
        "checker/output_preparation.py",
        "config/settings.py",
    )
    offenders = []
    for module_path in modules:
        for node in ast.walk(_parse(PACKAGE_ROOT / module_path)):
            if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Mult):
                continue
            names = {
                inner.id for inner in ast.walk(node) if isinstance(inner, ast.Name)
            } | {
                inner.attr for inner in ast.walk(node) if isinstance(inner, ast.Attribute)
            }
            if any(
                word in name.lower()
                for name in names
                for word in ("limit", "budget", "bytes", "headroom")
            ):
                offenders.append(f"{module_path}:{node.lineno}")
    assert offenders == [], offenders


#: 出力層（`checker/output_preparation.py`）を import してよい module。どれも
#: 「結果を出力する側」で、意味解析・solver・authority の判定はここに入らない。
#: だから出力の表へ field を足しても、意味の経路（query・判定・reason）は動かない
#: （M-3。実経路での確認は `test_issue22d_output_schema_locality.py`）。
_OUTPUT_LAYER_IMPORTERS = frozenset({
    "checker/result.py",
    "authority/lifecycle/production_boundary.py",
    "cli/commands/equivalence.py",
})


def test_m3_only_the_output_side_depends_on_the_output_layer():
    importers = set()
    for path in _module_files():
        relative = _relative(path)
        if relative == "checker/output_preparation.py":
            continue
        for name, _lineno in _imported_modules(_parse(path)):
            if name == "scripts.function_tracer_pcode.checker.output_preparation":
                importers.add(relative)
    assert importers == _OUTPUT_LAYER_IMPORTERS, importers


def test_only_fields_prepared_before_authority_can_become_a_limitation():
    """authority 確定後に合成する field（B / C）は限界を作れない（計画 §4.6）。"""

    from scripts.function_tracer_pcode.checker.output_preparation import (
        RESULT_FIELDS,
        FieldOwner,
        Overflow,
    )

    for item in RESULT_FIELDS:
        if item.overflow is Overflow.LIMITATION:
            assert item.owner is FieldOwner.PREPARED, item.key
        if item.owner is FieldOwner.AUTHORITY:
            assert item.overflow is Overflow.INVARIANT, item.key


def test_the_output_option_is_read_once_when_the_output_is_prepared():
    """`emit_debug_trace`（出力 option）を読むのは `OutputOptions.for_result` だけ。"""

    offenders = []
    for path in _module_files():
        relative = _relative(path)
        if not relative.startswith(("checker/output_preparation.py", "cli/")):
            continue
        tree = _parse(path)
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr == "emit_debug_trace":
                offenders.append(f"{relative}:{node.lineno}")
            if (
                isinstance(node, ast.Constant)
                and node.value == "emit_debug_trace"
            ):
                offenders.append(f"{relative}:{node.lineno}")
    assert len(offenders) == 1 and offenders[0].startswith(
        "checker/output_preparation.py"
    ), offenders
