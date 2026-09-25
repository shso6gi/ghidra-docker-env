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
import re
from typing import Dict, Iterable, List, Optional, Set, Tuple

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
    # Issue #165: 終端 authority の変更軸ごとの owner。process の終端の module は
    # 分類器（decision）にも CLI の orchestration（supervisor_command）にも依存
    # しない。分類器は下の owner を import して同じ判断・同じ検証を呼び直す。
    # 語彙・同一性・envelope の owner は標準 library と contracts だけに依存する。
    "authority/process/checkpoint_vocabulary.py": (
        "os", "fcntl", "subprocess", "signal", "json", "pathlib",
        "scripts.function_tracer_pcode.authority",
    ),
    "authority/process/store_layout.py": (
        "os", "fcntl", "subprocess", "signal", "json", "pathlib",
        "scripts.function_tracer_pcode.authority",
    ),
    "authority/process/child_exit.py": (
        "os", "fcntl", "subprocess", "signal", "json", "pathlib",
        "scripts.function_tracer_pcode.authority",
    ),
    "authority/process/process_identity.py": (
        "fcntl", "subprocess", "signal", "json",
        "scripts.function_tracer_pcode.authority",
    ),
    # envelope の owner は contracts と store_layout（file 名）だけに依存する。
    "authority/process/canonical_envelope.py": (
        "os", "fcntl", "subprocess", "signal", "pathlib",
        "scripts.function_tracer_pcode.authority.decision", "scripts.function_tracer_pcode.authority.lifecycle",
        "scripts.function_tracer_pcode.authority.process.supervisor",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
        "scripts.function_tracer_pcode.authority.process.terminal_recovery",
        "scripts.function_tracer_pcode.authority.process.terminal_snapshot",
        "scripts.function_tracer_pcode.authority.process.terminal_transaction",
        "scripts.function_tracer_pcode.authority.process.terminal_driver",
        "scripts.function_tracer_pcode.authority.process.checkpoint_archive",
    ),
    # 復旧の判断は純関数（store を読む・書く・process を触る、のどれもしない）。
    "authority/process/terminal_recovery.py": (
        "os", "fcntl", "subprocess", "signal", "tempfile", "json", "pathlib",
        "scripts.function_tracer_pcode.authority.decision",
        "scripts.function_tracer_pcode.authority.process.supervisor",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
        "scripts.function_tracer_pcode.authority.process.terminal_snapshot",
        "scripts.function_tracer_pcode.authority.process.terminal_transaction",
        "scripts.function_tracer_pcode.authority.process.terminal_driver",
        "scripts.function_tracer_pcode.authority.process.checkpoint_archive",
    ),
    # D / E / A の schema と検証は file も process も触らない（書くのは store）。
    "authority/process/terminal_evidence.py": (
        "os", "fcntl", "subprocess", "signal", "tempfile",
        "scripts.function_tracer_pcode.authority.decision",
        "scripts.function_tracer_pcode.authority.process.supervisor",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
        "scripts.function_tracer_pcode.authority.process.terminal_recovery",
    ),
    # archive は file の移動と照合だけ（署名・判断・lock は持たない）。
    "authority/process/checkpoint_archive.py": (
        "fcntl", "subprocess", "signal",
        "scripts.function_tracer_pcode.authority.decision",
        "scripts.function_tracer_pcode.authority.process.supervisor",
        "scripts.function_tracer_pcode.authority.process.terminal_recovery",
        "scripts.function_tracer_pcode.authority.process.terminal_evidence",
    ),
    "authority/process/terminal_snapshot.py": (
        "fcntl", "subprocess", "signal",
        "scripts.function_tracer_pcode.authority.decision",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
        "scripts.function_tracer_pcode.authority.process.terminal_driver",
    ),
    "authority/process/terminal_transaction.py": (
        "fcntl", "subprocess", "signal",
        "scripts.function_tracer_pcode.authority.decision",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
        "scripts.function_tracer_pcode.authority.process.terminal_driver",
    ),
    # driver は loop の方針だけ（process の終了観測や signal は supervisor command）。
    "authority/process/terminal_driver.py": (
        "os", "fcntl", "subprocess", "signal",
        "scripts.function_tracer_pcode.authority.decision",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
    ),
    "authority/process/terminal_projection.py": (
        "os", "fcntl", "subprocess", "signal",
        "scripts.function_tracer_pcode.authority.decision",
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
    ),
    # store は終端の判断・transaction を知らない（lock と ownership だけを提供する）。
    "authority/process/supervisor.py": (
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
        "scripts.function_tracer_pcode.authority.process.terminal_recovery",
        "scripts.function_tracer_pcode.authority.process.terminal_snapshot",
        "scripts.function_tracer_pcode.authority.process.terminal_transaction",
        "scripts.function_tracer_pcode.authority.process.terminal_driver",
        "scripts.function_tracer_pcode.authority.process.terminal_projection",
    ),
    # supervisor の CLI（orchestration）は分類器を呼ばない。
    "authority/process/supervisor_command.py": (
        "scripts.function_tracer_pcode.authority.decision",
    ),
    # 分類器は process の orchestration（CLI）に依存しない。
    "authority/decision/canonical_result.py": (
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
    ),
    "authority/decision/production_cutover.py": (
        "scripts.function_tracer_pcode.authority.process.supervisor_command",
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
    # policy を組み立てるのは入口だけ: checker の構築と、pair 境界を通らなかった結果（起動・
    # import 失敗の ERROR）を最終 envelope にする CLI。深い module は scope から読む。
    assert sorted(builders) == ["checker/checker.py", "cli/commands/equivalence.py"], builders


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
    "serialization_bytes": {"core/budget_policy.py", "checker/output_preparation.py"},
    # 数える量を予算で打ち切るために読む（比べるのは `enforce_budget`）
    "expression_nodes": {"semantics/transform/expander_multiequal.py"},
    "expansion_cases": set(),
    "serialization_nodes": set(),
    # 出力 schema が headroom の最小値を確かめる（checker 構築時）
    "envelope_headroom_bytes": {
        "core/budget_policy.py", "checker/output_preparation.py", "checker/output_schema.py",
    },
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
    # policy を作るのは json_encoding だけ（結果 JSON と、同じ文字列の規則で区切りだけ詰める
    # 永続化の envelope の 2 つ）
    assert instantiations == ["core/json_encoding.py"] * 2, instantiations
    from scripts.function_tracer_pcode.core import json_encoding

    persisted = json_encoding.PERSISTED_ENVELOPE_JSON_POLICY
    assert (persisted.ensure_ascii, persisted.sort_keys) == (
        json_encoding.RESULT_JSON_POLICY.ensure_ascii, json_encoding.RESULT_JSON_POLICY.sort_keys,
    )
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
        "measure", "encode_bounded", "RESULT_FIELDS", "OutputPreparer",
        "RESULT_JSON_POLICY", "JsonObjectBudget", "estimate_legacy_dict_bytes",
        "enforce_budget", "serialization_bytes", "render_bytes", "envelope_headroom_bytes",
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
    # 出力 schema は出力層の一部（C の診断 field の上限を `RESULT_FIELDS` から導く）
    "checker/output_schema.py",
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


# ---------------------------------------------------------------------------
# live → prepared の変換境界（Issue #22 PR-22-D、3 回目の修正）
#
# 表現を作るのは walker（`core/json_encoding._Walk`: 出力の `prepare` と `to_dict()` /
# snapshot の `materialize`）だけ。record は `json_items()` で **source**（scalar・既存の
# 値への参照・record・遅延構成子）を 1 つずつ返し、表現を先に作らない。field / record を
# 足すたびに同じ欠陥を入れ直さないための **規則**（一覧ではない）:
#
# * J1 `json_items()` と出力 field の読み方は、内包表記・`list()` などの複製・`to_dict()`・
#   `join` をしない（固定個数の scalar を作るのはよい）
# * J2 record の層（core / analysis / semantics / smt / checker / proof）で `to_dict()` を
#   持つ class は `json_items()` も持つ（例外は理由つきの固定の形の class だけ）
# * J3 解析 1 件分の表現は `RESULT_JSON_POLICY.materialize(..., budget=work)` だけで作る
# ---------------------------------------------------------------------------

#: producer が呼んではいけない「表現を先に作る」操作
_EAGER_METHODS = frozenset({
    "to_dict", "deepcopy", "copy", "dumps", "asdict", "materialize", "prepare",
    "project_bounded", "join", "json_view",
    # identity key の組み立て（key の owner は identity。表現の producer が呼ぶと、key の
    # 大きさの tuple を予算の前に作る）
    "stable_key", "to_key", "structural_key",
})
_EAGER_BUILTINS = frozenset({"list", "dict", "tuple", "sorted", "set", "frozenset", "deepcopy", "asdict"})


def _eager_constructions(node: ast.AST) -> List[str]:
    found = []
    for inner in ast.walk(node):
        if isinstance(inner, (ast.ListComp, ast.DictComp, ast.SetComp)):
            found.append(f"{type(inner).__name__}@{inner.lineno}")
        elif isinstance(inner, ast.Call):
            func = inner.func
            if isinstance(func, ast.Attribute) and func.attr in _EAGER_METHODS:
                found.append(f"{func.attr}()@{inner.lineno}")
            elif isinstance(func, ast.Name) and func.id in _EAGER_BUILTINS:
                found.append(f"{func.id}()@{inner.lineno}")
    return found


def _output_field_rows(tree: ast.Module) -> List[ast.Call]:
    for node in tree.body:
        target = getattr(node, "target", None) or (node.targets[0] if isinstance(node, ast.Assign) else None)
        if isinstance(target, ast.Name) and target.id == "RESULT_FIELDS":
            return [call for call in ast.walk(node.value) if isinstance(call, ast.Call)
                    and isinstance(call.func, ast.Name) and call.func.id == "OutputField"]
    raise AssertionError("RESULT_FIELDS not found")


#: 読み方の中で呼んでよい集計（authority 後は準備済みの `cause_evidence` と schema で
#: 行数が有界な canonical reason だけから組む。trace 由来の部分は authority 前に
#: 診断用の作業量で数えながら作る。出力は TRUNCATE）
_KNOWN_EAGER_READERS = frozenset({"RESULT_FIELDS[unknown_cause_aggregate]"})

#: `json_items` の中で identity key をそのまま写す site（key の owner は identity）。
#: return 値の flow certificate の key は RETURN の def-chain の辿った辺の数だけの組で、
#: 旧 `to_dict` と同じ値。identity key を eager に作る問題の owner は別 Issue（PR 本文の残件）。
#: 6 回目: `ReturnInfo.json_items` の証明書の key は owner の `identity_key_of`（#194。呼ぶ場所は
#: `test_issue22d_capabilities.py` の J19 が固定する）で読む: `stable_key()` を直接呼ぶ producer は無い
_KNOWN_IDENTITY_KEY_COPIES: frozenset = frozenset()


def _reader_nodes() -> List[Tuple[str, ast.AST]]:
    """出力 field の読み方（lambda / 関数）と、package の全 `json_items`。"""
    path = PACKAGE_ROOT / "checker/output_preparation.py"
    tree = _parse(path)
    functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    nodes: List[Tuple[str, ast.AST]] = []
    for call in _output_field_rows(tree):
        reader = call.args[2]
        key = call.args[0]
        label = getattr(key, "value", getattr(key, "id", "?"))
        if isinstance(reader, ast.Lambda):
            nodes.append((f"RESULT_FIELDS[{label}]", reader))
        elif isinstance(reader, ast.Name):
            nodes.append((f"RESULT_FIELDS[{label}]", functions[reader.id]))
        elif isinstance(reader, ast.Call) and isinstance(reader.func, ast.Name) and reader.func.id == "_function":
            # 登録した読み方の関数（`_read_by_function` が名前で呼ぶ `_<name>`）
            nodes.append((f"RESULT_FIELDS[{label}]", functions["_" + reader.args[0].value]))
        elif isinstance(reader, ast.Call) and isinstance(reader.func, ast.Name):
            nodes.append((f"RESULT_FIELDS[{label}]", functions[reader.func.id]))
    for module in _module_files():
        for node in ast.walk(_parse(module)):
            if isinstance(node, ast.FunctionDef) and node.name in {"json_items", "_json_items"}:
                nodes.append((f"{_relative(module)}:json_items@{node.lineno}", node))
    return nodes


def test_producers_return_json_sources_and_never_build_the_representation():
    """J1: producer は参照と遅延構成子だけを返す（`to_dict()`・複製・内包表記をしない）。"""

    nodes = _reader_nodes()
    assert sum(1 for label, _node in nodes if "json_items" in label) >= 80
    assert any(label.startswith("RESULT_FIELDS[debug_trace]") for label, _node in nodes)
    offenders = {}
    identity_copies = set()
    for label, node in nodes:
        if label in _KNOWN_EAGER_READERS:
            continue
        found = []
        for item in _eager_constructions(node):
            if item.startswith("stable_key()") and label.startswith("core/analysis.py:json_items"):
                identity_copies.add("core/analysis.py:ReturnInfo.stable_key()")
                continue
            found.append(item)
        if found:
            offenders[label] = found
    assert offenders == {}, offenders
    assert identity_copies == set(_KNOWN_IDENTITY_KEY_COPIES)


#: J2 の例外（`to_dict()` を持つが `json_items()` を持たない class）。理由つきで固定する。
#: 出力・snapshot に届かない報告 / authority の内部表現と、pure layer の固定の形の record。
_TO_DICT_WITHOUT_JSON_ITEMS = {
    # authority の lifecycle / receipt の内部表現（出力は authority の payload 関数が作る）
    "authority/lifecycle/pilot.py", "authority/process/supervisor.py",
    # log を読む側（run 後の集計。live な解析 object を持たない）
    "reporting/unknown_reason_summary.py", "reporting/timeout_hotspot_summary.py",
    "reporting/root_blocker_summary.py", "reporting/result_summary.py",
    "core/stage_journal_reader.py", "checker/cause_aggregate.py",
    # proof の内部の証拠（出力へは producer が組んだ dict として入る）
    "proof/recurrence_promotion.py", "proof/call_effect/preflight.py",
    "proof/call_effect/candidates.py", "proof/call_effect/obligations.py",
    "proof/formula/variable.py",
    # 結果 object 自身（出力は `RESULT_FIELDS` が決める）
    "checker/result.py",
}


def test_every_serialized_record_exposes_its_json_items():
    """J2: record の層で `to_dict()` を持つ class は `json_items()` も持つ。"""

    offenders = []
    for path in _module_files():
        relative = _relative(path)
        if relative in _TO_DICT_WITHOUT_JSON_ITEMS or relative.startswith("tests/"):
            continue
        for node in ast.walk(_parse(path)):
            if not isinstance(node, ast.ClassDef):
                continue
            methods = {item.name for item in node.body if isinstance(item, ast.FunctionDef)}
            if "to_dict" in methods and not ({"json_items", "__json_tree__"} & methods):
                offenders.append(f"{relative}:{node.name}")
    assert offenders == [], offenders


def test_pure_layer_records_keep_to_dict_equal_to_their_json_items():
    """pure layer（project を import しない）の固定の形の record は `to_dict()` を手で持つ。

    その値が `json_items()` の LEGACY 表現と同じであることを固定する（schema は 1 つ）。
    """

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY
    from scripts.function_tracer_pcode.proof.cause_identity import (
        ProofRequirementContract,
        ProofRequirementId,
        UnaryCauseKey,
    )
    from scripts.function_tracer_pcode.proof.unknown_reason import (
        UnknownRecoveryPlan,
        UnknownRecoveryProofObligation,
    )

    obligation = UnknownRecoveryProofObligation.create(
        "call_effect_summary", "stage", required_evidence=("a", "b"), description="d",
    )
    samples = (
        obligation,
        UnknownRecoveryPlan.create("unknown", (obligation,), target_regression="t"),
        ProofRequirementId.create("k", ("target", 1), ProofRequirementContract("c")),
        UnaryCauseKey("kind", ("domain",), ("object",), ("fact",)),
    )
    for sample in samples:
        assert RESULT_JSON_POLICY.materialize(sample) == sample.to_dict(), type(sample)


def test_the_snapshot_representation_is_built_only_through_the_work():
    """J3: 解析 1 件分の表現は、walker が直列化の作業量（`SerializationWork`）で数えながら作る。"""

    analysis = _parse(PACKAGE_ROOT / "core/analysis.py")
    (body,) = [
        node for node in ast.walk(analysis)
        if isinstance(node, ast.FunctionDef) and node.name == "_materialize"
    ]
    scopes = [
        inner for inner in ast.walk(body)
        if isinstance(inner, ast.Call) and getattr(inner.func, "id", None) == "serialization_scope"
    ]
    assert len(scopes) == 1
    builds = [
        inner for inner in ast.walk(body)
        if isinstance(inner, ast.Call) and getattr(inner.func, "attr", None) == "materialize"
    ]
    assert len(builds) == 1
    (build,) = builds
    assert [keyword.arg for keyword in build.keywords] == ["budget"]
    assert isinstance(build.keywords[0].value, ast.Name) and build.keywords[0].value.id == "work"


def test_json_framing_and_separators_live_only_in_the_policy():
    """区切りの長さ・framing の勘定は `JsonEncodingPolicy` だけが持つ。"""

    offenders = []
    for path in _module_files():
        relative = _relative(path)
        if relative == "core/json_encoding.py":
            continue
        for node in ast.walk(_parse(path)):
            if isinstance(node, ast.Attribute) and node.attr in {
                "item_separator", "key_separator", "separators",
            }:
                offenders.append(f"{relative}:{node.lineno} .{node.attr}")
    assert offenders == [], offenders


def test_prepared_json_is_created_only_by_the_policy():
    creators = set()
    for path in _module_files():
        for node in ast.walk(_parse(path)):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "PreparedJson"
            ):
                creators.add(_relative(path))
    assert creators == {"core/json_encoding.py"}, creators


def test_the_post_decision_lane_runs_in_its_own_failure_scope():
    """authority 確定後の proof は、pair と別の台帳の中でだけ走る。"""

    tree = _parse(PACKAGE_ROOT / "authority/decision/conditional_lane.py")
    calls, isolated = [], []

    def _visit(node, inside):
        if isinstance(node, ast.With):
            opens = any(
                isinstance(item.context_expr, ast.Call)
                and getattr(item.context_expr.func, "id", None) == "post_decision_failure_scope"
                for item in node.items
            )
            inside = inside or opens
        if isinstance(node, ast.Call) and getattr(node.func, "id", None) == "run_conditional_proof":
            calls.append(node.lineno)
            if inside:
                isolated.append(node.lineno)
        for child in ast.iter_child_nodes(node):
            _visit(child, inside)

    _visit(tree, False)
    assert calls and calls == isolated, (calls, isolated)


def test_prepared_readers_read_only_the_declared_source_attributes():
    """A の読み方が読む結果の属性 = 準備後に差し替えを拒む属性（`PREPARED_SOURCE_ATTRIBUTES`）。"""

    from scripts.function_tracer_pcode.checker.output_preparation import (
        PREPARED_SOURCE_ATTRIBUTES,
    )

    tree = _parse(PACKAGE_ROOT / "checker/output_preparation.py")
    functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    read = set()
    for call in _output_field_rows(tree):
        if getattr(call.args[1], "id", None) != "_A":
            continue
        reader = call.args[2]
        if isinstance(reader, ast.Call):  # `_when_present("name")` など
            read.add(reader.args[0].value)
            continue
        node = reader if isinstance(reader, ast.Lambda) else functions[reader.id]
        for inner in ast.walk(node):
            if (
                isinstance(inner, ast.Attribute)
                and isinstance(inner.value, ast.Name)
                and inner.value.id == "r"
            ):
                read.add(inner.attr)
    methods = {"get_effective_function1_signature", "get_effective_function2_signature"}
    assert read - methods <= PREPARED_SOURCE_ATTRIBUTES, read - methods - PREPARED_SOURCE_ATTRIBUTES
    # 準備が読まない属性を宣言しない（smt_formula は成果物として準備する）
    declared_extra = PREPARED_SOURCE_ATTRIBUTES - read - {
        "effective_function1_signature", "effective_function2_signature", "smt_formula",
    }
    assert declared_extra == set(), declared_extra


# ---------------------------------------------------------------------------
# Issue #22 PR-22-D（4 回目）: 有界化する処理そのものが有界であること
# ---------------------------------------------------------------------------
#
# 入力の大きさに比例する作業（容器の複製・並べ替え・digest・canonical 化・書き出し）は、
# 上限（`work` / `max_bytes`）を受け取る **登録された有界化の primitive** の中だけで行う。
# primitive 以外の code は、primitive が有界にした値しか受け取らない。規則は次の 6 つ:
#
# J4 primitive は上限を必須の keyword-only 引数で受け取る（既定値なし = 上限を知らずに呼べない）
# J5 PR-22-D の module と関数で、並べ替え・hash・canonical 化・`dumps` を行う場所は登録の中だけ
# J6 有界な証拠（`BoundedEvidence`）を作るのは唯一の owner（`core/json_encoding`）だけ
# J7 上限なしの予算（`JsonBudget(None)` / `BudgetPolicy.unlimited()`）は登録した場所だけ
# J8 digest / fingerprint の等しさを値の等しさ（⇔ / iff）として述べない
# J9 `json_items` の中で集計（`sum` / `max` / `min` / `any` / `all`）をしない（集計は `scan`）。
#    `json_items` が呼ぶ同じ module の helper も同じ（helper へ移しても規則を外れない）
# J10 walker を上限なしで回す呼び出し（`prepare` / `measure` に `max_bytes` 無し、`materialize`
#    に `budget` 無し）は登録した場所だけ（J7 の、予算を作らずに上限なしで辿る形）

#: J4: 有界化の primitive と、上限を受け取る引数（必須の keyword-only）
_BOUNDING_PRIMITIVES = (
    ("core/canonical_digest.py", "canonical_fingerprint", "work"),
    ("core/json_encoding.py", "bounded_evidence", "work"),
    ("core/json_encoding.py", "bounded_text", "work"),
    ("core/json_encoding.py", "cached_string_bytes", "max_bytes"),
    ("core/json_encoding.py", "JsonEncodingPolicy.token_fingerprint", "work"),
    ("checker/unknown_reason.py", "bounded_prefix", "work"),
    ("checker/unknown_reason.py", "finitize_unknown_reason_record", "work"),
    ("checker/unknown_reason.py", "finitize_unknown_recovery_action", "work"),
    ("checker/unknown_reason.py", "build_projection_diagnostic", "work"),
    ("checker/unknown_reason.py", "_match_legacy_reasons", "work"),
    ("checker/unknown_reason.py", "_bounded_cause_value", "work"),
    ("checker/output_preparation.py", "finitize_legacy_reasons", "authority_projects_reasons"),
)

#: J5 の対象: PR-22-D が所有する module 全体と、他の module の中の PR-22-D の関数 / class
_PR22D_MODULES = (
    "core/json_encoding.py", "core/canonical_digest.py", "core/budget_policy.py",
    "checker/output_preparation.py", "checker/output_schema.py",
)
_PR22D_FUNCTIONS = {
    "checker/unknown_reason.py": {
        "bounded_prefix", "finitize_unknown_reason_record", "finitize_unknown_recovery_action",
        "_bounded_value", "_bounded_text", "_match_legacy_reasons", "build_projection_diagnostic",
        "_bounded_cause_value", "projection_diagnostic_work", "_ReasonCounts", "_RecoveryBacklog",
        "_BacklogEntryView", "_PrimaryFilter", "LegacyReasonIndex", "legacy_reason_index", "_text_cost", "_LegacyReasonGroup", "_inline_canonical", "_canonical_summary", "_coerce_record_within",
        "recovery_actions_source", "_iter_recovery_actions", "_key_width",
    },
    "checker/cause_aggregate.py": {
        "_counted", "reason_detail_key", "attach_cause_aggregate", "_payload_occurrence_views",
        "_prepared_within_work",
    },
    "checker/diagnostics.py": {
        "TraceTimingsView", "_SolverTotals", "trace_timings_payload", "_solver_rows", "_attempt_rows",
        "_ResultDiagnosticsView",
    },
    "checker/debug_trace.py": {"_PhaseUsageFold"},
}
#: J5 で数える呼び出し（入力に比例し得る並べ替え・hash・canonical 化・書き出し）
_BOUNDED_WORK_NAMES = frozenset({"sorted", "canonical_value", "authority_digest"})
_BOUNDED_WORK_ATTRS = frozenset({"sort", "dumps", "sha256", "blake2b", "md5", "sha1"})
#: J5 の登録: (module, 関数の qualname, 呼び出し) → なぜ有界か
_REGISTERED_BOUNDED_WORK = {
    ("core/json_encoding.py", "JsonEncodingPolicy.dumps", "dumps"):
        "policy の書き出し（呼ぶ側が大きさを確かめた小さい値だけ。見積りは文字列の長さを先に数える）",
    ("core/json_encoding.py", "JsonEncodingPolicy.token_fingerprint", "sha256"):
        "token 列の hash（流す token は walker が `work` へ数える）",
    ("core/json_encoding.py", "_printable_identity", "sha256"):
        "96 文字以下に切った identity の hash",
    ("core/json_encoding.py", "_window_sha256", "sha256"):
        "長さと先頭・末尾の窓（`2 * TEXT_MARKER_WINDOW_CHARS` 文字）だけの hash",
    ("core/json_encoding.py", "_string_sha256", "sha256"):
        "長い文字列の marker の hash（`bounded_text` が長さを `work` へ数えてから呼ぶ）",
    ("core/json_encoding.py", "_Walk.push", "sort"):
        "token digest の dict の並べ替え（引き出す 1 組ごとに予算へ数えてから）",
    ("core/canonical_digest.py", "_json_key", "dumps"): "float 1 つの key",
    ("core/canonical_digest.py", "_Sink.__init__", "sha256"): "流す byte は `emit` が `work` へ数える",
    ("core/canonical_digest.py", "_Sink.emit_leaf", "dumps"): "float 1 つ",
    ("core/canonical_digest.py", "_emit", "sort"): "set の要素（幅を `work` へ数え、要素の JSON も数え済み）",
    ("core/canonical_digest.py", "_pairs", "sort"): "mapping の組（幅を `work` へ数えてから）",
    ("core/canonical_digest.py", "_push_raw_container", "sorted"): "enum の値の dict（幅を `work` へ数えてから）",
    ("core/budget_policy.py", "BudgetObservations.snapshot", "sorted"): "観測点（予算の種類 × site）の固定の語彙",
    ("checker/output_preparation.py", "SerializationPlan.to_diagnostic", "sorted"): "RESULT_FIELDS の固定の field",
    ("checker/output_preparation.py", "OutputPreparer.prepare", "sort"): "RESULT_FIELDS の固定の field",
    ("checker/output_preparation.py", "_ordered", "sorted"): "RESULT_FIELDS の固定の key",
    ("checker/unknown_reason.py", "_canonical_summary", "canonical_value"):
        "`bounded_evidence` の結果だけ（plain な小さい値か、固定の形の要約を持つ `BoundedEvidence`）",
    ("checker/unknown_reason.py", "_bounded_cause_value", "canonical_value"):
        "`bounded_evidence` が inline の上限以下と確かめた plain な値だけ",
    ("checker/unknown_reason.py", "_match_legacy_reasons", "sorted"):
        "索引で一致した位置（件数は索引に入れた record 以下で、索引を作るときに数え済み）",
    ("checker/unknown_reason.py", "_inline_canonical", "canonical_value"):
        "大きさを `work` へ数えた後の、有界化で inline のまま残った小さい値だけ（索引を作るとき 1 回）",
}
#: J7 の登録: 上限なしの予算を作ってよい場所 → なぜ
_REGISTERED_UNBOUNDED_BUDGETS = {
    ("core/json_encoding.py", "JsonEncodingPolicy.materialize"):
        "予算 scope の外（部品単体の呼び出し）の `to_dict()`。pair の中は `materialize()` が作業量を渡す",
    ("core/json_encoding.py", "_canonical_copy_uncounted"): "`tree()` が作る前に数え済みの木の canonical な複製",
    ("core/budget_policy.py", "<module>"): "予算を無効にした policy（`FT_*` で制限だけを外す。構造は同じ）",
    ("checker/cause_aggregate.py", "reason_detail_key"): "作業量の scope の外（部品単体の呼び出し）だけ",
    ("checker/debug_trace.py", "DebugTrace._iter_phase_usage"):
        "人向けの phase 利用の一覧（出力の準備の外。出力は `phase_usage_source` が walk の作業量で畳む）",
    ("checker/unknown_reason.py", "iter_unknown_recovery_actions"):
        "producer 時点（出力の前）の構築。出力の行数は finitize が判定の前に schema と比べ、出力は "
        "`recovery_actions_source` が walk の作業量へ数える",
}


def _qualified_calls(path: pathlib.Path, only: Optional[Set[str]] = None):
    """(qualname, 呼び出し名, 行, Call) を返す（`only` があれば top-level の名前で絞る）。"""

    tree = _parse(path)
    found = []

    def visit(node, qual):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                visit(child, qual + [child.name])
                continue
            if isinstance(child, ast.Call):
                func = child.func
                name = func.id if isinstance(func, ast.Name) else (
                    func.attr if isinstance(func, ast.Attribute) else None
                )
                if name is not None and (only is None or (qual and qual[0] in only)):
                    found.append((".".join(qual) or "<module>", name, child.lineno, child))
            visit(child, qual)

    visit(tree, [])
    return found


def _j5_targets():
    for relative in _PR22D_MODULES:
        yield relative, None
    for relative, names in _PR22D_FUNCTIONS.items():
        yield relative, names


def test_j4_bounding_primitives_require_their_bound():
    for relative, qualname, parameter in _BOUNDING_PRIMITIVES:
        tree = _parse(PACKAGE_ROOT / relative)
        node = tree
        for part in qualname.split("."):
            node = next(
                item for item in ast.iter_child_nodes(node)
                if isinstance(item, (ast.FunctionDef, ast.ClassDef)) and item.name == part
            )
        kwonly = {arg.arg: default for arg, default in zip(node.args.kwonlyargs, node.args.kw_defaults)}
        assert parameter in kwonly, f"{relative}:{qualname} must take keyword-only {parameter!r}"
        assert kwonly[parameter] is None, f"{relative}:{qualname}.{parameter} must have no default"


def test_j5_input_proportional_work_happens_only_in_registered_primitives():
    unexpected = []
    seen = set()
    for relative, names in _j5_targets():
        for qualname, name, lineno, call in _qualified_calls(PACKAGE_ROOT / relative, names):
            is_attr = isinstance(call.func, ast.Attribute)
            if (not is_attr and name in _BOUNDED_WORK_NAMES) or (is_attr and name in _BOUNDED_WORK_ATTRS):
                key = (relative, qualname, name)
                seen.add(key)
                if key not in _REGISTERED_BOUNDED_WORK:
                    unexpected.append(f"{relative}:{lineno} {qualname} calls {name}()")
    assert unexpected == [], unexpected
    stale = set(_REGISTERED_BOUNDED_WORK) - seen
    assert stale == set(), stale


def test_j6_only_the_owner_constructs_bounded_evidence():
    owners = set()
    for path in _module_files():
        relative = _relative(path)
        for qualname, name, lineno, call in _qualified_calls(path):
            # `BoundedEvidence(...)` も `json_encoding.BoundedEvidence(...)` も
            if name == "BoundedEvidence":
                owners.add(relative)
    assert owners == {"core/json_encoding.py"}, owners


def test_j7_unbounded_budgets_are_created_only_at_registered_sites():
    found = set()
    for path in _module_files():
        relative = _relative(path)
        for qualname, name, lineno, call in _qualified_calls(path):
            unbounded = (
                name == "JsonBudget" and call.args
                and isinstance(call.args[0], ast.Constant) and call.args[0].value is None
            ) or (name == "unlimited" and isinstance(call.func, ast.Attribute))
            if unbounded:
                found.add((relative, qualname))
    assert found == set(_REGISTERED_UNBOUNDED_BUDGETS), found ^ set(_REGISTERED_UNBOUNDED_BUDGETS)


_EQUALITY_CLAIM = re.compile(r"(digest|fingerprint|Merkle)[^\n]{0,60}(⇔|\biff\b)|(⇔|\biff\b)[^\n]{0,60}(digest|fingerprint)", re.I)


def test_j8_no_code_or_test_claims_digest_equality_is_value_equality():
    offenders = []
    roots = [PACKAGE_ROOT]
    for root in roots:
        for path in sorted(root.rglob("*.py")):
            if path.name == pathlib.Path(__file__).name:
                continue
            for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
                if _EQUALITY_CLAIM.search(line):
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{lineno}")
    assert offenders == [], offenders


_AGGREGATE_BUILTINS = frozenset({"sum", "max", "min", "any", "all"})


def _json_items_closure(tree: ast.Module) -> List[Tuple[str, ast.AST]]:
    """`json_items` と、そこから（推移的に）呼ばれる同じ module の関数 / 同じ class の method。"""

    functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    found: List[Tuple[str, ast.AST]] = []
    seen: Set[int] = set()

    def add(label: str, node: ast.AST, methods: dict) -> None:
        if id(node) in seen:
            return
        seen.add(id(node))
        found.append((label, node))
        for inner in ast.walk(node):
            if not isinstance(inner, ast.Call):
                continue
            func = inner.func
            if isinstance(func, ast.Name) and func.id in functions:
                add(func.id, functions[func.id], {})
            elif (
                isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                and func.value.id == "self" and func.attr in methods
            ):
                add(f"{label.split('.')[0]}.{func.attr}", methods[func.attr], methods)

    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            methods = {item.name: item for item in node.body if isinstance(item, ast.FunctionDef)}
            if "json_items" in methods:
                add(f"{node.name}.json_items", methods["json_items"], methods)
    return found


def _over_literal(arg: ast.AST) -> bool:
    """固定個数の列（tuple / list の literal）だけを辿る内包表記・literal そのもの。"""

    if isinstance(arg, (ast.Tuple, ast.List)):
        return True
    if isinstance(arg, (ast.GeneratorExp, ast.ListComp, ast.SetComp)):
        return all(isinstance(generator.iter, (ast.Tuple, ast.List)) for generator in arg.generators)
    return False


def _aggregations(node: ast.AST) -> List[int]:
    lines = []
    for inner in ast.walk(node):
        if (
            isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name)
            and inner.func.id in _AGGREGATE_BUILTINS
            # 集計 = 列 1 つを畳む呼び出し（`max(1, x)` のような scalar どうしは除く）
            and (len(inner.args) == 1 or any(
                isinstance(arg, (ast.GeneratorExp, ast.ListComp, ast.SetComp))
                for arg in inner.args
            ))
            # 固定個数の literal を畳むのは入力に比例しない
            and not all(_over_literal(arg) for arg in inner.args)
        ):
            lines.append(inner.lineno)
    return lines


#: J9 の登録: `json_items` の helper で集計してよい場所 → なぜ有界か
_REGISTERED_JSON_ITEMS_AGGREGATIONS: Dict[Tuple[str, str], str] = {}


def test_j9_json_items_do_not_aggregate_collections():
    offenders = []
    seen = set()
    for path in _module_files():
        relative = _relative(path)
        for label, node in _json_items_closure(_parse(path)):
            for lineno in _aggregations(node):
                key = (relative, label)
                seen.add(key)
                if key not in _REGISTERED_JSON_ITEMS_AGGREGATIONS:
                    offenders.append(f"{relative}:{lineno} {label}")
    assert offenders == [], offenders
    assert set(_REGISTERED_JSON_ITEMS_AGGREGATIONS) - seen == set()


def test_j9_reaches_the_helpers_json_items_calls():
    tree = ast.parse(
        "def helper(rows):\n    return sum(rows)\n\n"
        "class R:\n    def json_items(self):\n        yield 'n', self._n()\n"
        "    def _n(self):\n        return helper(self.rows)\n"
    )
    labels = {label for label, node in _json_items_closure(tree) if _aggregations(node)}
    assert labels == {"helper"}
    fixed = ast.parse("def f(x):\n    return any(getattr(x, a) for a in ('p', 'q'))\n")
    assert _aggregations(fixed) == []


#: J1 の推移的な形: `json_items` が呼ぶ helper で表現を先に作ってよい場所 → なぜ有界か
_REGISTERED_JSON_ITEMS_HELPER_BUILDS: dict = {}


def test_j1_helpers_json_items_calls_do_not_build_the_representation_either():
    """J1 の推移的な形: `json_items` から呼ばれる同じ module の helper も、表現を先に作らない。"""

    offenders = []
    seen = set()
    for path in _module_files():
        relative = _relative(path)
        for label, node in _json_items_closure(_parse(path)):
            if label.endswith(".json_items"):
                continue  # json_items 自身は J1 が見る
            if _eager_constructions(node):
                key = (relative, label)
                seen.add(key)
                if key not in _REGISTERED_JSON_ITEMS_HELPER_BUILDS:
                    offenders.append(f"{relative}:{label} {_eager_constructions(node)[:4]}")
    assert offenders == [], offenders
    assert set(_REGISTERED_JSON_ITEMS_HELPER_BUILDS) - seen == set()


#: J10 の登録: walker を上限なしで回してよい場所 → なぜ
_REGISTERED_UNBOUNDED_WALKS = {
    ("core/json_encoding.py", "materialize"): "予算 scope の外（部品単体の呼び出し）の `to_dict()`",
    ("core/expression.py", "Expression._serialize_runtime_ref"):
        "木を作る前に runtime ref を含む大きさを数え終えている（`estimate_legacy_dict_bytes`）",
    ("checker/cause_aggregate.py", "_prepared_within_work"): "作業量の scope の外（部品単体の呼び出し）だけ",
    ("checker/output_preparation.py", "OutputPreparer._prepare_cause_evidence"):
        "scalar だけの固定の形の marker",
    ("checker/output_preparation.py", "OutputPreparer._prepare_trace_timings"):
        "scalar だけの固定の形の marker（`_truncation_marker`。schema の上限あり）",
    ("checker/output_preparation.py", "OutputPreparer._prepare_limitation_evidence"):
        "scalar だけの固定の形の marker",
    ("checker/diagnostics.py", "result_diagnostics_payload"):
        "直接の読み手（出力の外）の canonical な dict。出力の準備は `lazy=True` の view を上限の中で辿る",
}
_WALK_BOUNDS = {"prepare": "max_bytes", "measure": "max_bytes", "materialize": "budget", "plain_bytes": "max_bytes"}


def _is_json_policy(receiver: ast.AST) -> bool:
    """JSON の policy と読める receiver（名前の一覧ではなく形で: `*_JSON_POLICY`・`encoding`・`policy`）。"""

    text = ast.unparse(receiver)
    last = text.rsplit(".", 1)[-1]
    return last.endswith("JSON_POLICY") or last in {"encoding", "policy", "_policy", "_encoding"}


def _bounded_by(call: ast.Call, keyword_name: str) -> bool:
    """`keyword_name=` を **None でない値で** 渡しているか（`max_bytes=None` は上限なし）。"""

    for keyword in call.keywords:
        if keyword.arg == keyword_name:
            return not (isinstance(keyword.value, ast.Constant) and keyword.value.value is None)
    return False


def test_j10_unbounded_walks_happen_only_at_registered_sites():
    found = set()
    for path in _module_files():
        relative = _relative(path)
        for qualname, name, lineno, call in _qualified_calls(path):
            bound = _WALK_BOUNDS.get(name)
            if (
                bound is not None and isinstance(call.func, ast.Attribute)
                and _is_json_policy(call.func.value)
                and not _bounded_by(call, bound)
            ):
                found.add((relative, qualname))
    assert found == set(_REGISTERED_UNBOUNDED_WALKS), found ^ set(_REGISTERED_UNBOUNDED_WALKS)


# ---------------------------------------------------------------------------
# Issue #22 PR-22-D（5 回目）: bounded path から呼べる callback を protocol に限る
# ---------------------------------------------------------------------------
#
# J11 walker が要素ごとに呼ぶ変換（`each` / `mapping_of` の `fn`、`Column(legacy=)`）は登録した
#     source converter（`@source_converter`、または `source_converter(lambda ...)`）だけ。
#     converter の本体は表現を先に作らない（J1 と同じ規則）
# J12 `scan` の reducer は `Reducer` の subclass で、`add` / `result` は作業量（`work`）を
#     keyword-only で受け取る。`cost` のような「呼ぶ側が O(1) にする約束」の callback は持たない
# J13 identity key（`stable_key()` / `to_key()`）を呼ぶのは `identity_key_of` だけ。PR-22-D の
#     module と関数から `to_authority_dict()` を呼ばない（固定の形の要約は `BoundedEvidence.summary` だけ）
# J14 最終 envelope の封印を作るのは `AuthoritySeal` だけ（production の subclass を作らない）
# J15 有界な証拠の identity は文字列（callable を受けない）
# J16 作業量（`JsonBudget`）を作ってよい場所は登録した場所だけ（helper が親の作業量から逃れる
#     新しい予算を作らない）

_SOURCE_CONSTRUCTORS = frozenset({
    "each", "nested", "as_list", "as_dict", "mapping_of", "pairs_of", "inline", "raw", "text", "evidence",
})


def _decorated_converters() -> Set[str]:
    names = set()
    for path in _module_files():
        for node in ast.walk(_parse(path)):
            if isinstance(node, ast.FunctionDef) and any(
                (isinstance(d, ast.Name) and d.id == "source_converter") for d in node.decorator_list
            ):
                names.add(node.name)
    return names


def _callback_arguments(tree: ast.AST):
    """(行, 呼び出し名, callback の式) を返す（each / mapping_of の 2 番目、Column の legacy=）。"""

    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        name = func.id if isinstance(func, ast.Name) else (func.attr if isinstance(func, ast.Attribute) else None)
        if name in {"each", "mapping_of", "pairs_of"}:
            if len(node.args) >= 2:
                yield node.lineno, name, node.args[1]
            for keyword in node.keywords:
                if keyword.arg == "fn":
                    yield node.lineno, name, keyword.value
        if name == "Column":
            for keyword in node.keywords:
                if keyword.arg == "legacy":
                    yield node.lineno, name, keyword.value


def test_j11_walker_callbacks_are_registered_source_converters():
    converters = _decorated_converters() | _SOURCE_CONSTRUCTORS
    offenders = []
    for path in _module_files():
        relative = _relative(path)
        for lineno, name, callback in _callback_arguments(_parse(path)):
            if isinstance(callback, ast.Constant) and callback.value is None:
                continue
            if isinstance(callback, (ast.Name, ast.Attribute)):
                label = callback.id if isinstance(callback, ast.Name) else callback.attr
                if label in converters or label in {"_RAW", "_NESTED"}:
                    continue
            if (
                isinstance(callback, ast.Call) and getattr(callback.func, "id", None) == "source_converter"
                and callback.args and isinstance(callback.args[0], ast.Lambda)
                and not _eager_constructions(callback.args[0])
            ):
                continue
            offenders.append(f"{relative}:{lineno} {name}({ast.unparse(callback)[:60]})")
    assert offenders == [], offenders


#: converter（と、そこから呼ぶ同じ module の helper）が呼んではいけない、値を文字列にする組み込み
#: （`__str__` / `__repr__` / `__format__` は live な値の producer。`bounded_repr` / `builtin_str` を使う）
_RENDERING_BUILTINS = frozenset({"str", "repr", "format", "hash", "ascii"})


def _is_type_name(node: ast.AST) -> bool:
    """`type(x).__qualname__` / `type(x).__module__`（型の名前。値の producer を呼ばない）。"""

    return (
        isinstance(node, ast.Attribute) and node.attr in {"__qualname__", "__module__", "__name__"}
        and isinstance(node.value, ast.Call) and getattr(node.value.func, "id", None) == "type"
    )


def _rendering_calls(node: ast.AST) -> List[str]:
    found = []
    for inner in ast.walk(node):
        if isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name) and inner.func.id in _RENDERING_BUILTINS:
            found.append(f"{inner.func.id}()@{inner.lineno}")
        elif isinstance(inner, ast.FormattedValue) and not _is_type_name(inner.value):
            found.append(f"f-string@{inner.value.lineno}")
    return found


def _takes_work(function: ast.FunctionDef) -> bool:
    arguments = function.args
    return any(arg.arg == "work" for arg in (*arguments.args, *arguments.kwonlyargs))


def _converter_closure(tree: ast.Module, roots: List[ast.AST]) -> List[ast.AST]:
    """converter の本体と、そこから名前で呼ぶ同じ module の top-level 関数（作業量を受け取らないもの）。

    作業量（`work`）を受け取る helper は数えながら辿る側の関数で、J5 の規則が本体を見る。
    """

    functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    pending = list(roots)
    closure: List[ast.AST] = []
    seen: Set[int] = set()
    while pending:
        node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        closure.append(node)
        for inner in ast.walk(node):
            if isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name):
                callee = functions.get(inner.func.id)
                if callee is not None and not _takes_work(callee):
                    pending.append(callee)
    return closure


def test_j11_source_converters_do_not_build_the_representation():
    """converter と、それが呼ぶ同じ module の helper は、表現を作らず値を文字列にしない（呼び先まで辿る）。"""

    offenders = []
    for path in _module_files():
        relative = _relative(path)
        tree = _parse(path)
        roots: List[ast.AST] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and any(
                isinstance(d, ast.Name) and d.id == "source_converter" for d in node.decorator_list
            ):
                roots.append(node)
            elif (
                isinstance(node, ast.Call) and getattr(node.func, "id", None) == "source_converter"
                and node.args and isinstance(node.args[0], ast.Lambda)
            ):
                roots.append(node.args[0])
        for node in _converter_closure(tree, roots):
            found = _eager_constructions(node) + _rendering_calls(node)
            if found:
                label = getattr(node, "name", f"<lambda>@{getattr(node, 'lineno', '?')}")
                offenders.append(f"{relative}:{label} {found[:4]}")
    assert offenders == [], offenders


def test_j11_the_walker_refuses_unregistered_callbacks_at_construction():
    from scripts.function_tracer_pcode.core.json_encoding import Column, TEXT, each, evidence, mapping_of

    def plain(value):
        return value

    for construct in (
        lambda: each([1], plain),
        lambda: mapping_of({}, plain),
        lambda: Column("k", TEXT, 8, legacy=plain),
        lambda: evidence((1,), identity=lambda _value: "x"),
    ):
        with pytest.raises(TypeError):
            construct()


def _reducer_classes():
    for path in _module_files():
        relative = _relative(path)
        for node in ast.walk(_parse(path)):
            if isinstance(node, ast.ClassDef) and any(
                (isinstance(base, ast.Name) and base.id == "Reducer") for base in node.bases
            ):
                yield relative, node


def test_j12_reducers_receive_the_work_and_declare_no_cost_callback():
    found = 0
    offenders = []
    for relative, node in _reducer_classes():
        found += 1
        methods = {item.name: item for item in node.body if isinstance(item, ast.FunctionDef)}
        if "cost" in methods:
            offenders.append(f"{relative}:{node.name}.cost")
        for name in ("add", "result"):
            method = methods.get(name)
            if method is None or "work" not in {arg.arg for arg in method.args.kwonlyargs}:
                offenders.append(f"{relative}:{node.name}.{name} does not take keyword-only work")
    assert found >= 5 and offenders == [], offenders


#: J17 の例外（reducer の `add` が要素の値を直接 key にしてよい理由）
_REDUCER_KEY_CHECKED = {
    ("core/json_encoding.py", "Tally"): "key は scalar だけ（型を確かめてから hash し、文字列は長さを数える）",
}
#: key として hash してよい値を作る関数（hash する前に数え、組み込みの値だけを値で比べる）
_HASHABLE_KEY_FACTORIES = frozenset({"hashable_key", "builtin_str"})


def _key_expressions(function: ast.FunctionDef):
    """`add` の中で hash される key の式（添字・`in`・`get` / `add` / `setdefault` / `pop` / `discard`）。"""

    for node in ast.walk(function):
        if isinstance(node, ast.Subscript) and not (
            isinstance(node.value, ast.Name) and node.value.id == "self"
        ):
            yield node.slice
        elif isinstance(node, ast.Compare) and any(isinstance(op, (ast.In, ast.NotIn)) for op in node.ops):
            yield node.left
        elif (
            isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in {"get", "add", "setdefault", "pop", "discard"} and node.args
            # 作業量を受け取る `add`（入れ子の reducer・entry）は hash しない: その本体が数える
            and not any(keyword.arg == "work" for keyword in node.keywords)
        ):
            yield node.args[0]


def test_j17_reducers_hash_only_keys_made_for_hashing():
    """reducer の `add` は、要素の値を直接 hash しない（`hashable_key` / `builtin_str` の値か定数だけ）。"""

    offenders = []
    for relative, node in _reducer_classes():
        if (relative, node.name) in _REDUCER_KEY_CHECKED:
            continue
        methods = {item.name: item for item in node.body if isinstance(item, ast.FunctionDef)}
        add = methods.get("add")
        if add is None:
            continue
        made: Set[str] = set()
        for inner in ast.walk(add):
            if (
                isinstance(inner, ast.Assign) and isinstance(inner.value, ast.Call)
                and getattr(inner.value.func, "id", None) in _HASHABLE_KEY_FACTORIES
            ):
                made.update(target.id for target in inner.targets if isinstance(target, ast.Name))
        for key in _key_expressions(add):
            if isinstance(key, ast.Constant):
                continue
            if isinstance(key, ast.Name) and key.id in made:
                continue
            if isinstance(key, ast.Call) and getattr(key.func, "id", None) in _HASHABLE_KEY_FACTORIES:
                continue
            offenders.append(f"{relative}:{node.name}.add hashes {ast.unparse(key)[:60]}@{key.lineno}")
    assert offenders == [], offenders


def test_j12_scan_refuses_anything_but_a_reducer():
    from scripts.function_tracer_pcode.core.json_encoding import Tally, scan

    class _Duck:
        def add(self, element, *, work):
            pass

        def result(self, *, work):
            return 0

    with pytest.raises(TypeError):
        scan([1], _Duck())
    with pytest.raises(TypeError):
        Tally(lambda element: element)


def test_j13_identity_keys_and_authority_producers_have_one_caller():
    offenders = []
    # `ExpansionBudgetTruncation.event_id` は identity の digest（owner #194。producer 時点で作って
    # cache し、出力の `json_items` は cache を読む）: 出力の側（`json_items`）だけを対象にする
    targets = list(_j5_targets()) + [("proof/obligations/snapshot.py", None), ("core/runtime_refs/unknowns.py", {
        # 出力の側の helper（切り捨て事実の identity は構築のときに作って cache する: #194）
        "_runtime_ref_origin_source", "_call_target_display_name", "_deferred_call_display_name",
    })]
    for relative, names in targets:
        for qualname, name, lineno, call in _qualified_calls(PACKAGE_ROOT / relative, names):
            if name in {"stable_key", "to_key"} and qualname != "identity_key_of":
                offenders.append(f"{relative}:{lineno} {qualname} calls {name}()")
            if name == "to_authority_dict":
                offenders.append(f"{relative}:{lineno} {qualname} calls to_authority_dict()")
    assert offenders == [], offenders
    from scripts.function_tracer_pcode.core import canonical_digest
    from scripts.function_tracer_pcode.core.json_encoding import BoundedEvidence

    # 固定の形の record は 1 つだけで、callable の登録表は持たない（要約は名前で呼ぶ）
    assert canonical_digest._bounded_evidence_type() is BoundedEvidence
    assert not hasattr(canonical_digest, "register_fixed_canonical")


def test_j14_the_final_envelope_is_sealed_only_by_the_authority_seal():
    subclasses = []
    constructions = set()
    for path in _module_files():
        relative = _relative(path)
        tree = _parse(path)
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and any(
                getattr(base, "id", None) == "AuthoritySeal" for base in node.bases
            ):
                subclasses.append(f"{relative}:{node.name}")
            if isinstance(node, ast.Call) and getattr(node.func, "id", None) == "AuthoritySeal":
                constructions.add(relative)
    assert subclasses == [], subclasses
    assert constructions == {"cli/commands/equivalence.py"}, constructions


def test_j15_bounded_evidence_identity_is_a_string():
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget, bounded_evidence

    with pytest.raises(TypeError):
        bounded_evidence(("x" * 5_000,), work=JsonBudget(1 << 20), identity=lambda _value: "cause:x")


#: J16 の登録: 作業量を作ってよい場所 → なぜ親の作業量から逃れないか
_REGISTERED_WORK_SCOPES = {
    ("core/json_encoding.py", "JsonEncodingPolicy.prepare"): "walk 1 つの予算（上限は呼ぶ側の `max_bytes`）",
    ("core/json_encoding.py", "JsonEncodingPolicy.measure"): "walk 1 つの予算（上限は呼ぶ側の `max_bytes`）",
    ("core/json_encoding.py", "JsonEncodingPolicy.materialize"): "J7 の登録（予算 scope の外の `to_dict()`）",
    ("core/json_encoding.py", "JsonEncodingPolicy.plain_bytes"): "walk 1 つの予算（上限は呼ぶ側の `max_bytes`）",
    ("core/json_encoding.py", "bounded_evidence"): "試しの予算（呼ぶ側の `work` の残り以下で、使った分を `work` へ戻す）",
    ("core/json_encoding.py", "_Walk.__init__"): "walk の作業量（上限は walk の byte 予算の残り）",
    ("core/json_encoding.py", "_Walk.enter_evidence"): "試しの予算（walk の作業量の残り以下で、使った分を作業量へ戻す）",
    ("core/json_encoding.py", "_canonical_copy_uncounted"): "J7 の登録（数え済みの木の複製）",
    ("checker/output_preparation.py", "OutputPreparer.prepare"): "診断の準備物が共有する予算（上限は headroom）",
    ("checker/output_preparation.py", "finitize_legacy_reasons"): "G4-b の作業量（上限は出力 schema の field の上限の和）",
    ("checker/unknown_reason.py", "projection_diagnostic_work"): "finish 1 回の診断の作業量（上限は出力 schema の reason の field）",
    ("checker/unknown_reason.py", "iter_unknown_recovery_actions"): "J7 の登録（producer 時点の構築）",
    ("checker/debug_trace.py", "DebugTrace._iter_phase_usage"): "J7 の登録（人向けの一覧）",
    ("checker/cause_aggregate.py", "reason_detail_key"): "J7 の登録（作業量の scope の外）",
}


def _work_scope_names(tree: ast.Module) -> Set[str]:
    """この module で `JsonBudget` を指す名前（`import ... as` の別名を含む）。"""

    names = {"JsonBudget"}
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name == "JsonBudget" and alias.asname:
                    names.add(alias.asname)
        elif isinstance(node, ast.Assign) and isinstance(node.value, ast.Name) and node.value.id in names:
            names.update(target.id for target in node.targets if isinstance(target, ast.Name))
    return names


def test_j16_work_scopes_are_created_only_at_registered_sites():
    """作業量を作る呼び出し（別名・`module.JsonBudget(...)` の形も）は登録した場所だけ。

    walk の中で作った作業量は実行時にもその walk の作業量の子になる（`JsonBudget.parent`。
    `test_issue22d_live_values.py` が固定する）。ここは作ってよい場所の一覧を固定する。
    """

    found = set()
    for path in _module_files():
        relative = _relative(path)
        names = _work_scope_names(_parse(path))
        for qualname, name, lineno, call in _qualified_calls(path):
            func = call.func
            if isinstance(func, ast.Name) and func.id in names:
                found.add((relative, qualname))
            elif isinstance(func, ast.Attribute) and func.attr == "JsonBudget":
                found.add((relative, qualname))
    assert found == set(_REGISTERED_WORK_SCOPES), found ^ set(_REGISTERED_WORK_SCOPES)


def test_j18_a_work_scope_opened_inside_a_walk_cannot_escape_it():
    """実行時の保証: walk の中では新しい作業量（別名でも、有限でも）を作れない（owner は walk の作業量 1 つ）。"""

    from scripts.function_tracer_pcode.core import json_encoding
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonValueRejected, Reducer, scan

    Alias = json_encoding.JsonBudget
    charged = []

    class _Escape(Reducer):
        def add(self, element, *, work):
            work.charge(1)

        def result(self, *, work):
            inner = Alias(1 << 40)
            for _ in range(10_000):
                inner.charge(10)
                charged.append(1)
            return "escaped"

    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(scan((0,), _Escape()), max_bytes=1_000)
    assert charged == []
