# -*- coding: utf-8 -*-
"""Issue #167: proof 層は比較の中の証拠を ``store_comparison_evidence`` だけで書く。

proof 層の producer は比較（最終 relation）の中で動き、その証拠は relation に束縛
されなければならない。束縛を producer ごとの約束にすると、新しい producer が忘れた
ときに別の relation の比較へ証拠が漏れても何も落ちない。そこで analysis への書き込み口を
1 つにし（``store_comparison_evidence`` が比較の中で増えた record を束縛する）、
proof 層でそれ以外の書き込みが増えたらこの test が落ちる。

例外は下の表だけで、各行に理由がある（表に無い書き込みを足すときは、まず
``store_comparison_evidence`` を使えないかを考える）。
"""

from __future__ import annotations

import ast
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[2]
PROOF = PACKAGE / "proof"
FIELD = "completed_recovery_proof_evidence"

#: (proof/ からの相対 path, 関数名) -> 理由
ALLOWED_WRITERS = {
    ("formula/input_correspondence/binding.py", "store_comparison_evidence"):
        "唯一の書き込み口（比較の中で増えた record を束縛する）",
    ("recurrence_promotion.py", "_prepare_side_for_proposal"):
        "unary（関数単体）の recurrence artifact を後継 analysis に載せる。pair の relation に依存しない",
    ("strategies/pairwise_services/orchestration.py", "_impl_check"):
        "analysis ではなく strategy 結果の payload。戻り幅の完了証拠を relation に明示的に束縛して載せる",
}


def _writes(tree: ast.AST):
    """``x.<FIELD> = ...`` / ``x.<FIELD> += ...`` / ``setattr(x, "<FIELD>", ...)`` の関数名。"""

    for function in ast.walk(tree):
        if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for node in ast.walk(function):
            targets = ()
            if isinstance(node, ast.Assign):
                targets = node.targets
            elif isinstance(node, (ast.AugAssign, ast.AnnAssign)):
                targets = (node.target,)
            for target in targets:
                for element in ast.walk(target):
                    if isinstance(element, ast.Attribute) and element.attr == FIELD:
                        yield function.name, node.lineno
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "setattr"
                and len(node.args) >= 2
                and isinstance(node.args[1], ast.Constant)
                and node.args[1].value == FIELD
            ):
                yield function.name, node.lineno


def _proof_writers():
    found = {}
    for path in sorted(PROOF.rglob("*.py")):
        relative = path.relative_to(PROOF).as_posix()
        for name, line in _writes(ast.parse(path.read_text(encoding="utf-8"))):
            found.setdefault((relative, name), []).append(line)
    return found


def test_proof_layer_writes_comparison_evidence_only_through_the_binding_writer():
    unexpected = {
        key: lines for key, lines in _proof_writers().items() if key not in ALLOWED_WRITERS
    }
    assert unexpected == {}, (
        "proof 層で completed_recovery_proof_evidence を直接書いている。"
        "store_comparison_evidence を使うこと: " + repr(unexpected)
    )


def test_the_allowed_writers_still_exist():
    assert set(ALLOWED_WRITERS) <= set(_proof_writers())


def test_the_guard_sees_every_form_of_write():
    source = '''
def assign(analysis):
    analysis.completed_recovery_proof_evidence = ()

def augmented(analysis):
    analysis.completed_recovery_proof_evidence += ({},)

def via_setattr(analysis):
    setattr(analysis, "completed_recovery_proof_evidence", ())

def read_only(analysis):
    return analysis.completed_recovery_proof_evidence
'''
    assert sorted(name for name, _line in _writes(ast.parse(source))) == ["assign", "augmented", "via_setattr"]
