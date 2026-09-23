# -*- coding: utf-8 -*-
"""Issue #167: 証拠は authority scope を決める書き込み口だけで analysis に書く。

* 関数単体の事実（analysis 層など）: ``record_function_unary_evidence``（``function_unary``）。
* 比較の中の証拠（proof 層）: ``store_comparison_evidence``（比較の binding に束縛）。

scope の無い record はどこでも採用されない（``evidence_authority_holds``）ので、書き込み口を
通らない書き込みは fail-closed になる。これは意味の型の代わりではなく防御で、書き込み口を
通らない書き込みが増えたらこの test が落ちる。

例外は下の表だけで、各行に理由がある。
"""

from __future__ import annotations

import ast
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[2]
FIELD = "completed_recovery_proof_evidence"

#: (package からの相対 path, 関数名) -> 理由
ALLOWED_WRITERS = {
    ("proof/formula/input_correspondence/binding.py", "store_comparison_evidence"):
        "比較の中の証拠の書き込み口（比較の中で増えた record を束縛する）",
    ("core/evidence_authority.py", "record_function_unary_evidence"):
        "関数単体の事実の書き込み口（function_unary を明示する）",
    ("proof/strategies/pairwise_services/orchestration.py", "_impl_check"):
        "analysis ではなく strategy 結果の payload。戻り幅の完了証拠を比較に明示的に束縛して載せる",
    ("checker/recovery_proofs.py", "_merge_completed_recovery_proofs_from_result"):
        "結果の証拠を raw analysis へ合流する。record の authority（scope と binding）はそのまま",
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


def _package_writers():
    found = {}
    for path in sorted(PACKAGE.rglob("*.py")):
        relative = path.relative_to(PACKAGE).as_posix()
        if relative.startswith("tests/"):
            continue
        for name, line in _writes(ast.parse(path.read_text(encoding="utf-8"))):
            found.setdefault((relative, name), []).append(line)
    return found


def test_evidence_is_written_only_through_the_authority_writers():
    unexpected = {
        key: lines for key, lines in _package_writers().items() if key not in ALLOWED_WRITERS
    }
    assert unexpected == {}, (
        "completed_recovery_proof_evidence を直接書いている。関数単体の事実は "
        "record_function_unary_evidence、比較の中の証拠は store_comparison_evidence を使うこと: "
        + repr(unexpected)
    )


def test_the_allowed_writers_still_exist():
    assert set(ALLOWED_WRITERS) <= set(_package_writers())


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


def test_comparison_annotations_are_written_only_through_their_writer():
    """比較が raw analysis に書き戻す観測（比較の identity から除く note）は、登録した書き込み口
    ``record_comparison_annotation`` だけで書く（直接 append すると、除外の対象が名前だけで
    決まり、誰が書いたかを保証できない）。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot import COMPARISON_ANNOTATION_NOTES

    direct = []
    for path in sorted(PACKAGE.rglob("*.py")):
        relative = path.relative_to(PACKAGE).as_posix()
        if relative.startswith("tests/"):
            continue
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr in {"append", "extend", "insert"}
                and any(
                    isinstance(argument, ast.Constant) and argument.value in COMPARISON_ANNOTATION_NOTES
                    for argument in ast.walk(node)
                )
            ):
                direct.append((relative, node.lineno))
    assert direct == []
