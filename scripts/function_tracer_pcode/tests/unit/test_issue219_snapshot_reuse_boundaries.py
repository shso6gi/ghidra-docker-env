# -*- coding: utf-8 -*-
"""snapshot の再利用の owner の境界（Issue #219 PR-219-B、T-B19）。

静的な規則で固定する（一覧ではなく規則: 新しい module が規則を破れば落ちる）:

1. 直列化の作業量の葉の置き換え（`leaf_substitution=`）を渡すのは snapshot の再利用の owner
   だけ（core は渡された置き換えを次へ渡すだけ）。codec に witness の token を通させる（`witness`
   に真を渡す）のも owner だけ。
2. 再利用の token・witness の型は owner の外で使わない（作るのも比べるのも owner だけ）。
3. production の module は snapshot / fingerprint の独自の cache を持たない: 本体の結果を
   mapping へ代入しない・`setdefault` しない・memo の decorator で包まない。再利用の判断は
   owner の 1 か所（`snapshot_reuse.reuse_or_build`）だけ。
4. `from_function_analysis` は owner へ委ねる 1 か所で、本体（`_build_from_function_analysis`）を
   直接呼ぶ production code は owner だけ。
"""

from __future__ import annotations

import ast
from pathlib import Path
from typing import Iterator, List, Tuple

from scripts.function_tracer_pcode.tests.unit._package_sources import parse_source

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
OWNER = PACKAGE_ROOT / "proof" / "obligations" / "snapshot_reuse.py"
#: 置き換えを次へ渡すだけの core の仕組み（同名の引数をそのまま渡す）
FORWARDER = PACKAGE_ROOT / "core" / "budget_policy.py"
OWNER_NAMES = frozenset({"ElidedSemanticValue", "_Witness", "_Retained", "_Pending", "_LeafSubstitution"})
#: witness の材料を写す口（`witness` が真のときだけ token を通す）。真を渡すのは owner だけ
WITNESS_FLAG_CALLEES = frozenset({
    "snapshot_material", "_semantic_effect_summary_projection", "freeze", "_freeze_unmetered", "_FreezeMeter",
})
SNAPSHOT_PRODUCERS = frozenset({"from_function_analysis", "_build_from_function_analysis", "snapshot_material"})
MEMO_DECORATORS = frozenset({"lru_cache", "cache", "cached_property"})


def _production_modules() -> Iterator[Tuple[Path, ast.Module]]:
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT)
        if relative.parts and relative.parts[0] == "tests":
            continue
        yield path, parse_source(path)


def _calls_snapshot_producer(node: ast.AST) -> bool:
    for child in ast.walk(node):
        if isinstance(child, ast.Call):
            func = child.func
            name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
            if name in SNAPSHOT_PRODUCERS:
                return True
    return False


def test_only_the_reuse_owner_passes_a_leaf_substitution():
    offenders: List[str] = []
    for path, tree in _production_modules():
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            for keyword in node.keywords:
                if keyword.arg != "leaf_substitution":
                    continue
                forwarding = (
                    path == FORWARDER
                    and isinstance(keyword.value, ast.Name)
                    and keyword.value.id == "leaf_substitution"
                )
                if path != OWNER and not forwarding:
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}")
    assert offenders == []


def test_only_the_reuse_owner_asks_the_codec_to_pass_witness_tokens():
    offenders: List[str] = []
    for path, tree in _production_modules():
        if path == OWNER:
            continue
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
            if name not in WITNESS_FLAG_CALLEES:
                continue
            values = list(node.args) + [keyword.value for keyword in node.keywords]
            if any(isinstance(value, ast.Constant) and value.value is True for value in values):
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}")
    assert offenders == []


def test_reuse_tokens_and_witnesses_stay_inside_the_owner():
    offenders: List[str] = []
    for path, tree in _production_modules():
        if path == OWNER:
            continue
        for node in ast.walk(tree):
            name = None
            if isinstance(node, ast.Name):
                name = node.id
            elif isinstance(node, ast.Attribute):
                name = node.attr
            elif isinstance(node, ast.alias):
                name = node.name
            if name in OWNER_NAMES:
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{getattr(node, 'lineno', '?')}:{name}")
    assert offenders == []


def test_production_modules_keep_no_snapshot_cache_of_their_own():
    offenders: List[str] = []
    for path, tree in _production_modules():
        if path == OWNER:
            continue
        for node in ast.walk(tree):
            if isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                if node.value is not None and any(isinstance(t, ast.Subscript) for t in targets):
                    if _calls_snapshot_producer(node.value):
                        offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: mapping store")
            elif isinstance(node, ast.Call):
                func = node.func
                if isinstance(func, ast.Attribute) and func.attr == "setdefault":
                    if any(_calls_snapshot_producer(arg) for arg in node.args[1:]):
                        offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: setdefault")
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                decorators = []
                for decorator in node.decorator_list:
                    target = decorator.func if isinstance(decorator, ast.Call) else decorator
                    decorators.append(target.attr if isinstance(target, ast.Attribute) else getattr(target, "id", None))
                if MEMO_DECORATORS.intersection(decorators) and _calls_snapshot_producer(node):
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: memo decorator")
    assert offenders == []


def test_only_the_owner_runs_the_snapshot_body_and_from_function_analysis_delegates():
    snapshot_path = PACKAGE_ROOT / "proof" / "obligations" / "snapshot.py"
    offenders: List[str] = []
    for path, tree in _production_modules():
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr == "_build_from_function_analysis":
                if path not in (OWNER, snapshot_path):
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}")
    assert offenders == []

    tree = parse_source(snapshot_path)
    method = next(
        node for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef) and node.name == "from_function_analysis"
    )
    calls = [
        node for node in ast.walk(method)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
    ]
    assert [call.func.attr for call in calls] == ["reuse_or_build"]
    # 本体は class の方法として 1 か所で渡す（呼ばない）
    assert any(
        isinstance(arg, ast.Attribute) and arg.attr == "_build_from_function_analysis"
        for arg in calls[0].args
    )


def test_the_live_flow_audit_follows_the_leaf_substitution_protocol():
    """置き換えの protocol（`LeafSubstitution.__leaf_substitute__`）は bounded path の root（葉は live）。"""

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as flow

    _violations, analyzed, _index, _missing = flow.audit(PACKAGE_ROOT)
    assert (flow.PKG + ".proof.obligations.snapshot_reuse", "_LeafSubstitution.__leaf_substitute__") in analyzed


def test_only_the_reuse_owner_registers_witness_token_types():
    """codec が witness の中でそのまま通す型は、再利用の owner が発行して登録した型だけ（入力の自己宣言は無い）。"""

    offenders: List[str] = []
    for path, tree in _production_modules():
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                func = node.func
                name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
                if name == "register_witness_token_type" and path != OWNER:
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}")
            # 型の属性で token を名乗る仕組み（class 属性の宣言）を codec が読まない
            if isinstance(node, ast.Constant) and node.value == "__snapshot_witness_token__":
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: self-declared token marker")
    assert offenders == []

    from scripts.function_tracer_pcode.proof.obligations import snapshot as snapshot_module
    from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse

    assert set(snapshot_module._WITNESS_TOKEN_TYPES) == {snapshot_reuse.ElidedSemanticValue, snapshot_reuse._Pending}
