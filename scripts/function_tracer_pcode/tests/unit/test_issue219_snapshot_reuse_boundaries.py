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

import pytest

from scripts.function_tracer_pcode.tests.unit._package_sources import parse_source

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
OWNER = PACKAGE_ROOT / "proof" / "obligations" / "snapshot_reuse.py"
#: schema の owner（単一の読み `read_snapshot_inputs` と、置き換えを渡す `snapshot_material`）
SCHEMA = PACKAGE_ROOT / "proof" / "obligations" / "snapshot.py"
OWNER_NAMES = frozenset({"ElidedSemanticValue", "_Witness", "_Retained", "_ReadHook"})
#: 入力を読む口（入力の code を走らせ得る）。再利用の owner は自分では呼ばない（読みは `read_snapshot_inputs` だけ）
INPUT_READERS = frozenset({
    "snapshot_material", "_semantic_effect_summary_projection", "freeze", "_freeze_unmetered", "_freeze",
    "digest", "materialize", "to_dict", "semantic_snapshot_dict", "json_items", "stable_key", "create",
    "_build_from_function_analysis_with",
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


def _calls(tree: ast.AST) -> Iterator[Tuple[ast.Call, str]]:
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            func = node.func
            name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
            if name is not None:
                yield node, name


ANALYSIS = PACKAGE_ROOT / "core" / "analysis.py"


def _keyword_passers(keyword: str) -> List[str]:
    """`keyword=` を `None` 以外の値で渡す production の関数（`path:関数名`）。"""

    passers: List[str] = []
    for path, tree in _production_modules():
        for function in (node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)):
            # 呼ぶ先の形（名前・属性・`_CANONICAL_VIEW[1]` のような添字）によらず全ての呼び出しを見る
            for node in (child for child in ast.walk(function) if isinstance(child, ast.Call)):
                for item in node.keywords:
                    if item.arg == keyword and not (isinstance(item.value, ast.Constant) and item.value.value is None):
                        passers.append(f"{path.relative_to(PACKAGE_ROOT)}:{function.name}")
    return sorted(set(passers))


def test_only_the_snapshot_material_hands_a_walk_a_leaf_substitution_and_only_the_owner_defines_one():
    """置き換えは walk の引数でだけ渡る（作業量・thread・context に登録しない）。それを渡すのは schema の owner の
    `snapshot_material`（意味の view 1 回）と、受け取った引数を自分の walk 1 回へそのまま渡す
    `FunctionReturnAnalysis._materialize` だけ。core の walk は受け取った置き換えを自分の葉へ使うだけ
    （`_Walk` の `substitution=`）。置き換える型を定義するのは再利用の owner だけ。"""

    assert _keyword_passers("leaf_substitution") == [
        f"{ANALYSIS.relative_to(PACKAGE_ROOT)}:_materialize",
        f"{SCHEMA.relative_to(PACKAGE_ROOT)}:snapshot_material",
    ]
    materialize = next(
        node for node in ast.walk(parse_source(ANALYSIS))
        if isinstance(node, ast.FunctionDef) and node.name == "_materialize"
    )
    forwarded = [
        item.value for node in ast.walk(materialize) if isinstance(node, ast.Call)
        for item in node.keywords if item.arg == "leaf_substitution"
    ]
    # 受け取った引数をそのまま 1 回だけ渡す（自分で置き換えを作らない）
    assert len(forwarded) == 1 and isinstance(forwarded[0], ast.Name) and forwarded[0].id == "leaf_substitution"
    offenders: List[str] = []
    for path, tree in _production_modules():
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and path != OWNER:
                bases = [base.attr if isinstance(base, ast.Attribute) else getattr(base, "id", None) for base in node.bases]
                if "LeafSubstitution" in bases:
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: {node.name}")
    assert offenders == []


def test_only_the_single_read_hands_the_codec_a_token_capability():
    """token を扱う許可（`PlacedTokens`）は引数でだけ渡る: `_freeze_placing` に `None` 以外を渡すのは単一の読みの
    `frozen_fingerprint_payload`（意味の field の位置だけ。`snapshot_id` は `None`）だけ（`_freeze_placing` 自身の
    再帰を除く）。許可を作るのは `placed_tokens_of`（と
    `NO_PLACED_TOKENS`）だけ。"""

    passers: List[str] = []
    makers: List[str] = []
    for path, tree in _production_modules():
        for function in (node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)):
            for node, name in _calls(function):
                if name == "_freeze_placing":
                    capability = node.args[1] if len(node.args) > 1 else None
                    if not (isinstance(capability, ast.Constant) and capability.value is None):
                        passers.append(f"{path.relative_to(PACKAGE_ROOT)}:{function.name}")
                if name == "PlacedTokens":
                    makers.append(f"{path.relative_to(PACKAGE_ROOT)}:{function.name}")
    schema = SCHEMA.relative_to(PACKAGE_ROOT)
    # `_freeze_placing` の再帰は局所の名前（`recurse`）で、許可を渡すのは組み込みの型そのものの tuple / list / dict の
    # 要素だけ（MappingProxy・subclass・set・record の表現・
    # identity key・dataclass の field へ渡らないことは `test_only_a_placed_token_passes_...` が実際に確かめる）
    assert sorted(set(passers)) == [f"{schema}:frozen_fingerprint_payload"]
    callers = sorted({
        f"{path.relative_to(PACKAGE_ROOT)}:{function.name}"
        for path, tree in _production_modules()
        for function in (node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef))
        for _node, name in _calls(function) if name == "frozen_fingerprint_payload"
    })
    assert callers == [f"{schema}:read_snapshot_inputs"]
    assert sorted(set(makers)) == [f"{schema}:placed_tokens_of"]


def test_no_ambient_state_decides_whether_a_token_passes():
    """token の許可を thread / context の状態に置かない（入力の code へ伝わる）: snapshot の schema と再利用の owner
    は `threading.local` / `ContextVar` を持たない（静的な確認はこの 2 module だけ。葉の置き換えは walk の引数で
    だけ渡り、新しい context・別 thread・入れ子や前後の walk に渡らないことは `test_issue219_leaf_substitution.py`
    と `test_issue219_token_authority.py` が実行して確かめる）。"""

    for path in (SCHEMA, OWNER):
        tree = parse_source(path)
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                bases = [base.attr if isinstance(base, ast.Attribute) else getattr(base, "id", None) for base in node.bases]
                assert "local" not in bases, f"{path.name}:{node.lineno}"
            if isinstance(node, ast.Call):
                name = node.func.attr if isinstance(node.func, ast.Attribute) else getattr(node.func, "id", None)
                assert name not in ("local", "ContextVar"), f"{path.name}:{node.lineno}"


def test_the_reuse_owner_reads_the_input_only_through_the_single_read():
    """再利用の owner は入力を読む口を自分で呼ばない: 入力に対して走る code は本体と同じ 1 回の読みだけ。"""

    calls = sorted({name for _node, name in _calls(parse_source(OWNER)) if name in INPUT_READERS})
    assert calls == []
    called = {name for _node, name in _calls(parse_source(OWNER))}
    assert {"read_snapshot_inputs", "assemble_snapshot", "canonical_generation_path"} <= called


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
    # 生成経路（class）と解析をそのまま渡す（本体を選ぶのは再利用の owner: canonical でなければ本体へ）
    assert [getattr(arg, "id", None) for arg in calls[0].args] == ["cls", "analysis"]


def test_the_live_flow_audit_follows_the_leaf_substitution_protocol():
    """置き換えの protocol（`LeafSubstitution.__leaf_substitute__`）は bounded path の root（葉は live）。"""

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as flow

    _violations, analyzed, _index, _missing = flow.audit(PACKAGE_ROOT)
    assert (flow.PKG + ".proof.obligations.snapshot_reuse", "_ReadHook.__leaf_substitute__") in analyzed


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

    assert [entry[0] for entry in snapshot_module._WITNESS_TOKEN_TYPES] == [snapshot_reuse.ElidedSemanticValue]


def test_only_a_placed_token_passes_and_only_through_the_internal_freeze():
    """通常の入口（`freeze` / `_freeze_unmetered` / `digest`）は token を拒む。`_freeze_placing` は渡された許可に
    ある token **そのもの** だけを置く（同じ型の別の object は拒む）。許可は record の表現・identity key・dataclass
    の field へは渡らない（そこは入力の値）。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot import PlacedTokens, SnapshotFingerprintCodec
    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import ElidedSemanticValue

    token = ElidedSemanticValue(object())
    placed = PlacedTokens([token])
    for entry in (SnapshotFingerprintCodec.freeze, SnapshotFingerprintCodec._freeze_unmetered, SnapshotFingerprintCodec.digest):
        with pytest.raises(TypeError, match="opaque object ElidedSemanticValue"):
            entry({"k": token})
    assert SnapshotFingerprintCodec._freeze_placing({"k": [token]}, placed) == (("k", (token,)),)
    with pytest.raises(TypeError, match="opaque object ElidedSemanticValue"):
        SnapshotFingerprintCodec._freeze_placing({"k": ElidedSemanticValue(token.value)}, placed)

    import dataclasses

    class Keyed:
        def stable_key(self):
            return ("key", token)

    class Record:
        def json_items(self):
            yield "held", [token]

    @dataclasses.dataclass(frozen=True)
    class Fields:
        held: object

    # 置いた token そのものでも、入力の値（identity key・record の表現・dataclass の field）の中では token ではない
    for value in (Keyed(), Record(), Fields(token)):
        with pytest.raises(TypeError, match="ElidedSemanticValue"):
            SnapshotFingerprintCodec._freeze_placing({"k": value}, placed)
    with pytest.raises(TypeError):
        PlacedTokens([object()])
