# -*- coding: utf-8 -*-
"""Issue #215 Gate A: 構造 key の tail token を process をまたいで identity にしない。

tail token の index は「この process で同じ digest に何番目に来た record か」なので、
digest が衝突すると **別の process が同じ `(digest, index)` を別の record に割り当て得る**
（A: X→0, Y→1 / B: Y→0, X→1）。識別不能 token の serial も process ごとの counter。

実コードで確かめた事実（Issue #215 / PR 本文に記録）:

* 構造 key を作るのは解析 worker の process だけ（authority / reporting は
  `core.structural` を import しない。下の static test が固定する）。
* key の値は結果 JSON（sealed event stream の `canonical_target_key`、
  `completed_recovery_proof_evidence[].object_target_key`、
  `unknown_cause_aggregate.identity_pool`）へ生のまま書かれる。
* 永続化した key を **別 process の結果** と identity として比べるのは
  `reporting/root_blocker_summary`（pair・関数・run をまたぐ root blocker 集計）で、
  その identity は `checker/cause_aggregate.resolve_cause_identity` 1 か所で決まる。

したがって token を含む key はそこで比較不能（`process_scoped_cause_identity`）に
倒す。ここの test は、digest を強制衝突させた 2 process を実際に走らせ、永続化した
値を JSON 経由で読み戻して確かめる。
"""

from __future__ import annotations

import ast
import json
import os
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.checker.cause_aggregate import (
    freeze_identity,
    resolve_cause_identity,
)
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.structural import expression_key


def key_is_process_independent(key):
    return structural.key_is_process_independent(key)


REPO_ROOT = Path(__file__).resolve().parents[4]
PACKAGE_ROOT = Path(__file__).resolve().parents[2]

#: 子 process: digest を定数にして（SHA-256 の衝突の代わり）、指定順に key を作り JSON で返す
_CHILD = r"""
import json, sys
sys.path.insert(0, {root!r})
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.tests.unit.test_sn3_cross_process_identity import build

if {collide!r}:
    structural._ExactTailIntern.digest = staticmethod(lambda record: "0" * 64)
order = {order!r}
keys = {{name: structural.expression_key(build(name), budget={budget!r}, **{options!r}) for name in order}}
unidentified = [structural.unidentified_identity("probe") for _ in order]
print(json.dumps({{"keys": keys, "unidentified": dict(zip(order, unidentified)),
                   "stats": structural.exact_tail_statistics()}}))
"""


#: 根だけを key に入れ、子を tail token にする予算
BUDGET = 1


def build(name):
    """X / Y / Z: 予算を超えた先（右の定数）だけが違う式。

    根 1 つで予算を使い切るので、左の ``a`` と右の定数がそれぞれ 1 record の tail
    token になる。``a`` は共通なので、登録順を逆にすると X と Y の定数の record が
    同じ index を取る。
    """

    from scripts.function_tracer_pcode.core.expression import Expression

    tail = {"X": 1, "Y": 2, "Z": 3}[name]
    return Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(tail, size=4))


def _run_child(order, *, collide=True, seed="0", options=None):
    code = _CHILD.format(
        root=str(REPO_ROOT), collide=collide, order=list(order), options=dict(options or {}), budget=BUDGET,
    )
    completed = subprocess.run(
        [sys.executable, "-B", "-c", code],
        env=dict(os.environ, PYTHONHASHSEED=seed),
        cwd=str(REPO_ROOT), capture_output=True, text=True, check=True,
    )
    return json.loads(completed.stdout)


def _cause_key(structural_key):
    """`deferred_call_v1` の legacy cause key（引数に構造 key を持つ）。JSON 往復後の形。"""

    return freeze_identity(
        ["deferred_call_site", ["function_ref", "f"], ["pcode_op", 1], ["argument", structural_key]]
    )


def _resolve(structural_key):
    return resolve_cause_identity(
        typed_cause_key=None,
        object_target_key=_cause_key(structural_key),
        left_binary_identity=("sha256", "a" * 64),
        right_binary_identity=("sha256", "b" * 64),
    )


# --------------------------------------------------------------------------
# 1. 強制衝突: process A は X→Y、process B は Y→X
# --------------------------------------------------------------------------

def test_reversed_registration_across_processes_gives_different_records_the_same_raw_token():
    a = _run_child(["X", "Y"])
    b = _run_child(["Y", "X"])
    # 同じ process の中では別の identity（C-K1）
    assert a["keys"]["X"] != a["keys"]["Y"]
    assert b["keys"]["X"] != b["keys"]["Y"]
    assert a["stats"]["collisions"] >= 1
    # しかし永続化した値を process をまたいで比べると、別の record が同じ値になる
    # （これが process-local index を identity にしてはいけない理由）
    assert a["keys"]["X"] == b["keys"]["Y"]
    assert a["keys"]["Y"] == b["keys"]["X"]


def test_the_cross_process_identity_resolver_refuses_process_scoped_keys():
    a = _run_child(["X", "Y"])
    b = _run_child(["Y", "X"])
    for key in (a["keys"]["X"], a["keys"]["Y"], b["keys"]["X"], b["keys"]["Y"]):
        assert not key_is_process_independent(key)
        resolution = _resolve(key)
        assert not resolution.resolved
        assert resolution.diagnostic == "process_scoped_cause_identity"
    # A の X と B の Y は、root blocker として 1 つにまとまらない
    assert _resolve(a["keys"]["X"]).canonical_cause_key is None
    assert _resolve(b["keys"]["Y"]).canonical_cause_key is None


def test_a_key_without_tokens_still_resolves_across_processes():
    shallow = expression_key(build("X"), budget=10_000)
    assert key_is_process_independent(shallow)
    assert _resolve(json.loads(json.dumps(shallow))).resolved


# --------------------------------------------------------------------------
# 2. 永続化した token と、新しい process の token
# --------------------------------------------------------------------------

def test_a_persisted_token_is_never_accepted_as_the_identity_of_a_fresh_process_token(monkeypatch):
    persisted = _run_child(["X"])["keys"]["X"]  # process A が X を書いた
    # この process（B）は Y だけを見る。衝突させると Y も index 0 になる
    monkeypatch.setattr(structural, "_TAIL_INTERN", _colliding_intern())
    monkeypatch.setattr(structural, "_VALIDATED_TAIL_MEMO", structural.WeakKeyedTable())
    fresh = json.loads(json.dumps(expression_key(build("Y"), budget=BUDGET)))
    assert fresh == persisted  # 値は一致してしまう
    assert not key_is_process_independent(persisted)
    assert not key_is_process_independent(fresh)
    assert not _resolve(persisted).resolved and not _resolve(fresh).resolved


def _colliding_intern():
    class _CollidingIntern(structural._ExactTailIntern):
        @staticmethod
        def digest(record):
            return "0" * 64

    return _CollidingIntern()


# --------------------------------------------------------------------------
# 3. 識別不能 token を逆順で作る 2 process
# --------------------------------------------------------------------------

def test_unidentified_tokens_from_reversed_processes_never_become_an_identity():
    a = _run_child(["X", "Y"], collide=False)
    b = _run_child(["Y", "X"], collide=False)
    # 通し番号は process ごとなので逆順だと別のものに同じ番号が付くが、token は nonce で
    # 別 process の token と一致しない（昇格規則から見えない形に埋め込まれても同じ）
    assert a["unidentified"]["X"][2] == b["unidentified"]["Y"][2]
    assert a["unidentified"]["X"] != b["unidentified"]["Y"]
    for token in (a["unidentified"]["X"], b["unidentified"]["Y"]):
        assert not key_is_process_independent(token)
        assert not _resolve(token).resolved
    # 同じ process の中では何とも等しくならない（C-K5）
    assert structural.unidentified_identity("probe") != structural.unidentified_identity("probe")


# --------------------------------------------------------------------------
# 4. restart / replay・PYTHONHASHSEED・option の差
# --------------------------------------------------------------------------

@pytest.mark.parametrize("seed", ["0", "7", "random"])
def test_restarted_processes_produce_the_same_tokens_but_they_stay_process_scoped(seed):
    first = _run_child(["X", "Y", "Z"], collide=False, seed="0")
    again = _run_child(["X", "Y", "Z"], collide=False, seed=seed)
    # 衝突が無ければ再起動しても値は同じ（決定性、C-K6）
    assert first["keys"] == again["keys"]
    assert first["stats"]["collisions"] == again["stats"]["collisions"] == 0
    # それでも identity として process をまたいで使わない
    assert not any(key_is_process_independent(key) for key in first["keys"].values())


@pytest.mark.parametrize(
    "options",
    [{"normalize_commutative": False}, {"include_memory_read_order": False},
     {"strip_width_adapters": True}, {"collapse_full_masks": True}],
)
def test_option_and_process_differences_do_not_change_the_relation(options):
    here = {name: expression_key(build(name), budget=BUDGET, **options) for name in ("X", "Y")}
    there = _run_child(["Y", "X"], collide=False, seed="4242", options=options)["keys"]
    assert json.loads(json.dumps(here)) == there
    default = _run_child(["X", "Y"], collide=False, seed="1")["keys"]
    # option が T_o を変えない式なので、option を変えても X≠Y の関係は同じ
    assert (there["X"] == there["Y"]) is (default["X"] == default["Y"]) is False


# --------------------------------------------------------------------------
# 5. 境界の固定（static）
# --------------------------------------------------------------------------

def _imports_of(path):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    names = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            names.add(node.module)
        elif isinstance(node, ast.Import):
            names.update(alias.name for alias in node.names)
    return names


#: 別の process が書いた結果を読む側の module（supervisor 側の `authority/process`、`reporting`、
#: package 外の評価 tool）。`authority/domains` などの判定 authority は解析 worker の process の
#: 中で動き、token を作った process の中で比べるので、ここには入れない。
_READER_PROCESS_TREES = (
    PACKAGE_ROOT / "authority" / "process",
    PACKAGE_ROOT / "reporting",
    PACKAGE_ROOT.parent / "eqbench",
)
#: 構造 key（token を持ち得る値）を作る API。import でなく method として呼ばれても数える
_KEY_MINTING_NAMES = frozenset({
    "structural_key", "expression_key", "condition_key", "expression_key_safe", "condition_key_safe",
    "expression_key_status", "expression_key_or_identity", "exact_structural_identity",
    "exact_tail_token", "unidentified_identity", "_safe_structural_key",
})


def test_no_cross_process_consumer_mints_structural_tokens():
    """結果 JSON を読む側（別の process）は構造 key を作らない（import でも method 呼び出しでも）。

    読む側が自分で作った token と、worker が書いた token を比べる経路を作らないため。ここへ
    増えたら Gate A を見直す（読む側の identity は `freeze_identity` の昇格を通った値だけ）。
    """

    offenders = []
    for tree_root in _READER_PROCESS_TREES:
        for path in sorted(tree_root.rglob("*.py")):
            source = path.read_text(encoding="utf-8")
            if "scripts.function_tracer_pcode.core.structural" in _imports_of(path):
                offenders.append((str(path.relative_to(PACKAGE_ROOT.parent)), "import"))
            for node in ast.walk(ast.parse(source)):
                if isinstance(node, ast.Call):
                    func = node.func
                    name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
                    if name in _KEY_MINTING_NAMES:
                        offenders.append((str(path.relative_to(PACKAGE_ROOT.parent)), name, node.lineno))
    assert offenders == []


def test_readers_never_enter_the_minting_process_scope():
    """昇格を外す scope（token を作った process 自身の集計）は、読む側の module から張れない。"""

    offenders = []
    for tree_root in _READER_PROCESS_TREES:
        for path in sorted(tree_root.rglob("*.py")):
            if "minting_process_identities" in path.read_text(encoding="utf-8"):
                offenders.append(str(path.relative_to(PACKAGE_ROOT.parent)))
    assert offenders == []


def test_the_minting_process_compares_its_own_tokens_and_everyone_else_promotes_them():
    from scripts.function_tracer_pcode.checker.cause_aggregate import IdentityPool, minting_process_identities

    key = expression_key(build("X"), budget=BUDGET)
    assert not key_is_process_independent(key)
    with minting_process_identities():
        # 作った process の中では token は identity（C-K1）: 同じ値は同じ、pool も 1 つにまとめる
        assert freeze_identity(key) == freeze_identity(key)
        assert _resolve(key).resolved
        pool = IdentityPool()
        assert pool.intern(key) == pool.intern(json.loads(json.dumps(key)))
        assert freeze_identity(key) != freeze_identity(expression_key(build("Y"), budget=BUDGET))
    # scope の外（既定: 別の process が書いた値として読む）では一致しない
    assert freeze_identity(key) != freeze_identity(key)
    assert _resolve(key).diagnostic == "process_scoped_cause_identity"


def test_the_worker_aggregate_is_built_inside_the_minting_scope(monkeypatch):
    from scripts.function_tracer_pcode.checker import cause_aggregate

    seen = []
    monkeypatch.setattr(
        cause_aggregate, "_build_unknown_cause_aggregate",
        lambda result: seen.append(cause_aggregate._MINTING_PROCESS_SCOPE.get()) or {"schema": "x"},
    )
    monkeypatch.setattr(
        cause_aggregate, "build_trace_cause_evidence",
        lambda result, **kwargs: seen.append(cause_aggregate._MINTING_PROCESS_SCOPE.get()) or {"schema": "y"},
    )
    cause_aggregate.build_unknown_cause_aggregate(object())
    cause_aggregate.build_unknown_cause_aggregate(object(), trace_evidence_for=(None, None))
    assert seen == [True, True]
    assert cause_aggregate._MINTING_PROCESS_SCOPE.get() is False  # scope は抜けると戻る


_NONCE_CHILD = r"""
import json, sys
sys.path.insert(0, {root!r})
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
from scripts.function_tracer_pcode.core.expression import Expression
tokens = [structural.unidentified_identity("probe") for _ in range(3)]
objects = [structural.expression_key_or_identity(Expression.parameter("a", 0, size=4), budget=0) for _ in range(3)]
hidden = [structural._digest_structural_payload(canonical_atom(token)) for token in tokens]
print(json.dumps({{"tokens": tokens, "objects": objects, "hidden": hidden}}))
"""


def _run_nonce_child():
    completed = subprocess.run(
        [sys.executable, "-B", "-c", _NONCE_CHILD.format(root=str(REPO_ROOT))],
        cwd=str(REPO_ROOT), capture_output=True, text=True, check=True,
    )
    return json.loads(completed.stdout)


def test_counter_tokens_of_two_processes_never_coincide_even_when_hidden_in_a_digest():
    """識別不能 token / object identity は process の中の通し番号が同じでも別 process と一致しない。

    `canonical_atom` の包みや digest の preimage の中では昇格規則（`cross_process_node`）が
    token を見られないので、token 自身が別 process の token と等しくならない必要がある。
    """

    a, b = _run_nonce_child(), _run_nonce_child()
    # 通し番号は両方の process で同じ（0, 1, 2 …）
    assert [token[2] for token in a["tokens"]] == [token[2] for token in b["tokens"]]
    assert set(map(json.dumps, a["tokens"])).isdisjoint(map(json.dumps, b["tokens"]))
    assert set(map(json.dumps, a["objects"])).isdisjoint(map(json.dumps, b["objects"]))
    # 見えない形（包んで digest にした値）でも一致しない
    assert set(a["hidden"]).isdisjoint(b["hidden"])
    # 同じ process の中でも、すべて別
    assert len({json.dumps(token) for token in a["tokens"]}) == 3


@pytest.mark.skipif(not hasattr(os, "fork"), reason="needs fork")
def test_a_forked_child_does_not_repeat_the_parents_counter_tokens():
    read_end, write_end = os.pipe()
    structural.unidentified_identity("warm")
    pid = os.fork()
    if pid == 0:  # child: 親と同じ通し番号の状態から作る
        try:
            os.write(write_end, json.dumps(structural.unidentified_identity("probe")).encode())
        finally:
            os._exit(0)
    os.close(write_end)
    child = json.loads(os.read(read_end, 4096).decode())
    os.close(read_end)
    os.waitpid(pid, 0)
    parent = structural.unidentified_identity("probe")
    assert child[2] == parent[2]  # 通し番号は同じ
    assert child != list(parent)  # それでも一致しない


def test_the_root_blocker_summary_identity_goes_through_the_single_resolver():
    from scripts.function_tracer_pcode.reporting import root_blocker_summary

    stable = SimpleNamespace(comparison_domain=SimpleNamespace(
        left_binary_identity=("sha256", "a" * 64), right_binary_identity=("sha256", "b" * 64),
    ))
    record = {"object_target_key": _cause_key(json.loads(json.dumps(expression_key(build("X"), budget=BUDGET))))}
    diagnostics = {}
    blocker, typed = root_blocker_summary._blocker_id(record, stable, diagnostics)
    assert blocker is None and typed is False
    assert "process_scoped_cause_identity" in json.dumps(diagnostics)


# --------------------------------------------------------------------------
# 6. 唯一の昇格点: 結果 JSON から作る identity はすべて `freeze_identity` を通る
# --------------------------------------------------------------------------

def test_freeze_identity_never_lets_a_process_scoped_token_compare_equal():
    a = _run_child(["X", "Y"])
    b = _run_child(["Y", "X"])
    # 同じ永続化値を 2 回凍らせても、別 process の値と比べても一致しない（過分割）
    assert freeze_identity(a["keys"]["X"]) != freeze_identity(b["keys"]["Y"])
    assert freeze_identity(a["keys"]["X"]) != freeze_identity(a["keys"]["X"])
    # token を持たない値は従来どおり、JSON の往復に依らず一致する
    plain = expression_key(build("X"), budget=10_000)
    assert freeze_identity(plain) == freeze_identity(json.loads(json.dumps(plain)))


def test_required_proof_keys_from_different_processes_are_not_merged():
    from scripts.function_tracer_pcode.checker.cause_aggregate import resolve_required_proofs
    from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementId

    a = _run_child(["X", "Y"])
    b = _run_child(["Y", "X"])

    def keys(structural_key):
        requirement = ProofRequirementId.create("return_coverage", ("target", structural_key), ("contract",))
        payload = json.loads(json.dumps(requirement.to_dict()))
        return resolve_required_proofs(
            proof_requirement_ids=[payload], object_target_key=None, identity_scope="unary",
            canonical_cause_key=("cause",), recovery_actions=(),
        ).keys

    assert a["keys"]["X"] == b["keys"]["Y"]  # 生の値は一致してしまう
    assert set(keys(a["keys"]["X"])).isdisjoint(keys(b["keys"]["Y"]))
    plain = json.loads(json.dumps(expression_key(build("X"), budget=10_000)))
    assert keys(plain) == keys(plain)


def test_a_required_proof_set_with_process_scoped_keys_is_not_reported_complete():
    """過分割した requirement の件数を「完全」と名乗らない（reporting の root blocker 集計）。"""

    from scripts.function_tracer_pcode.checker.cause_aggregate import (
        minting_process_identities,
        resolve_required_proofs,
    )
    from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementId

    def resolve(structural_key):
        requirement = ProofRequirementId.create("return_coverage", ("target", structural_key), ("contract",))
        payload = json.loads(json.dumps(requirement.to_dict()))
        return resolve_required_proofs(
            proof_requirement_ids=[payload], object_target_key=None, identity_scope="unary",
            canonical_cause_key=("cause",), recovery_actions=(),
        )

    scoped = _run_child(["X", "Y"])["keys"]["X"]
    reported = resolve(scoped)
    assert reported.complete is False
    assert "process_scoped_proof_requirement" in reported.diagnostics
    # token を作った process 自身の集計では照合できるので完全
    token_key = json.loads(json.dumps(expression_key(build("X"), budget=BUDGET)))
    with minting_process_identities():
        assert resolve(token_key).complete is True
    # 対照: token を持たない requirement は完全
    plain = json.loads(json.dumps(expression_key(build("X"), budget=10_000)))
    assert resolve(plain).complete is True and resolve(plain).diagnostics == ()


def test_case_pair_refs_from_different_processes_are_not_merged():
    from scripts.function_tracer_pcode.reporting import root_blocker_summary

    a = _run_child(["X", "Y"])
    b = _run_child(["Y", "X"])
    stable = SimpleNamespace(to_key=lambda: ("stable",))
    occurrence = {"attempt_identity": {"strategy_identity": "pairwise"}}

    def ref(case_key):
        return root_blocker_summary._case_pair_ref({}, stable, occurrence, {"pair_or_case": [case_key, case_key]})

    assert ref(a["keys"]["X"]) != ref(b["keys"]["Y"])


#: reporting が結果 JSON の identity field を読んでよい関数（読んだ値は必ず
#: `freeze_identity` / `identity_tuple` か `cause_aggregate` の resolver へ渡す）。
#: 関数を足すなら、ここへ足す前にその経路が昇格点を通ることを確かめること。
_PERSISTED_IDENTITY_FIELDS = frozenset({
    "object_target_key", "typed_cause_key", "proof_requirement_ids", "proof_obligation_id",
    "pair_or_case", "canonical_cause_key", "canonical_target_key", "identity_pool",
    "required_proof_id_refs", "cause_ref", "case_pair_ref", "target_occurrence_id",
})
_PERSISTED_IDENTITY_READERS = {
    ("function_tracer_pcode/reporting/root_blocker_summary.py", "summarize_root_blockers"),
    ("function_tracer_pcode/reporting/root_blocker_summary.py", "_blocker_id"),
    ("function_tracer_pcode/reporting/root_blocker_summary.py", "_case_pair_ref"),
    ("function_tracer_pcode/reporting/root_blocker_summary.py", "_add_occurrence"),
    ("function_tracer_pcode/reporting/root_blocker_summary.py", "_add_cause_group"),
}


def test_only_registered_reporting_functions_read_persisted_identity_fields():
    """新しい cross-process consumer が、昇格点を通さずに永続化した key を比べ始めないこと。"""

    readers = set()
    # 結果 JSON を読む側: package の reporting と、package 外の評価 tool（`scripts/eqbench`）
    paths = sorted((PACKAGE_ROOT / "reporting").rglob("*.py")) + sorted(
        (PACKAGE_ROOT.parent / "eqbench").rglob("*.py")
    )
    for path in paths:
        tree = ast.parse(path.read_text(encoding="utf-8"))

        def visit(node, function):
            for child in ast.iter_child_nodes(node):
                name = child.name if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) else function
                if isinstance(child, ast.Constant) and child.value in _PERSISTED_IDENTITY_FIELDS:
                    readers.add((str(path.relative_to(PACKAGE_ROOT.parent)), function))
                visit(child, name)

        visit(tree, "<module>")
    assert readers == _PERSISTED_IDENTITY_READERS
