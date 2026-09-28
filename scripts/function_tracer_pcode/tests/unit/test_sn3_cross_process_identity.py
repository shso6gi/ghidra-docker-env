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
    monkeypatch.setattr(structural, "_VALIDATED_TAIL_MEMO", structural.weakref.WeakKeyDictionary())
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
    # counter は process ごとなので、逆順だと別のものに同じ値が付く
    assert a["unidentified"]["X"] == b["unidentified"]["Y"]
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


def test_no_cross_process_consumer_mints_structural_tokens():
    """結果 JSON を読む側（authority / reporting）は構造 key を作らない。

    作れるのは解析 worker の process だけなので、authority が worker の結果と自分で作った
    token を比べる経路は存在しない。ここへ import が増えたら Gate A を見直す。
    """

    offenders = []
    for folder in ("authority", "reporting"):
        for path in sorted((PACKAGE_ROOT / folder).rglob("*.py")):
            if "scripts.function_tracer_pcode.core.structural" in _imports_of(path):
                offenders.append(str(path.relative_to(PACKAGE_ROOT)))
    assert offenders == []


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
