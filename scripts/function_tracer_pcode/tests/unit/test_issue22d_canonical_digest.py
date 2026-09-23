# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D: 有界な証拠の identity / 照合用 digest の契約。

* `canonical_merkle_digest(a) == canonical_merkle_digest(b)` ⇔
  `canonical_value(a) == canonical_value(b)`（legacy reason の照合の等しさは変えない）
* DAG-aware: 共有部分を持つ key は distinct な node の数だけ辿る
* `streaming_canonical_str_digest(v) == sha256(str(canonical_value(v)))`
"""

from __future__ import annotations

import enum
import hashlib
import random
import time
from dataclasses import dataclass

from scripts.function_tracer_pcode.authority.contracts import (
    canonical_value,
    streaming_canonical_str_digest,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    MATCH_AUTHORITY_DIGEST,
    bounded_match_evidence,
)
from scripts.function_tracer_pcode.core.canonical_digest import canonical_merkle_digest
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    BoundedEvidence,
    evidence,
)


class _Kind(enum.Enum):
    A = "a"
    B = 3


@dataclass(frozen=True)
class _Pair:
    x: object
    y: object


def _values(seed=11, count=1500):
    rnd = random.Random(seed)

    def gen(depth=0):
        choice = rnd.randrange(12 if depth < 4 else 6)
        if choice == 0:
            return None
        if choice == 1:
            return rnd.choice([True, False])
        if choice == 2:
            return rnd.choice([0, 1, 2, -3, 10 ** 20])
        if choice == 3:
            return rnd.choice([0.5, 1.0, 2.0, -1.25, 1e300, float("inf")])
        if choice == 4:
            return rnd.choice(["", "a'b", 'q"x', "日本", "\n\t", "1"])
        if choice == 5:
            return rnd.choice([_Kind.A, _Kind.B])
        if choice == 6:
            return tuple(gen(depth + 1) for _ in range(rnd.randrange(3)))
        if choice == 7:
            return [gen(depth + 1) for _ in range(rnd.randrange(3))]
        if choice == 8:
            return {rnd.choice(["k1", "k2", 3, "z"]): gen(depth + 1) for _ in range(rnd.randrange(3))}
        if choice == 9:
            return _Pair(gen(depth + 1), gen(depth + 1))
        if choice == 10:
            return frozenset(rnd.randrange(3) for _ in range(rnd.randrange(3)))
        return (gen(depth + 1),)

    return [gen() for _ in range(count)]


def test_merkle_digest_equality_is_canonical_value_equality():
    values = _values()
    canonical = [canonical_value(value) for value in values]
    digests = [canonical_merkle_digest(value)[0] for value in values]
    for i in range(len(values)):
        for j in range(i, min(len(values), i + 30)):
            assert (canonical[i] == canonical[j]) == (digests[i] == digests[j]), (values[i], values[j])


def test_canonical_str_digest_equals_the_eager_text():
    for value in _values(seed=3, count=800):
        expected = hashlib.sha256(str(canonical_value(value)).encode("utf-8")).hexdigest()
        assert streaming_canonical_str_digest(value) == expected, value


def test_a_dag_shaped_key_is_digested_by_its_distinct_nodes():
    node = ("leaf",)
    for _ in range(60):
        node = (node, node)  # 木に展開すると 2^60 個の葉
    started = time.perf_counter()
    digest, distinct = canonical_merkle_digest(node)
    assert distinct == 62 and time.perf_counter() - started < 1.0
    bounded = bounded_match_evidence(("key",) + tuple(range(3_000)) + (node,))
    assert type(bounded) is BoundedEvidence and bounded.distinct_nodes < 3_200
    assert bounded.match_digest(MATCH_AUTHORITY_DIGEST) == bounded.identity


def test_the_output_summary_and_the_authority_side_summary_share_one_identity():
    key = ("return_coverage",) + tuple(range(5_000))
    finitized = bounded_match_evidence(key)
    rendered = RESULT_JSON_POLICY.prepare({"k": evidence(key)}).value()["k"]
    assert rendered["identity"] == finitized.identity
    assert rendered["distinct_nodes"] == finitized.distinct_nodes
    assert rendered == RESULT_JSON_POLICY.prepare({"k": finitized}).value()["k"]
