# -*- coding: utf-8 -*-
"""recovery 証拠 record の authority scope（Issue #167）。

``completed_recovery_proof_evidence`` の record は、どの範囲で authority を持つかを
**明示する**。scope の無い record はどこでも採用されない（fail-closed）。

* ``function_unary``: 1 つの関数だけについての事実（analysis 層の recurrence・
  bounded refinement・unary recurrence artifact など）。peer の関数も入力の対応も
  前提にしないので、その関数を含むどの比較でも使える。書くのは
  ``record_function_unary_evidence`` だけ。
* ``comparison``: 1 つの比較（raw pair と最終 InputCorrespondence）の中で作った事実。
  ``comparison_authority`` にその比較の ``ComparisonAuthorityBinding`` の digest を持ち、
  同じ binding の比較でだけ採用される。束縛と照合の owner は
  ``proof/formula/input_correspondence/binding.py``。

この module は scope の語彙と unary 側の書き込み口だけを持つ（analysis 層から使うので
core に置く。比較の binding は proof 層にある）。
"""

from __future__ import annotations

from typing import Any, Mapping, MutableMapping, Optional

#: record が authority を持つ範囲。
AUTHORITY_SCOPE_KEY = "authority_scope"
FUNCTION_UNARY = "function_unary"
COMPARISON = "comparison"

#: ``COMPARISON`` の record が持つ、それを作った比較の binding の digest。
COMPARISON_AUTHORITY_KEY = "comparison_authority"


def evidence_authority_scope(record: Any) -> Optional[str]:
    if not isinstance(record, Mapping):
        return None
    scope = record.get(AUTHORITY_SCOPE_KEY)
    return scope if scope in (FUNCTION_UNARY, COMPARISON) else None


def mark_function_unary(record: MutableMapping[str, Any]) -> MutableMapping[str, Any]:
    """``record`` を関数単体の事実として明示する（比較に束縛済みの record は変えない）。"""

    if record.get(AUTHORITY_SCOPE_KEY) == COMPARISON or COMPARISON_AUTHORITY_KEY in record:
        raise ValueError("a comparison-bound record cannot be relabelled as function-unary")
    record[AUTHORITY_SCOPE_KEY] = FUNCTION_UNARY
    return record


def record_function_unary_evidence(analysis: Any, record: MutableMapping[str, Any]) -> None:
    """関数単体の事実 ``record`` を ``analysis`` の証拠列の末尾に足す（analysis 層の書き込み口）。"""

    existing = tuple(getattr(analysis, "completed_recovery_proof_evidence", ()) or ())
    analysis.completed_recovery_proof_evidence = existing + (mark_function_unary(record),)
