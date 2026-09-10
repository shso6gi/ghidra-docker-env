"""ABI-determined call-site argument extraction (Issue #20 PR-D).

効果レーンの経路列挙が届かなかった呼び出しサイトでも、**object 由来の ABI 証拠**
だけから引数証拠を作れるようにする。M-20 で確認したとおり、`ran/gammln` では
`log` の 2 箇所のうち 1 箇所が属するブロックが `complete_unreachable` と判定され、
`CallArgumentEvidence` 行が 1 件も作られない。その結果 `callee_parameter_keys=()`
となり callsite correspondence が成立しない。

ここでの ABI authority は **callee の宣言済み引数ストレージ**
(`VariableStorage` 由来の `StorageInfo`) と、**callsite の P-code 引数リスト**の
二つだけである。calling convention 名 (`PrototypeModel`) が取れることは要求しない。
M-20 では ET_REL のバイナリで外部 callee の convention が ``unknown`` でも
引数ストレージは ``d0:8`` のように具体値が取れることを確認している。

* convention 名が取れることは要求しない（取れなくてよい）
* **ordinal ごとの具体ストレージ**が無ければ fail closed
* 決定は次の二段で行い、どちらも成立しなければ fail closed

  tier A ``callee_declared_parameter_storage``
      宣言ストレージが callsite の入力ストレージと ordinal ごとに **一意**照合できる。

  tier B ``callsite_prototype_parameter_slots``
      高位 P-code では decompiler が ABI 受け渡しの COPY を畳み込むため、CALL 入力の
      register は「値を定義したレジスタ」であって ABI スロットとは限らない
      （M-20 の gammln arm64-O1: ``fmov d0,d1`` が畳まれ、ABI は d0 なのに入力は d1）。
      この場合は「CALL 入力 1..n は適用された prototype の引数を順番に並べたもの」と
      いう Ghidra の構造上の契約を authority とし、**宣言 arity の完全一致**と
      **ordinal ごとの幅の完全一致**を検証条件にする。

名前・callee 種別・「たぶんこの順番だろう」という推測では決めない。arity か幅が
一つでも合わなければ tier B も不成立とし、証拠行を作らない。

復元できなかったスロットは捨てず、``FreshCallArgumentRef`` を runtime ref に
持つ side-specific な UNKNOWN 式にする。左右の fresh は ``binary_id`` を含む
identity を持つので同一シンボルにならない。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import (
    AbiArgumentSlotRef,
    CallTargetRef,
    Condition,
    Expression,
    FreshCallArgumentRef,
    StorageInfo,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    CallArgumentEvidence,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _call_evidence_callee_param_identities,
    _call_target_ref_is_resolved,
    _callee_param_identities_are_object_proven,
    _coerce_storage_info,
    _normalize_call_argument_expression,
    _resolve_call_argument_expression,
    _storage_identity_key,
    _storage_matches_parameter,
)


#: ABI 決定の出所。証拠の種類を receipt / diagnostics に残すために型で持つ。
#:
#: tier A: callee の宣言済み引数ストレージが callsite の P-code 入力ストレージと
#:   ordinal ごとに一意照合できた場合。最も強い証拠。
#: tier B: 高位 P-code では decompiler が ABI の受け渡し COPY を畳み込むため、
#:   CALL 入力の register は「値を定義したレジスタ」であって ABI スロットとは
#:   限らない（M-20 の gammln arm64-O1: ABI は d0 だが入力は d1）。この場合は
#:   Ghidra の CALL 入力が「適用された prototype の引数リストを順番どおりに
#:   並べたもの」であるという契約を authority とし、**宣言 arity と ordinal ごとの
#:   幅が完全に一致すること**を検証条件にする。位置だけで埋めることはしない。
ABI_AUTHORITY_CALLEE_DECLARED_STORAGE = "callee_declared_parameter_storage"
ABI_AUTHORITY_CALLSITE_PROTOTYPE_SLOTS = "callsite_prototype_parameter_slots"

#: fail-closed の理由。どれも「推測すれば埋められる」ものだが、埋めない。
ABI_UNRESOLVED_TARGET = "abi_call_target_unresolved"
ABI_NO_CALLEE_PARAMETERS = "abi_callee_parameters_unavailable"
ABI_PARAMETER_STORAGE_MISSING = "abi_callee_parameter_storage_missing"
ABI_PARAMETER_IDENTITY_UNPROVEN = "abi_callee_parameter_identity_unproven"
ABI_CALLSITE_INPUTS_UNAVAILABLE = "abi_callsite_input_storage_unavailable"
ABI_SLOT_MATCH_AMBIGUOUS = "abi_callsite_slot_match_ambiguous"
ABI_CALLSITE_ARITY_MISMATCH = "abi_callsite_argument_arity_mismatch"
ABI_CALLSITE_WIDTH_MISMATCH = "abi_callsite_argument_width_mismatch"

#: 引数式が作れなかったスロットに付ける理由。
FRESH_ARGUMENT_UNTRACEABLE_INPUT = "abi_slot_input_not_traceable"


@dataclass(frozen=True)
class AbiCallArgumentSlot:
    """One resolved slot: identity + the expression occupying it (or a fresh ref)."""

    slot: AbiArgumentSlotRef
    expression: Expression
    fresh_ref: Optional[FreshCallArgumentRef] = None

    @property
    def is_fresh(self) -> bool:
        return self.fresh_ref is not None


@dataclass(frozen=True)
class AbiCallArgumentResolution:
    """A fully ABI-determined callsite argument list, or nothing at all.

    There is no partial success: either every declared ordinal was matched to a
    distinct callsite input storage, or the resolution fails closed.  Slots whose
    *expression* could not be traced still count as resolved — they carry a fresh
    reference, which is a recorded unknown, not a guess.
    """

    authority_source: str
    slots: Tuple[AbiCallArgumentSlot, ...]

    @property
    def arguments(self) -> Tuple[Expression, ...]:
        return tuple(item.expression for item in self.slots)

    @property
    def slot_refs(self) -> Tuple[AbiArgumentSlotRef, ...]:
        return tuple(item.slot for item in self.slots)

    @property
    def fresh_refs(self) -> Tuple[FreshCallArgumentRef, ...]:
        return tuple(item.fresh_ref for item in self.slots if item.fresh_ref is not None)

    @property
    def has_fresh_arguments(self) -> bool:
        return any(item.is_fresh for item in self.slots)

    def sources(self) -> Tuple[str, ...]:
        return tuple(
            "abi_fresh_argument" if item.is_fresh else self.authority_source
            for item in self.slots
        )


def _impl__abi_storage_class(storage: Optional[StorageInfo]) -> Optional[str]:
    storage = _coerce_storage_info(storage)
    if storage is None:
        return None
    if getattr(storage, "is_register", False):
        return "register"
    space_name = str(getattr(storage, "space_name", "") or "").strip().lower()
    return space_name or None


def _impl__abi_argument_slot_ref(ordinal: int, callee_param: Mapping[str, Any]) -> Optional[AbiArgumentSlotRef]:
    """Build the slot identity for one declared callee parameter.

    ``None`` when the parameter has no concrete storage: that is the fail-closed
    condition, not something to fill in from the ordinal alone.
    """

    storage = _coerce_storage_info((callee_param or {}).get("storage"))
    if storage is None:
        return None
    identity_key = _storage_identity_key(storage)
    if identity_key is None:
        return None
    size_bits = int(getattr(storage, "size_bits", 0) or 0)
    if size_bits <= 0:
        size_bits = int(getattr(storage, "size", 0) or 0) * 8
    if size_bits <= 0:
        return None
    declared_type = (callee_param or {}).get("data_type")
    return AbiArgumentSlotRef(
        ordinal=int(ordinal),
        storage_class=_impl__abi_storage_class(storage),
        width_bits=size_bits,
        storage_identity_key=tuple(identity_key),
        declared_type_name=str(declared_type) if declared_type is not None else None,
    )


def _impl__callee_parameter_storages_are_abi_complete(
    callee_parameters: Sequence[Mapping[str, Any]],
) -> bool:
    """Every declared parameter carries a concrete, object-derived storage."""

    if not callee_parameters:
        return False
    for callee_param in callee_parameters:
        if _coerce_storage_info((callee_param or {}).get("storage")) is None:
            return False
        if _storage_identity_key(_coerce_storage_info((callee_param or {}).get("storage"))) is None:
            return False
    return True


def _impl__callsite_input_storages(call_op, tracer) -> Optional[List[Optional[StorageInfo]]]:
    """Storage of each callsite P-code input (``op.getInput(1..n)``)."""

    try:
        input_count = int(call_op.getNumInputs())
    except Exception:
        return None
    if input_count <= 1:
        return None
    get_input = getattr(call_op, "getInput", None)
    get_storage = getattr(tracer, "_get_storage_info_from_varnode", None)
    if not callable(get_input) or not callable(get_storage):
        return None
    storages: List[Optional[StorageInfo]] = []
    for index in range(1, input_count):
        try:
            varnode = get_input(index)
        except Exception:
            return None
        try:
            storages.append(_coerce_storage_info(get_storage(varnode)))
        except Exception:
            storages.append(None)
    return storages


def _impl__callsite_input_widths(call_op) -> Optional[List[int]]:
    """Bit width of each callsite P-code argument input."""

    try:
        input_count = int(call_op.getNumInputs())
    except Exception:
        return None
    if input_count <= 1:
        return None
    get_input = getattr(call_op, "getInput", None)
    if not callable(get_input):
        return None
    widths: List[int] = []
    for index in range(1, input_count):
        try:
            varnode = get_input(index)
            size = int(varnode.getSize())
        except Exception:
            return None
        if size <= 0:
            return None
        widths.append(size * 8)
    return widths


def _impl__abi_slot_input_assignment(
    call_op,
    tracer,
    callee_parameters: Sequence[Mapping[str, Any]],
) -> Tuple[Optional[str], Optional[List[int]], Optional[str]]:
    """Decide which callsite input index carries each declared ordinal.

    Returns ``(authority_source, input_index_per_ordinal, None)`` on success and
    ``(None, None, reason)`` when the assignment cannot be established without
    guessing.
    """

    input_storages = _impl__callsite_input_storages(call_op, tracer)
    input_widths = _impl__callsite_input_widths(call_op)
    if input_storages is None or input_widths is None:
        return None, None, ABI_CALLSITE_INPUTS_UNAVAILABLE

    # tier A: exact, unique storage identity match per ordinal.
    assignment: List[int] = []
    used: set = set()
    storage_match_complete = True
    for callee_param in callee_parameters:
        param_storage = _coerce_storage_info((callee_param or {}).get("storage"))
        if param_storage is None:
            storage_match_complete = False
            break
        matches = [
            index
            for index, input_storage in enumerate(input_storages)
            if index not in used
            and input_storage is not None
            and _storage_matches_parameter(input_storage, param_storage)
        ]
        if len(matches) != 1:
            storage_match_complete = False
            break
        used.add(matches[0])
        assignment.append(matches[0])
    if storage_match_complete and len(assignment) == len(callee_parameters):
        return ABI_AUTHORITY_CALLEE_DECLARED_STORAGE, assignment, None

    # tier B: Ghidra's CALL inputs are the applied prototype's parameters in
    # order.  Accept that ordering only when the callsite agrees with the
    # declared signature on arity *and* on every ordinal's width.
    if len(input_widths) != len(callee_parameters):
        return None, None, ABI_CALLSITE_ARITY_MISMATCH
    for ordinal, callee_param in enumerate(callee_parameters):
        slot_ref = _impl__abi_argument_slot_ref(ordinal, callee_param)
        if slot_ref is None:
            return None, None, ABI_PARAMETER_STORAGE_MISSING
        if int(slot_ref.width_bits or 0) != int(input_widths[ordinal]):
            return None, None, ABI_CALLSITE_WIDTH_MISMATCH
    return ABI_AUTHORITY_CALLSITE_PROTOTYPE_SLOTS, list(range(len(callee_parameters))), None


def _impl__resolve_abi_call_arguments(
    call_op,
    tracer,
    caller_parameters: Sequence[Mapping[str, Any]],
    callee_parameters: Sequence[Mapping[str, Any]],
    *,
    binary_id: Optional[str],
    call_site_key: Optional[Tuple[Any, ...]],
) -> Tuple[Optional[AbiCallArgumentResolution], Optional[str]]:
    """Resolve a callsite's arguments from declared ABI storage.

    Returns ``(resolution, None)`` on success and ``(None, reason)`` when the ABI
    could not be determined without guessing.
    """

    if not callee_parameters:
        return None, ABI_NO_CALLEE_PARAMETERS
    if not _impl__callee_parameter_storages_are_abi_complete(callee_parameters):
        return None, ABI_PARAMETER_STORAGE_MISSING

    identities = _call_evidence_callee_param_identities(callee_parameters)
    if len(identities) != len(callee_parameters) or not _callee_param_identities_are_object_proven(identities):
        return None, ABI_PARAMETER_IDENTITY_UNPROVEN

    authority_source, assignment, reason = _impl__abi_slot_input_assignment(
        call_op,
        tracer,
        callee_parameters,
    )
    if authority_source is None or assignment is None:
        return None, reason or ABI_SLOT_MATCH_AMBIGUOUS

    get_input = getattr(call_op, "getInput", None)
    slots: List[AbiCallArgumentSlot] = []
    for ordinal, callee_param in enumerate(callee_parameters):
        slot_ref = _impl__abi_argument_slot_ref(ordinal, callee_param)
        if slot_ref is None:
            return None, ABI_PARAMETER_STORAGE_MISSING
        input_index = assignment[ordinal]

        expression = None
        try:
            varnode = get_input(input_index + 1)
        except Exception:
            varnode = None
        if varnode is not None:
            try:
                expression = _resolve_call_argument_expression(varnode, tracer, caller_parameters)
            except Exception:
                expression = None
        if expression is not None:
            try:
                expression = _normalize_call_argument_expression(expression, ordinal, caller_parameters)
            except Exception:
                pass
        if expression is None:
            fresh_ref = FreshCallArgumentRef(
                binary_id=binary_id,
                slot=slot_ref,
                call_site_key=call_site_key,
                reason=FRESH_ARGUMENT_UNTRACEABLE_INPUT,
            )
            slots.append(
                AbiCallArgumentSlot(
                    slot=slot_ref,
                    expression=_impl__fresh_call_argument_expression(fresh_ref),
                    fresh_ref=fresh_ref,
                )
            )
            continue
        slots.append(AbiCallArgumentSlot(slot=slot_ref, expression=expression))

    return (
        AbiCallArgumentResolution(
            authority_source=authority_source,
            slots=tuple(slots),
        ),
        None,
    )


def _impl__fresh_call_argument_expression(fresh_ref: FreshCallArgumentRef) -> Expression:
    """A side-specific free symbol for one unrecovered argument slot.

    The UNKNOWN SMT symbol is derived from ``runtime_ref.stable_key()``, which
    includes ``binary_id``; the left and the right side therefore declare two
    different constants without any further coordination.
    """

    runtime_ref = UnknownValueRef(
        kind="fresh_call_argument",
        reason=fresh_ref.reason,
        origin_kind="abi_call_argument_slot",
        origin_ref=fresh_ref,
        display_hint=fresh_ref.display_name(),
    )
    expression = Expression.unknown(fresh_ref.display_name(), runtime_ref=runtime_ref)
    width_bits = int(fresh_ref.slot.width_bits or 0)
    if width_bits > 0:
        expression.size = max(1, width_bits // 8)
    return expression


def _impl__abi_call_argument_evidence(
    call_op,
    tracer,
    target_ref: Optional[CallTargetRef],
    callee_parameters: Sequence[Mapping[str, Any]],
    resolution: AbiCallArgumentResolution,
    path_conditions: Sequence[Condition] = (),
) -> Optional[CallArgumentEvidence]:
    """Build a ``CallArgumentEvidence`` row from an ABI resolution.

    ``coverage_complete`` is asserted only when every declared ordinal was
    matched *and* every slot carries a traced expression.  A resolution holding
    fresh slots is recorded as ``recoverable_partial``: the arity is known and
    the correspondence inputs exist, but the values are not observed, so it must
    not be used as if the arguments had been recovered.
    """

    make_ref = getattr(tracer, "_make_pcode_op_ref", None)
    if not callable(make_ref):
        return None
    pcode_op_ref = make_ref(call_op)
    if pcode_op_ref is None:
        return None
    if not _call_target_ref_is_resolved(target_ref):
        return None

    identities = _call_evidence_callee_param_identities(callee_parameters)
    if len(identities) != len(callee_parameters) or not _callee_param_identities_are_object_proven(identities):
        return None

    coverage_complete = not resolution.has_fresh_arguments
    recovery_status = (
        CallArgumentEvidence.RECOVERY_COMPLETE
        if coverage_complete
        else CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    )
    # 経路条件は「観測できたものだけ」を載せる。ABI 復元は効果レーンの経路列挙が
    # 届かなかった callsite を拾うためのもので、guard は分かっていない。空の
    # guard group を 1 つ積むと「無条件で実行される」と読めてしまうため、
    # 条件が無いときは group そのものを作らない（無条件だと主張しない）。
    normalized_path_conditions = tuple(path_conditions or ())
    guard_groups = (normalized_path_conditions,) if normalized_path_conditions else ()
    return CallArgumentEvidence(
        pcode_op_ref=pcode_op_ref,
        target_ref=target_ref,
        callee_param_identities=identities,
        arguments=resolution.arguments,
        sources=resolution.sources(),
        path_conditions=guard_groups,
        coverage_complete=coverage_complete,
        recovery_status=recovery_status,
        reason=(
            None
            if coverage_complete
            else "abi_argument_slots_resolved_with_fresh_values"
        ),
        abi_argument_slots=resolution.slot_refs,
        fresh_argument_refs=resolution.fresh_refs,
    )


def _impl__recover_abi_call_argument_evidence(
    call_op,
    tracer,
    caller_parameters: Sequence[Mapping[str, Any]],
    callee_parameters: Sequence[Mapping[str, Any]],
    target_ref: Optional[CallTargetRef],
    *,
    binary_id: Optional[str],
    path_conditions: Sequence[Condition] = (),
) -> Tuple[Optional[CallArgumentEvidence], Optional[str]]:
    """Full ABI recovery for one callsite: identity → resolution → evidence."""

    if not _call_target_ref_is_resolved(target_ref):
        return None, ABI_UNRESOLVED_TARGET
    make_ref = getattr(tracer, "_make_pcode_op_ref", None)
    pcode_op_ref = make_ref(call_op) if callable(make_ref) else None
    call_site_key = None
    if pcode_op_ref is not None:
        try:
            call_site_key = tuple(pcode_op_ref.stable_key())
        except Exception:
            call_site_key = None

    resolution, reason = _impl__resolve_abi_call_arguments(
        call_op,
        tracer,
        caller_parameters,
        callee_parameters,
        binary_id=binary_id,
        call_site_key=call_site_key,
    )
    if resolution is None:
        return None, reason
    evidence = _impl__abi_call_argument_evidence(
        call_op,
        tracer,
        target_ref,
        callee_parameters,
        resolution,
        path_conditions=path_conditions,
    )
    if evidence is None:
        return None, ABI_PARAMETER_IDENTITY_UNPROVEN
    return evidence, None


def _impl__abi_argument_slot_keys_for_evidence(
    evidence: Optional[CallArgumentEvidence],
) -> Tuple[Tuple[Any, ...], ...]:
    """Identity-correspondence keys carried by an evidence row's arguments."""

    slot_keys: List[Tuple[Any, ...]] = []
    for argument in getattr(evidence, "arguments", ()) or ():
        runtime_ref = getattr(argument, "runtime_ref", None)
        origin_ref = getattr(runtime_ref, "origin_ref", None)
        if isinstance(origin_ref, FreshCallArgumentRef):
            slot_keys.append(origin_ref.identity_correspondence_key())
    return tuple(slot_keys)


def _impl__collect_fresh_call_argument_refs(expr: Any) -> Tuple[FreshCallArgumentRef, ...]:
    """Every fresh call-argument reference reachable from ``expr``."""

    found: List[FreshCallArgumentRef] = []
    seen: set = set()
    pending: List[Any] = [expr]
    while pending:
        current = pending.pop()
        if current is None:
            continue
        runtime_ref = getattr(current, "runtime_ref", None)
        origin_ref = getattr(runtime_ref, "origin_ref", None)
        if isinstance(origin_ref, FreshCallArgumentRef):
            key = origin_ref.stable_key()
            if key not in seen:
                seen.add(key)
                found.append(origin_ref)
        value = getattr(current, "value", None)
        expr_type = getattr(current, "expr_type", None)
        if expr_type is not None and getattr(expr_type, "name", "") == "PHI" and value:
            for condition, branch in value:
                if branch is not None:
                    pending.append(branch)
                condition_expr = getattr(condition, "expression", None) if condition is not None else None
                if condition_expr is not None:
                    pending.append(condition_expr)
            continue
        pending.extend([item for item in (getattr(current, "operands", None) or []) if item is not None])
    return tuple(found)
