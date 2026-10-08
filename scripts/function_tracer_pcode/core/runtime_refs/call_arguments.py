"""Call-argument ABI slot identities and side-specific fresh argument references.

三つの概念を型として分離する（Issue #20 PR-D）。

``AbiArgumentSlotRef``
    **identity correspondence** のみ。「左の第 n 引数スロットは右の第 n 引数
    スロットの対応候補である」ことだけを表し、二つのスロットが同じ値を持つ
    ことは一切主張しない。``binary_id`` を含まないので左右で比較できる。

``FreshCallArgumentRef``
    復元できなかった引数スロットを表す **side-specific** な自由シンボル。
    ``binary_id`` が identity に入るので、ABI ordinal / storage / 幅が一致
    していても左右の fresh が同じシンボルになることは構造的に起こらない。
    同一シンボルへの **value coupling** は relational equality proof が
    与えられた場合のみ許され、それは proof 層が所有する（本 DTO は許可の
    記録場所を持たない）。

``proof irrelevance`` は本 DTO では表現しない。fresh を独立のまま保ち、
「その値が decisive predicate に影響しない」ことを別の proof obligation で
示すのが正しい扱いであり、irrelevance を identity の統合として書き込んでは
いけない。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record
from scripts.function_tracer_pcode.core.json_encoding import (as_list, each, inline, is_json_record, mapping_of, materialize, nested, raw)
from scripts.function_tracer_pcode.core.live_values import as_int, as_str, attribute, scalar_int, scalar_text


_ABI_SLOT_KIND = "abi_argument_slot"
_FRESH_ARGUMENT_KIND = "fresh_call_argument"


def _optional_text(value: Any) -> Optional[str]:
    if value is None:
        return None
    text = scalar_text(value).strip()
    return text or None


def _optional_int(value: Any) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    try:
        return scalar_int(value)
    except (TypeError, ValueError):
        return None


@dataclass(frozen=True)
@runtime_ref_record
class AbiArgumentSlotRef:
    """One ABI-determined argument slot of a call site.

    This is an *identity correspondence* key: two slots with the same
    ``stable_key()`` are candidate counterparts of each other.  It carries no
    claim about the values held in those slots.
    """

    ordinal: int
    storage_class: Optional[str] = None
    width_bits: Optional[int] = None
    storage_identity_key: Optional[Tuple[Any, ...]] = None
    declared_type_name: Optional[str] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "ordinal", scalar_int(self.ordinal))
        object.__setattr__(self, "storage_class", _optional_text(self.storage_class))
        object.__setattr__(self, "width_bits", _optional_int(self.width_bits))
        object.__setattr__(self, "declared_type_name", _optional_text(self.declared_type_name))
        key = self.storage_identity_key
        object.__setattr__(
            self,
            "storage_identity_key",
            tuple(key) if isinstance(key, (tuple, list)) else None,
        )

    def stable_key(self) -> Tuple[Any, ...]:
        """Cross-binary comparable identity.

        ``binary_id`` is deliberately absent: the whole point of this key is
        that the left and the right side can produce the *same* value for
        corresponding slots.
        """

        return (
            _ABI_SLOT_KIND,
            self.ordinal,
            self.storage_class,
            self.width_bits,
        )

    def provenance_key(self) -> Tuple[Any, ...]:
        """Full per-side detail, including the concrete storage identity.

        Used for diagnostics and for validating that two candidate-corresponding
        slots really were derived from the same kind of ABI evidence.  It is not
        the correspondence key.
        """

        return self.stable_key() + (self.storage_identity_key, self.declared_type_name)

    def json_items(self):
        yield "kind", _ABI_SLOT_KIND
        yield "ordinal", self.ordinal
        yield "storage_class", self.storage_class
        yield "width_bits", self.width_bits
        yield "storage_identity_key", (
            as_list(self.storage_identity_key)
            if self.storage_identity_key is not None
            else None
        )
        yield "declared_type_name", self.declared_type_name

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


class MissingSideDiscriminator(ValueError):
    """Raised when a fresh argument cannot be made side-specific.

    左右独立は「``binary_id`` が入っていれば保たれる」という約束ではなく、
    **discriminator が必ず存在する**ことで担保する。取得できないなら fresh を
    発行してはならない（``unknown_binary`` 等に丸めると左右が同じシンボルに
    潰れ、証明していない値の一致を主張することになる）。
    """


@dataclass(frozen=True)
@runtime_ref_record
class FreshCallArgumentRef:
    """A side-specific free symbol standing for one unrecovered call argument.

    ``binary_id`` participates in ``stable_key()`` and is **required to be a
    non-empty discriminator**.  Unknown-expression SMT symbols are derived from
    that key, so a left fresh argument and a right fresh argument are distinct
    symbols by construction; nothing downstream has to remember to keep them
    apart, and nothing may fall back to a shared placeholder.
    """

    binary_id: str
    slot: AbiArgumentSlotRef
    call_site_key: Optional[Tuple[Any, ...]] = None
    reason: str = "call_argument_unrecovered"

    def __post_init__(self) -> None:
        discriminator = _optional_text(self.binary_id)
        if discriminator is None:
            raise MissingSideDiscriminator(
                "fresh call argument requires a non-empty side discriminator"
            )
        object.__setattr__(self, "binary_id", discriminator)
        object.__setattr__(self, "reason", _optional_text(self.reason) or "call_argument_unrecovered")
        key = self.call_site_key
        object.__setattr__(
            self,
            "call_site_key",
            tuple(key) if isinstance(key, (tuple, list)) else None,
        )
        if not isinstance(self.slot, AbiArgumentSlotRef):
            raise TypeError("fresh call argument requires an AbiArgumentSlotRef slot")

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            _FRESH_ARGUMENT_KIND,
            self.binary_id,
            self.call_site_key,
            self.slot.stable_key(),
            self.reason,
        )

    def identity_correspondence_key(self) -> Tuple[Any, ...]:
        """The slot identity this fresh value occupies.

        Two fresh arguments sharing this key are candidate counterparts.  They
        remain *different symbols*: correspondence of the slot is not equality
        of the value.
        """

        return self.slot.stable_key()

    def display_name(self) -> str:
        # discriminator は __post_init__ で保証済み。ここで既定値へ丸めない。
        # field は owner の API で読む（`__post_init__` が str / int に正規化済みなので同じ文字列）
        return f"fresh_{as_str(self.binary_id)}_arg{as_int(attribute(self.slot, 'ordinal'))}"

    def json_items(self):
        yield "kind", _FRESH_ARGUMENT_KIND
        yield "binary_id", self.binary_id
        yield "slot", self.slot
        yield "call_site_key", as_list(self.call_site_key) if self.call_site_key is not None else None
        yield "reason", self.reason
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


def fresh_call_argument_refs_are_side_distinct(
    left: Optional[FreshCallArgumentRef],
    right: Optional[FreshCallArgumentRef],
) -> bool:
    """True when two fresh arguments are guaranteed to be different symbols.

    Used by tests and by the proof layer to assert the invariant rather than
    trusting it: matching ABI slots must never collapse into one symbol.
    """

    if left is None or right is None:
        return False
    return left.stable_key() != right.stable_key()
