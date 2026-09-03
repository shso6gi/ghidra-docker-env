# -*- coding: utf-8 -*-
"""P-code intrinsic registry and lowering metadata."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional


PTRADD_OPCODE = 65
PTRSUB_OPCODE = 66
READONLY_SUM_OPCODE = 4097
COUNTED_LOOP_SUM_OPCODE = 4098
STATE_TRANSITION_LOOP_COUNT_OPCODE = 4099
COUNTED_STATE_TRANSITION_VALUE_OPCODE = 4100


@dataclass(frozen=True)
class PcodeIntrinsicSpec:
    """Metadata for first-class P-code intrinsic expressions."""

    opcode: int
    mnemonic: str
    arity: Optional[int] = None
    smt_lowerable: bool = False


_INTRINSIC_SPECS = (
    PcodeIntrinsicSpec(
        opcode=PTRADD_OPCODE,
        mnemonic="PTRADD",
        arity=3,
        smt_lowerable=True,
    ),
    PcodeIntrinsicSpec(
        opcode=PTRSUB_OPCODE,
        mnemonic="PTRSUB",
        arity=2,
        smt_lowerable=True,
    ),
    PcodeIntrinsicSpec(
        opcode=READONLY_SUM_OPCODE,
        mnemonic="READONLY_SUM",
        arity=2,
        smt_lowerable=True,
    ),
    PcodeIntrinsicSpec(
        opcode=COUNTED_LOOP_SUM_OPCODE,
        mnemonic="COUNTED_LOOP_SUM",
        arity=3,
        smt_lowerable=True,
    ),
    PcodeIntrinsicSpec(
        opcode=STATE_TRANSITION_LOOP_COUNT_OPCODE,
        mnemonic="STATE_TRANSITION_LOOP_COUNT",
        arity=1,
        smt_lowerable=True,
    ),
    PcodeIntrinsicSpec(
        opcode=COUNTED_STATE_TRANSITION_VALUE_OPCODE,
        mnemonic="COUNTED_STATE_TRANSITION_VALUE",
        arity=3,
        smt_lowerable=True,
    ),
    PcodeIntrinsicSpec(
        opcode=-1,
        mnemonic="NEON_ext",
        arity=4,
        smt_lowerable=True,
    ),
)

_BY_OPCODE: Dict[int, PcodeIntrinsicSpec] = {
    spec.opcode: spec for spec in _INTRINSIC_SPECS if spec.opcode >= 0
}
_BY_MNEMONIC: Dict[str, PcodeIntrinsicSpec] = {
    spec.mnemonic: spec for spec in _INTRINSIC_SPECS
}


def resolve_pcode_intrinsic(
    *,
    opcode: Optional[int] = None,
    mnemonic: Optional[str] = None,
) -> Optional[PcodeIntrinsicSpec]:
    """Resolve a P-code intrinsic by opcode first, then mnemonic."""
    if opcode is not None:
        spec = _BY_OPCODE.get(int(opcode))
        if spec is not None:
            return spec
    if mnemonic:
        return _BY_MNEMONIC.get(str(mnemonic))
    return None


def is_supported_pcode_intrinsic(
    *,
    opcode: Optional[int] = None,
    mnemonic: Optional[str] = None,
) -> bool:
    """Return True when the intrinsic has a sound SMT lowering."""
    spec = resolve_pcode_intrinsic(opcode=opcode, mnemonic=mnemonic)
    return bool(spec is not None and spec.smt_lowerable)
