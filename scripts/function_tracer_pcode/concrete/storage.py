# -*- coding: utf-8 -*-
"""Where a recovered value lives, as exact storage facts of the binary.

``StorageLocation`` is the concrete layer's own, minimal view of one storage
piece.  It records the *exact* position of the piece inside its base register
(``byte_offset_in_base``: first byte of the piece minus first byte of the base
register, in address order), not the position of whichever named register
contains the piece.  The two differ when no named register has the piece's
size -- a 1-byte value in the lowest-order byte of a big-endian 64-bit
register is contained in the low 32-bit sub-register but does not start where
that sub-register starts -- and a rule built on the named register would take
such a value for something other than the low part.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional


@dataclass(frozen=True)
class StorageLocation:
    is_register: bool
    # The register the storage facts name (the register found for the piece).
    register_name: Optional[str]
    base_register_name: Optional[str]
    base_register_bytes: int
    byte_offset_in_base: int
    size_bytes: int

    @classmethod
    def from_storage_info(cls, storage: Any, size_bytes: Optional[int] = None) -> "StorageLocation":
        """Build from a ``core.storage.StorageInfo`` (or an object shaped like it).

        ``size_bytes`` overrides the storage's own size with the size the
        recovered type gives the value, when the two are tracked separately.
        """
        is_register = bool(getattr(storage, "is_register", False))
        base_bits = int(getattr(storage, "base_register_size_bits", 0) or 0)
        offset = int(getattr(storage, "offset", 0) or 0)
        base_offset = int(getattr(storage, "base_register_offset", 0) or 0)
        return cls(
            is_register=is_register,
            register_name=getattr(storage, "register_name", None),
            base_register_name=getattr(storage, "base_register_name", None),
            base_register_bytes=base_bits // 8,
            byte_offset_in_base=offset - base_offset,
            size_bytes=int(size_bytes if size_bytes is not None else getattr(storage, "size", 0) or 0),
        )

    def names_whole_base_register(self) -> bool:
        """The storage names the base register itself.

        Then the value is that whole register and ``size_bytes`` is only the
        width the recovered type gives it: a type hypothesis can narrow the
        type of a value without moving its storage, which leaves a record
        whose offset is the register's own start.  The offset is not a
        position inside the register in that case.
        """
        return (
            self.is_register
            and self.register_name is not None
            and self.register_name == self.base_register_name
        )

    def is_low_order_part(self, big_endian: bool) -> bool:
        """The piece is the low-order ``size_bytes`` bytes of its base register."""
        if not self.is_register or self.size_bytes <= 0 or self.base_register_bytes <= 0:
            return False
        if self.size_bytes > self.base_register_bytes:
            return False
        if self.names_whole_base_register():
            return True
        if big_endian:
            return self.byte_offset_in_base + self.size_bytes == self.base_register_bytes
        return self.byte_offset_in_base == 0
