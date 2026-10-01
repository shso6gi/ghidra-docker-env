# -*- coding: utf-8 -*-
"""ストレージ情報のデータモデル"""

from dataclasses import dataclass
from typing import Any, Dict, NamedTuple, Optional, Tuple
from scripts.function_tracer_pcode.core.json_encoding import scalar_record_dict


@dataclass
class StorageInfo:
    """
    ストレージ情報（レジスタ/メモリの位置情報）
    
    レジスタの場合、親レジスタ（ベースレジスタ）内でのビット位置を
    正確に追跡し、パラメータ断片の検出に使用する。
    
    例: MIPS64の64ビットレジスタ a1 に32ビットパラメータがある場合
    - a1_lo (下位32bit): bit_offset_in_base=32, size_bits=32
    - a1_hi (上位32bit): bit_offset_in_base=0, size_bits=32
    
    注意: ビッグエンディアンでは上位ビットが低いアドレスに配置されるため、
    a1_hi のオフセットが 0 になる。
    """
    is_register: bool = False
    space_name: str = ""
    space_id: Optional[int] = None
    offset: int = 0
    size: int = 0
    size_bits: int = 0
    # レジスタの場合の追加情報
    register_offset: int = 0
    register_size: int = 0
    register_size_bits: int = 0
    register_name: Optional[str] = None
    base_register_name: Optional[str] = None
    base_register_offset: int = 0
    base_register_size: int = 0
    base_register_size_bits: int = 0
    # 親レジスタ内でのビットオフセット
    bit_offset_in_base: int = 0
    is_stack_pointer: bool = False
    is_frame_pointer: bool = False

    def __post_init__(self) -> None:
        self.size = int(self.size or 0)
        self.size_bits = int(self.size_bits or (self.size * 8))
        self.offset = int(self.offset or 0)
        self.register_offset = int(self.register_offset or self.offset or 0)
        self.register_size = int(self.register_size or self.size or 0)
        self.register_size_bits = int(
            self.register_size_bits or (self.register_size * 8) or self.size_bits
        )
        self.base_register_size_bits = int(
            self.base_register_size_bits or self.register_size_bits or self.size_bits
        )
        self.base_register_size = int(
            self.base_register_size or ((self.base_register_size_bits + 7) // 8)
        )
        self.bit_offset_in_base = int(self.bit_offset_in_base or 0)

        if self.space_id is None and self.space_name:
            self.space_id = self._synthetic_space_id(self.space_name)

        if self.is_register:
            normalized_base = self._normalize_reg_name(
                self.base_register_name or self.register_name or ""
            )
            if not self.base_register_offset and normalized_base:
                self.base_register_offset = self._synthetic_register_offset(normalized_base)
            else:
                self.base_register_offset = int(self.base_register_offset or self.register_offset or 0)
            if not self.is_stack_pointer and normalized_base in {"sp", "wsp", "rsp", "esp"}:
                self.is_stack_pointer = True
            if not self.is_frame_pointer and normalized_base in {"rbp", "ebp", "bp", "fp", "s8", "x29"}:
                self.is_frame_pointer = True

    @staticmethod
    def _synthetic_space_id(name: str) -> int:
        normalized = str(name or "").strip().lower()
        if normalized == "register":
            return 0
        if normalized == "stack":
            return 1
        value = 0
        for ch in normalized:
            value = ((value * 131) + ord(ch)) & 0xFFFFFFFF
        return value

    @staticmethod
    def _synthetic_register_offset(name: str) -> int:
        normalized = StorageInfo._normalize_reg_name(name)
        if not normalized:
            return 0
        value = 0
        for ch in normalized:
            value = ((value * 131) + ord(ch)) & 0xFFFFFFFF
        return value or 1
    
    @staticmethod
    def _normalize_reg_name(name: str) -> str:
        """レジスタ名を正規化（$プレフィックス削除、小文字化）"""
        if not name:
            return ""
        return name.lstrip('$').lower()
    
    def shares_base_register_with(self, other: 'StorageInfo') -> bool:
        """同じ親レジスタを共有するかどうか"""
        if not self.is_register or not other.is_register:
            return False
        if self.base_register_size_bits <= 0 or other.base_register_size_bits <= 0:
            return False

        same_space = int(self.space_id or -1) == int(other.space_id or -1)
        if not same_space:
            same_space = (
                self._normalize_reg_name(self.space_name) == self._normalize_reg_name(other.space_name)
                and bool(self.space_name or other.space_name)
            )

        if (
            same_space
            and int(self.base_register_offset) == int(other.base_register_offset)
            and int(self.base_register_size_bits) == int(other.base_register_size_bits)
        ):
            return True

        self_base = self._normalize_reg_name(self.base_register_name or self.register_name or "")
        other_base = self._normalize_reg_name(other.base_register_name or other.register_name or "")
        if not self_base or not other_base:
            return False

        return (
            same_space
            and self_base == other_base
            and int(self.base_register_size_bits) == int(other.base_register_size_bits)
        )
    
    def bit_range_overlaps_with(self, other: 'StorageInfo') -> bool:
        """ビット範囲が重なるかどうか"""
        self_low = self.bit_offset_in_base
        self_high = self_low + self.size_bits
        other_low = other.bit_offset_in_base
        other_high = other_low + other.size_bits
        
        return not (self_high <= other_low or other_high <= self_low)
    
    def is_complement_of(self, other: 'StorageInfo') -> bool:
        """
        selfがotherの補完部分（残りのビット）かどうか
        
        条件:
        1. 同じ親レジスタを共有
        2. ビット範囲が重ならない
        3. 隣接している（selfとotherが連続したビット範囲を形成）
        4. 合計サイズが親レジスタのサイズと一致
        
        Returns:
            bool: selfがotherの補完部分である場合True
        """
        if not self.shares_base_register_with(other):
            return False
        
        # ビット範囲が重ならないか
        if self.bit_range_overlaps_with(other):
            return False
        
        # 親レジスタサイズの整合性チェック
        if self.base_register_size_bits <= 0 or other.base_register_size_bits <= 0:
            return False
        
        if self.base_register_size_bits != other.base_register_size_bits:
            return False
        
        # 合計サイズが親レジスタのサイズと一致するか
        if self.size_bits + other.size_bits != self.base_register_size_bits:
            return False
        
        # 隣接しているか（selfの終端がotherの開始、または逆）
        self_end = self.bit_offset_in_base + self.size_bits
        other_end = other.bit_offset_in_base + other.size_bits
        
        is_adjacent = (self_end == other.bit_offset_in_base or 
                       other_end == self.bit_offset_in_base)
        
        return is_adjacent
    
    def is_upper_bits_of(self, other: 'StorageInfo') -> bool:
        """
        selfがotherの上位ビット部分かどうか
        
        まず補完関係をチェックし、次にselfが「上位」であることを確認。
        
        上位/下位の判定:
        1. レジスタ名のパターン（_hi/_lo）
        2. 補完関係にある場合、パラメータ以外の部分を上位とみなす
        
        注意: 
        - ビッグエンディアンとリトルエンディアンでメモリ配置は異なる
        - しかし、sign/zero extensionの観点では、パラメータの「残り」は
          常に上位ビット（拡張される部分）として扱える
        """
        if not self.is_complement_of(other):
            return False

        # bit_offset_in_base は least-significant bit からの距離なので、
        # より大きい方が「上位ビット側」の断片になる。
        return self.bit_offset_in_base > other.bit_offset_in_base

    def register_identity_key(self):
        if not self.is_register:
            return None
        if self.base_register_size_bits <= 0:
            return None
        return (
            "register_storage",
            int(self.space_id or -1),
            int(self.base_register_offset),
            int(self.base_register_size_bits),
            int(self.bit_offset_in_base),
            int(self.size_bits),
        )

    def storage_identity_key(self):
        if self.is_register:
            return self.register_identity_key()
        return (
            "memory_storage",
            int(self.space_id or -1),
            int(self.offset),
            int(self.size),
        )
    
    def json_items(self):
        yield "is_register", self.is_register
        yield "space_name", self.space_name
        yield "space_id", self.space_id
        yield "offset", self.offset
        yield "size", self.size
        yield "size_bits", self.size_bits
        yield "register_offset", self.register_offset
        yield "register_size", self.register_size
        yield "register_size_bits", self.register_size_bits
        yield "register_name", self.register_name
        yield "base_register_name", self.base_register_name
        yield "base_register_offset", self.base_register_offset
        yield "base_register_size", self.base_register_size
        yield "base_register_size_bits", self.base_register_size_bits
        yield "bit_offset_in_base", self.bit_offset_in_base
        yield "is_stack_pointer", self.is_stack_pointer
        yield "is_frame_pointer", self.is_frame_pointer

    def to_dict(self) -> Dict[str, Any]:
        # 固定個数の scalar だけの record（式の木の node ごとに書くので walker を通さない）
        return scalar_record_dict(self)

    def frozen_record(self) -> "FrozenStorageRecord":
        """今の LEGACY 表現（`to_dict()`）の不変な写し（Issue #219）。

        `StorageInfo` は可変な dataclass なので、検証済みの式は凍結の時点の表現を
        これで持ち、以後は生の object を読まない（`core/semantic_freeze` が呼ぶ）。
        field が scalar でなければ `to_dict()` と同じく `TypeError`。
        """

        payload = scalar_record_dict(self)
        keys = tuple(payload)
        # key の並びは型ごとに固定なので、node ごとに持たずに 1 つを共有する
        keys = _FROZEN_RECORD_KEYS.setdefault(keys, keys)
        return FrozenStorageRecord(keys, tuple(payload.values()))


class FrozenStorageRecord(NamedTuple):
    """`StorageInfo.to_dict()` を凍結の時点で写した不変な値。

    値は scalar（とその subclass）だけで、容器は tuple なので、写した後に書き換わる
    状態を持たない。LEGACY 表現は `StorageInfo` と同じ規則（`scalar_record_dict`）で
    作るので、写した時点の `StorageInfo.to_dict()` と同じ dict になり、毎回新しい
    dict を返す（出力を書き換えても写しは動かない）。
    """

    keys: Tuple[str, ...]
    values: Tuple[Any, ...]

    def json_items(self):
        keys = self.keys
        values = self.values
        if type(keys) is not tuple:
            raise TypeError("FrozenStorageRecord.keys must be a tuple")
        if type(values) is not tuple:
            raise TypeError("FrozenStorageRecord.values must be a tuple")
        if len(keys) != len(values):
            raise TypeError("FrozenStorageRecord must hold one value per key")
        return zip(keys, values)

    def to_dict(self) -> Dict[str, Any]:
        # 固定個数の scalar だけの record（`StorageInfo.to_dict` と同じ規則）
        return scalar_record_dict(self)


#: `FrozenStorageRecord.keys` の共有表（key の並びは `json_items` が決める固定の形）。
_FROZEN_RECORD_KEYS: Dict[Tuple[str, ...], Tuple[str, ...]] = {}


def coerce_storage_info(storage: Any) -> Optional[StorageInfo]:
    """``StorageInfo`` か、その ``to_dict`` 形の dict を ``StorageInfo`` にする。

    parameter descriptor は storage を dict で持つことがあるので、storage の
    identity を比べる側（closure 走査、入力 extension 証拠、書き換え）はここを
    通して同じ解釈を使う。解釈できなければ None。
    """

    if storage is None:
        return None
    if isinstance(storage, StorageInfo):
        return storage
    if not isinstance(storage, dict):
        return None
    try:
        kind = str(storage.get("kind", "") or storage.get("space_name", "") or "").lower()
        is_register = bool(storage.get("is_register", False)) or kind == "register"
        return StorageInfo(
            is_register=is_register,
            space_name=str(storage.get("space_name") or ("register" if is_register else "")),
            space_id=storage.get("space_id"),
            offset=int(storage.get("offset", 0) or 0),
            size=int(storage.get("size", 0) or 0),
            size_bits=int(storage.get("size_bits", 0) or 0),
            register_name=storage.get("register_name"),
            register_offset=storage.get("register_offset"),
            register_size=storage.get("register_size"),
            register_size_bits=storage.get("register_size_bits"),
            base_register_name=storage.get("base_register_name"),
            base_register_offset=int(storage.get("base_register_offset", 0) or 0),
            base_register_size=int(storage.get("base_register_size", 0) or 0),
            base_register_size_bits=int(storage.get("base_register_size_bits", 0) or 0),
            bit_offset_in_base=int(storage.get("bit_offset_in_base", 0) or 0),
            is_stack_pointer=bool(storage.get("is_stack_pointer", False)),
            is_frame_pointer=bool(storage.get("is_frame_pointer", False)),
        )
    except (TypeError, ValueError):
        return None


def storage_identity_key_of(storage: Any) -> Optional[tuple]:
    """``coerce_storage_info`` 後の ``StorageInfo.storage_identity_key()``（無ければ None）。"""

    info = coerce_storage_info(storage)
    if info is None:
        return None
    try:
        return info.storage_identity_key()
    except (TypeError, ValueError):
        return None
