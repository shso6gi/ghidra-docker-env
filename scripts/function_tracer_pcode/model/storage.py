# -*- coding: utf-8 -*-
"""ストレージ情報のデータモデル"""

from dataclasses import dataclass
from typing import Optional, Dict, Any


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
    offset: int = 0
    size: int = 0
    size_bits: int = 0
    # レジスタの場合の追加情報
    register_name: Optional[str] = None
    base_register_name: Optional[str] = None
    base_register_offset: int = 0
    base_register_size: int = 0
    base_register_size_bits: int = 0
    # 親レジスタ内でのビットオフセット
    bit_offset_in_base: int = 0
    
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
        if not self.base_register_name or not other.base_register_name:
            return False
        
        return (self._normalize_reg_name(self.base_register_name) == 
                self._normalize_reg_name(other.base_register_name))
    
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
        
        # レジスタ名から上位/下位を判定
        if self.register_name and other.register_name:
            self_name = self._normalize_reg_name(self.register_name)
            other_name = self._normalize_reg_name(other.register_name)
            
            # _hi/_lo パターン
            if '_hi' in self_name or self_name.endswith('hi'):
                if '_lo' in other_name or other_name.endswith('lo'):
                    return True
            
            if '_lo' in self_name or self_name.endswith('lo'):
                if '_hi' in other_name or other_name.endswith('hi'):
                    return False
        
        # レジスタ名で判定できない場合:
        # 補完関係にあれば、selfを上位ビットとして扱う
        # （sign/zero extensionで正しく制約される）
        return True
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_register": self.is_register,
            "space_name": self.space_name,
            "offset": self.offset,
            "size": self.size,
            "size_bits": self.size_bits,
            "register_name": self.register_name,
            "base_register_name": self.base_register_name,
            "base_register_offset": self.base_register_offset,
            "base_register_size": self.base_register_size,
            "base_register_size_bits": self.base_register_size_bits,
            "bit_offset_in_base": self.bit_offset_in_base,
        }
