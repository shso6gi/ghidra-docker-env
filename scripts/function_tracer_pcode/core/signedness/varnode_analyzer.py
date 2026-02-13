# -*- coding: utf-8 -*-
"""
Varnode 解析ユーティリティ

Varnodeの同一性判定、透過的な追跡、パターン検出を提供
"""

from typing import Optional, Set, Tuple, FrozenSet, Any


class VarnodeAnalyzer:
    """
    Varnodeの解析を行うユーティリティクラス
    
    機能:
    - Varnode同一性キーの生成
    - 透過演算（COPY, CAST等）の追跡
    - 下位ビット抽出パターンの検出
    - 上位ビット抽出パターンの検出
    """
    
    # 透過的に追跡するオペコード（値を変えない演算）
    TRANSPARENT_OPCODES: FrozenSet[str] = frozenset({
        "COPY",
        "CAST",           # 型キャスト
        "MULTIEQUAL",     # PHI（透過追跡時は最初の入力を見る）
    })
    
    # 下位ビット抽出マスク（Phase 2: 明確な下位抽出のみ）
    LOWER_MASK_VALUES: FrozenSet[int] = frozenset({
        0xFFFFFFFF,       # 32ビット
        0xFFFF,           # 16ビット
        0xFF              # 8ビット
    })
    
    # 上位ビット抽出の最小シフト量（ビット単位）
    UPPER_SHIFT_THRESHOLD: int = 32
    
    # 上位ビット抽出の最小バイトオフセット
    UPPER_BYTE_OFFSET_THRESHOLD: int = 4
    
    def __init__(self, debug: bool = False):
        self.debug = debug
    
    def _debug_print(self, msg: str, indent: int = 0) -> None:
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[VarnodeAnalyzer] {msg}")
    
    def get_identity_key(self, varnode) -> Optional[str]:
        """
        Varnodeの同一性キーを生成
        
        同じ変数/レジスタを指すVarnodeは同じキーを返す
        透過演算を追跡して元のVarnodeのキーを返す
        
        Args:
            varnode: 対象のVarnode
            
        Returns:
            同一性キー（生成できない場合はNone）
        """
        if varnode is None:
            return None
        
        try:
            # 透過演算を追跡
            source_vn = self._trace_through_transparent_ops(varnode, max_depth=3)
            
            def_op = source_vn.getDef() if source_vn else None
            if def_op is not None:
                return self._get_op_key(def_op)
            
            # 入力パラメータや定数の場合
            if source_vn is not None:
                addr = source_vn.getAddress()
                if addr is not None:
                    space = addr.getAddressSpace()
                    space_name = space.getName() if space else "unknown"
                    return f"{space_name}:{source_vn.getOffset()}:{source_vn.getSize()}"
            
            return None
        except Exception:
            return None
    
    def _get_op_key(self, pcode_op) -> str:
        """PcodeOpの一意なキーを生成"""
        seq = pcode_op.getSeqnum()
        if seq:
            target = seq.getTarget()
            order = seq.getOrder()
            return f"{target}:{order}"
        return f"{pcode_op.hashCode()}:{pcode_op.getMnemonic()}"
    
    def _trace_through_transparent_ops(
        self, 
        varnode, 
        max_depth: int = 3
    ) -> Any:
        """
        透過演算を追跡して元のVarnodeを取得
        
        Args:
            varnode: 対象のVarnode
            max_depth: 最大追跡深度
            
        Returns:
            透過演算を追跡した後のVarnode
        """
        if varnode is None or max_depth <= 0:
            return varnode
        
        def_op = varnode.getDef()
        if def_op is None:
            return varnode
        
        mnemonic = def_op.getMnemonic()
        
        if mnemonic in self.TRANSPARENT_OPCODES:
            if def_op.getNumInputs() >= 1:
                return self._trace_through_transparent_ops(
                    def_op.getInput(0), max_depth - 1
                )
        
        return varnode
    
    def detect_lower_extraction(
        self, 
        varnode, 
        max_depth: int = 3
    ) -> Optional[Tuple[str, str]]:
        """
        下位ビット抽出パターンを検出
        
        検出パターン:
        - SUBPIECE(x, 0): 下位バイト抽出
        - INT_AND(x, mask): 下位ビットマスク
        
        Args:
            varnode: 対象のVarnode
            max_depth: 最大追跡深度
            
        Returns:
            (source_key, pattern_description) または None
        """
        if varnode is None or max_depth <= 0:
            return None
        
        def_op = varnode.getDef()
        if def_op is None:
            return None
        
        mnemonic = def_op.getMnemonic()
        
        # SUBPIECE(x, 0) パターン
        if mnemonic == "SUBPIECE":
            return self._check_subpiece_lower(def_op)
        
        # INT_AND(x, mask) パターン
        if mnemonic == "INT_AND":
            return self._check_and_mask_lower(def_op)
        
        # 透過演算を追跡
        if mnemonic in self.TRANSPARENT_OPCODES:
            if def_op.getNumInputs() >= 1:
                return self.detect_lower_extraction(
                    def_op.getInput(0), max_depth - 1
                )
        
        return None
    
    def _check_subpiece_lower(self, def_op) -> Optional[Tuple[str, str]]:
        """SUBPIECE(x, 0) パターンをチェック"""
        if def_op.getNumInputs() < 2:
            return None
        
        offset_vn = def_op.getInput(1)
        if not offset_vn.isConstant():
            return None
        
        if offset_vn.getOffset() != 0:
            return None
        
        source_vn = def_op.getInput(0)
        source_key = self.get_identity_key(source_vn)
        if source_key:
            return (source_key, "SUBPIECE(x,0)")
        
        return None
    
    def _check_and_mask_lower(self, def_op) -> Optional[Tuple[str, str]]:
        """INT_AND(x, mask) パターンをチェック"""
        if def_op.getNumInputs() < 2:
            return None
        
        left_vn = def_op.getInput(0)
        right_vn = def_op.getInput(1)
        
        # どちらがマスクか確認
        mask_vn = None
        source_vn = None
        
        if right_vn.isConstant():
            mask_vn = right_vn
            source_vn = left_vn
        elif left_vn.isConstant():
            mask_vn = left_vn
            source_vn = right_vn
        else:
            return None
        
        mask_val = mask_vn.getOffset()
        if mask_val not in self.LOWER_MASK_VALUES:
            return None
        
        source_key = self.get_identity_key(source_vn)
        if source_key:
            return (source_key, f"AND(x,0x{mask_val:X})")
        
        return None
    
    def detect_upper_extraction_sources(
        self, 
        varnode, 
        max_depth: int = 5
    ) -> Set[str]:
        """
        上位ビット抽出パターンの元Varnodeキー集合を取得
        
        検出パターン:
        - (x >> 32): 上位32ビット以上へのシフト
        - SUBPIECE(x, 4): 上位バイト抽出
        - (x | y) >> 32: OR結合後の上位抽出（両方のキーを返す）
        
        Args:
            varnode: 対象のVarnode
            max_depth: 最大追跡深度
            
        Returns:
            元Varnodeのキー集合
        """
        result: Set[str] = set()
        
        if varnode is None or max_depth <= 0:
            return result
        
        def_op = varnode.getDef()
        if def_op is None:
            return result
        
        mnemonic = def_op.getMnemonic()
        
        # INT_RIGHT x, shift パターン
        if mnemonic == "INT_RIGHT":
            sources = self._check_right_shift_upper(def_op, max_depth)
            result.update(sources)
        
        # SUBPIECE x, offset パターン
        elif mnemonic == "SUBPIECE":
            sources = self._check_subpiece_upper(def_op, max_depth)
            result.update(sources)
        
        # 透過演算を追跡
        elif mnemonic in self.TRANSPARENT_OPCODES:
            if def_op.getNumInputs() >= 1:
                sources = self.detect_upper_extraction_sources(
                    def_op.getInput(0), max_depth - 1
                )
                result.update(sources)
        
        return result
    
    def _check_right_shift_upper(self, def_op, max_depth: int) -> Set[str]:
        """INT_RIGHT x, shift_amount パターンをチェック"""
        result: Set[str] = set()
        
        if def_op.getNumInputs() < 2:
            return result
        
        source_vn = def_op.getInput(0)
        shift_vn = def_op.getInput(1)
        
        if not shift_vn.isConstant():
            return result
        
        shift_amount = shift_vn.getOffset()
        if shift_amount < self.UPPER_SHIFT_THRESHOLD:
            return result
        
        # 元のVarnodeから全てのソースキーを収集
        sources = self._collect_source_keys(source_vn, max_depth - 1)
        result.update(sources)
        
        return result
    
    def _check_subpiece_upper(self, def_op, max_depth: int) -> Set[str]:
        """SUBPIECE x, offset パターン（上位抽出）をチェック"""
        result: Set[str] = set()
        
        if def_op.getNumInputs() < 2:
            return result
        
        source_vn = def_op.getInput(0)
        offset_vn = def_op.getInput(1)
        
        if not offset_vn.isConstant():
            return result
        
        byte_offset = offset_vn.getOffset()
        if byte_offset < self.UPPER_BYTE_OFFSET_THRESHOLD:
            return result
        
        # 元のVarnodeから全てのソースキーを収集
        sources = self._collect_source_keys(source_vn, max_depth - 1)
        result.update(sources)
        
        return result
    
    def _collect_source_keys(self, varnode, max_depth: int) -> Set[str]:
        """
        Varnodeから元のソースキー集合を収集
        
        (x | y) のような複合式の場合、両方のキーを収集
        """
        result: Set[str] = set()
        
        if varnode is None or max_depth <= 0:
            return result
        
        def_op = varnode.getDef()
        if def_op is None:
            # リーフノード: 直接キーを取得
            key = self.get_identity_key(varnode)
            if key:
                result.add(key)
            return result
        
        mnemonic = def_op.getMnemonic()
        
        # 複合演算: 両方のオペランドからキーを収集
        if mnemonic in ("INT_OR", "INT_AND", "INT_XOR", "INT_ADD"):
            for i in range(def_op.getNumInputs()):
                input_vn = def_op.getInput(i)
                sources = self._collect_source_keys(input_vn, max_depth - 1)
                result.update(sources)
            return result
        
        # 透過演算
        if mnemonic in self.TRANSPARENT_OPCODES:
            if def_op.getNumInputs() >= 1:
                sources = self._collect_source_keys(
                    def_op.getInput(0), max_depth - 1
                )
                result.update(sources)
            return result
        
        # その他: 現在のVarnodeのキーを返す
        key = self.get_identity_key(varnode)
        if key:
            result.add(key)
        
        return result