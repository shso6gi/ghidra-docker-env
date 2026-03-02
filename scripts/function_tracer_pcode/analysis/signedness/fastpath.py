# -*- coding: utf-8 -*-
"""
Fast-path unsigned 検出モジュール

コンパイラ最適化によるfast-path unsignedパターンを検出し、
誤った符号性判定を防ぐ
"""

from typing import Optional, Set, Dict, Any, FrozenSet

from .varnode_analyzer import VarnodeAnalyzer


class FastPathDetector:
    """
    Fast-path unsigned パターンを検出するクラス
    
    検出対象:
    - INT_DIV, INT_REM, INT_RIGHT が下位化入力を使用
    - かつ、同一オペランドの上位ビットゼロチェックが条件分岐に存在
    
    使用方法:
        detector = FastPathDetector(high_function, debug=True)
        detector.collect_upper_zero_checks()
        reason = detector.check_fastpath(pcode_op)
        if reason:
            print(f"Fast-path detected: {reason}")
    """
    
    # fast-path 除外対象のオペコード
    TARGET_OPCODES: FrozenSet[str] = frozenset({
        "INT_DIV", 
        "INT_REM", 
        "INT_RIGHT"
    })
    
    def __init__(self, high_function, debug: bool = False):
        """
        Args:
            high_function: GhidraのHighFunctionオブジェクト
            debug: デバッグ出力を有効にする
        """
        self.high_function = high_function
        self.debug = debug
        self.varnode_analyzer = VarnodeAnalyzer(debug=debug)
        
        # 上位ビットゼロチェックが確認されたVarnodeキー集合
        self._upper_zero_checked_keys: Set[str] = set()
    
    def _debug_print(self, msg: str, indent: int = 0) -> None:
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[FastPathDetector] {msg}")
    
    def collect_upper_zero_checks(self) -> None:
        """
        条件分岐の上位ビットゼロチェックを収集
        
        High 2 対応: CBRANCH 経由の条件式のみを対象
        """
        self._upper_zero_checked_keys.clear()
        
        basic_blocks = self.high_function.getBasicBlocks()
        if basic_blocks is None:
            return
        
        for bb in basic_blocks:
            self._scan_block_for_cbranch(bb)
        
        if self.debug and self._upper_zero_checked_keys:
            self._debug_print(
                f"Collected {len(self._upper_zero_checked_keys)} upper-zero-check keys"
            )
    
    def _scan_block_for_cbranch(self, basic_block) -> None:
        """基本ブロック内のCBRANCHを走査"""
        try:
            pcode_iter = basic_block.getIterator()
            while pcode_iter.hasNext():
                pcode_op = pcode_iter.next()
                if pcode_op.getMnemonic() == "CBRANCH":
                    if pcode_op.getNumInputs() >= 2:
                        cond_vn = pcode_op.getInput(1)
                        self._analyze_cbranch_condition(cond_vn)
        except Exception:
            pass
    
    def _analyze_cbranch_condition(self, cond_varnode, depth: int = 0) -> None:
        """
        CBRANCH条件を解析して上位ビットゼロチェックを検出
        
        パターン:
        - (x >> 32) == 0
        - ((x | y) >> 32) == 0
        - SUBPIECE(x, 4) == 0
        """
        if cond_varnode is None or depth > 5:
            return
        
        def_op = cond_varnode.getDef()
        if def_op is None:
            return
        
        mnemonic = def_op.getMnemonic()
        
        # INT_EQUAL x, 0 パターン
        if mnemonic == "INT_EQUAL":
            self._check_equality_zero(def_op)
        
        # BOOL_NEGATE でラップされている場合（!= 0 パターン）
        elif mnemonic == "BOOL_NEGATE":
            if def_op.getNumInputs() >= 1:
                self._analyze_cbranch_condition(
                    def_op.getInput(0), depth + 1
                )
        
        # BOOL_AND / BOOL_OR（複合条件）
        elif mnemonic in ("BOOL_AND", "BOOL_OR"):
            for i in range(def_op.getNumInputs()):
                self._analyze_cbranch_condition(
                    def_op.getInput(i), depth + 1
                )
    
    def _check_equality_zero(self, pcode_op) -> None:
        """
        INT_EQUAL x, 0 パターンをチェック
        
        x が上位ビット抽出の場合、元のVarnodeキーを記録
        """
        if pcode_op.getNumInputs() < 2:
            return
        
        left_vn = pcode_op.getInput(0)
        right_vn = pcode_op.getInput(1)
        
        # どちらかが定数0
        zero_vn = None
        other_vn = None
        
        if right_vn.isConstant() and right_vn.getOffset() == 0:
            zero_vn = right_vn
            other_vn = left_vn
        elif left_vn.isConstant() and left_vn.getOffset() == 0:
            zero_vn = left_vn
            other_vn = right_vn
        else:
            return
        
        # other_vn が上位ビット抽出かチェック（キー集合を取得）
        source_keys = self.varnode_analyzer.detect_upper_extraction_sources(other_vn)
        
        if source_keys:
            self._upper_zero_checked_keys.update(source_keys)
            if self.debug:
                for key in source_keys:
                    self._debug_print(
                        f"Found upper-zero-check for: {key}", indent=1
                    )
    
    def check_fastpath(self, pcode_op) -> Optional[str]:
        """
        PcodeOpがfast-path unsignedパターンかを判定
        
        High 1 対応: 両方のオペランドをチェック
        
        Args:
            pcode_op: 対象のPcodeOp
            
        Returns:
            除外理由（fast-pathでない場合はNone）
        """
        mnemonic = pcode_op.getMnemonic()
        
        if mnemonic not in self.TARGET_OPCODES:
            return None
        
        # 両方のオペランドをチェック
        num_inputs = pcode_op.getNumInputs()
        
        for i in range(min(num_inputs, 2)):  # 最大2オペランド
            input_vn = pcode_op.getInput(i)
            if input_vn is None:
                continue
            
            # 下位化パターンを検出
            lower_info = self.varnode_analyzer.detect_lower_extraction(input_vn)
            if lower_info is None:
                continue
            
            source_key, pattern = lower_info
            
            # 上位ビットゼロチェックがあるか確認
            if source_key in self._upper_zero_checked_keys:
                operand_name = "first" if i == 0 else "second"
                return f"fast-path {pattern} on {operand_name} operand with upper-zero-check"
        
        return None
    
    def get_stats(self) -> Dict[str, Any]:
        """統計情報を取得"""
        return {
            "upper_zero_check_count": len(self._upper_zero_checked_keys),
            "upper_zero_check_keys": list(self._upper_zero_checked_keys),
        }