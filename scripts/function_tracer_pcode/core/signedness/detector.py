# -*- coding: utf-8 -*-
"""符号性検出ロジック"""

from typing import Optional, Set, Any, List

from .evidence import (
    SignednessType,
    EvidenceCategory,
    PcodeEvidence,
    SignednessEvidence,
    OPCODE_EVIDENCE_MAP,
)


class SignednessDetector:
    """
    P-codeから符号性証拠を収集し、戻り値の符号性を推定するクラス
    
    使用方法:
        detector = SignednessDetector(high_function, debug=True)
        evidence = detector.detect()
        print(f"Signedness: {evidence.result.value}")
    """
    
    def __init__(self, high_function, debug: bool = False):
        """
        Args:
            high_function: GhidraのHighFunctionオブジェクト
            debug: デバッグ出力を有効にする
        """
        self.high_function = high_function
        self.debug = debug
        self._visited_ops: Set[str] = set()
    
    def _debug_print(self, msg: str, indent: int = 0) -> None:
        """デバッグメッセージを出力"""
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[SignednessDetector] {msg}")
    
    def _get_op_key(self, pcode_op) -> str:
        """PcodeOpの一意なキーを生成"""
        seq = pcode_op.getSeqnum()
        if seq:
            target = seq.getTarget()
            order = seq.getOrder()
            return f"{target}:{order}"
        return f"{pcode_op.hashCode()}:{pcode_op.getMnemonic()}"
    
    def _get_op_address(self, pcode_op) -> Optional[str]:
        """PcodeOpのアドレスを取得"""
        try:
            seq = pcode_op.getSeqnum()
            if seq:
                return str(seq.getTarget())
        except Exception:
            pass
        return None
    
    def detect(self) -> SignednessEvidence:
        """
        High P-code全体をスキャンして符号性証拠を収集
        
        Returns:
            SignednessEvidence: 収集した証拠と判定結果
        """
        evidence = SignednessEvidence()
        
        try:
            self._debug_print("Starting signedness detection")
            self._scan_all_pcode_ops(evidence)
            evidence.determine_signedness()
            
            if self.debug:
                self._debug_print(f"Detection complete: {evidence.result.value}")
                self._debug_print(f"Summary: {evidence.get_summary()}")
        
        except Exception as e:
            self._debug_print(f"Error during detection: {e}")
            # エラー時もunknownとして継続
            evidence.result = SignednessType.UNKNOWN
        
        return evidence
    
    def _scan_all_pcode_ops(self, evidence: SignednessEvidence) -> None:
        """全てのPcodeOpをスキャンして証拠を収集"""
        basic_blocks = self.high_function.getBasicBlocks()
        
        if basic_blocks is None:
            self._debug_print("No basic blocks found")
            return
        
        for bb in basic_blocks:
            self._scan_basic_block(bb, evidence)
    
    def _scan_basic_block(self, basic_block, evidence: SignednessEvidence) -> None:
        """単一の基本ブロックをスキャン"""
        try:
            pcode_iter = basic_block.getIterator()
            while pcode_iter.hasNext():
                pcode_op = pcode_iter.next()
                self._process_pcode_op(pcode_op, evidence)
        except Exception as e:
            self._debug_print(f"Error scanning basic block: {e}")
    
    def _process_pcode_op(self, pcode_op, evidence: SignednessEvidence) -> None:
        """単一のPcodeOpを処理"""
        op_key = self._get_op_key(pcode_op)
        
        # 重複チェック
        if op_key in self._visited_ops:
            return
        self._visited_ops.add(op_key)
        
        mnemonic = pcode_op.getMnemonic()
        
        # 証拠マップでチェック
        if mnemonic in OPCODE_EVIDENCE_MAP:
            category = OPCODE_EVIDENCE_MAP[mnemonic]
            address = self._get_op_address(pcode_op)
            
            pcode_evidence = PcodeEvidence(
                opcode=mnemonic,
                category=category,
                address=address,
            )
            
            evidence.add_evidence(pcode_evidence)
            
            if self.debug and category != EvidenceCategory.IGNORED:
                self._debug_print(
                    f"Found {category.value} evidence: {mnemonic} at {address}"
                )
    
    def detect_from_return_chain(
        self, 
        return_varnode,
        max_depth: int = 50
    ) -> SignednessEvidence:
        """
        戻り値のデータフローチェーンのみをトレースして証拠を収集
        
        より精密な検出が必要な場合に使用（将来の拡張用）
        
        Args:
            return_varnode: 戻り値のVarnode
            max_depth: 最大トレース深度
        
        Returns:
            SignednessEvidence: 収集した証拠と判定結果
        """
        evidence = SignednessEvidence()
        visited: Set[str] = set()
        
        try:
            self._trace_varnode_for_evidence(
                return_varnode, evidence, visited, 0, max_depth
            )
            evidence.determine_signedness()
        except Exception as e:
            self._debug_print(f"Error in return chain detection: {e}")
            evidence.result = SignednessType.UNKNOWN
        
        return evidence
    
    def _trace_varnode_for_evidence(
        self,
        varnode,
        evidence: SignednessEvidence,
        visited: Set[str],
        depth: int,
        max_depth: int
    ) -> None:
        """Varnodeを再帰的にトレースして証拠を収集"""
        if varnode is None or depth > max_depth:
            return
        
        def_op = varnode.getDef()
        if def_op is None:
            return
        
        op_key = self._get_op_key(def_op)
        if op_key in visited:
            return
        visited.add(op_key)
        
        # 証拠をチェック
        self._process_pcode_op(def_op, evidence)
        
        # 入力を再帰的にトレース
        for i in range(def_op.getNumInputs()):
            input_vn = def_op.getInput(i)
            self._trace_varnode_for_evidence(
                input_vn, evidence, visited, depth + 1, max_depth
            )