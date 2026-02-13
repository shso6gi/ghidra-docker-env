# -*- coding: utf-8 -*-
"""符号性検出ロジック（Phase 2対応）"""

from typing import Optional, Set, Any, List

from .evidence import (
    SignednessType,
    EvidenceCategory,
    PcodeEvidence,
    SignednessEvidence,
    OPCODE_EVIDENCE_MAP,
    FASTPATH_UNSIGNED_OPCODES,
)
from .fastpath import FastPathDetector


class SignednessDetector:
    """
    P-codeから符号性証拠を収集し、戻り値の符号性を推定するクラス
    
    Phase 2:
    - RETURN chain 中心で証拠収集
    - fast-path unsigned パターンの除外
    - 同一オペランド性の検証
    
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
        
        # サブモジュール
        self.fastpath_detector = FastPathDetector(high_function, debug=debug)
        
        # 訪問済みPcodeOp
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
        Phase 2: RETURN chain 中心で符号性証拠を収集
        
        Returns:
            SignednessEvidence: 収集した証拠と判定結果
        """
        evidence = SignednessEvidence()
        self._visited_ops.clear()
        
        try:
            self._debug_print("Starting Phase 2 signedness detection (return-chain)")
            
            # 条件分岐の上位ビットゼロチェックを収集
            self.fastpath_detector.collect_upper_zero_checks()
            
            # RETURNを見つけてそこからデータフローを辿る
            return_ops = self._find_return_ops()
            self._debug_print(f"Found {len(return_ops)} RETURN operations")
            
            for return_op in return_ops:
                self._collect_evidence_from_return(return_op, evidence)
            
            evidence.determine_signedness()
            
            if self.debug:
                self._debug_print(f"Detection complete: {evidence.result.value}")
                self._debug_print(f"Summary: {evidence.get_summary()}")
                self._print_excluded_summary(evidence)
        
        except Exception as e:
            self._debug_print(f"Error during detection: {e}")
            evidence.result = SignednessType.UNKNOWN
        
        return evidence
    
    def _find_return_ops(self) -> List[Any]:
        """RETURNオペレーションを全て取得"""
        return_ops = []
        basic_blocks = self.high_function.getBasicBlocks()
        
        if basic_blocks is None:
            return return_ops
        
        for bb in basic_blocks:
            try:
                pcode_iter = bb.getIterator()
                while pcode_iter.hasNext():
                    pcode_op = pcode_iter.next()
                    if pcode_op.getMnemonic() == "RETURN":
                        return_ops.append(pcode_op)
            except Exception:
                continue
        
        return return_ops
    
    def _collect_evidence_from_return(
        self, 
        return_op, 
        evidence: SignednessEvidence
    ) -> None:
        """RETURNからデータフローを辿って証拠を収集"""
        if return_op.getNumInputs() < 2:
            self._debug_print("RETURN has no return value (void)")
            return
        
        return_varnode = return_op.getInput(1)
        addr = self._get_op_address(return_op)
        self._debug_print(f"Tracing return value from RETURN at {addr}")
        
        visited: Set[str] = set()
        self._trace_and_collect(
            return_varnode, evidence, visited, depth=0, max_depth=50
        )
    
    def _trace_and_collect(
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
        
        mnemonic = def_op.getMnemonic()
        
        # 証拠マップでチェック
        if mnemonic in OPCODE_EVIDENCE_MAP:
            self._process_evidence_op(def_op, mnemonic, evidence)
        
        # 入力を再帰的にトレース
        for i in range(def_op.getNumInputs()):
            input_vn = def_op.getInput(i)
            self._trace_and_collect(
                input_vn, evidence, visited, depth + 1, max_depth
            )
    
    def _process_evidence_op(
        self, 
        pcode_op, 
        mnemonic: str, 
        evidence: SignednessEvidence
    ) -> None:
        """証拠となるPcodeOpを処理"""
        category = OPCODE_EVIDENCE_MAP[mnemonic]
        address = self._get_op_address(pcode_op)
        
        pcode_evidence = PcodeEvidence(
            opcode=mnemonic,
            category=category,
            address=address,
        )
        
        # fast-path unsigned チェック
        if (mnemonic in FASTPATH_UNSIGNED_OPCODES and 
            category == EvidenceCategory.UNSIGNED):
            
            exclusion_reason = self.fastpath_detector.check_fastpath(pcode_op)
            
            if exclusion_reason:
                evidence.add_excluded_fastpath(pcode_evidence, exclusion_reason)
                self._debug_print(
                    f"Excluded fast-path: {mnemonic} at {address} - {exclusion_reason}",
                    indent=1
                )
                return
        
        # 通常の証拠として追加
        evidence.add_evidence(pcode_evidence)
        
        if self.debug and category != EvidenceCategory.IGNORED:
            self._debug_print(
                f"Found {category.value} evidence: {mnemonic} at {address}",
                indent=1
            )
    
    def _print_excluded_summary(self, evidence: SignednessEvidence) -> None:
        """除外されたfast-path証拠のサマリを出力"""
        if not evidence.excluded_fastpath:
            return
        
        self._debug_print(
            f"Excluded fast-path evidence: {len(evidence.excluded_fastpath)} item(s)"
        )
        
        opcode_counts = evidence.get_excluded_opcode_counts()
        for opcode, count in opcode_counts.items():
            self._debug_print(f"  {opcode}: {count}", indent=1)
    
    # ================================================================
    # 後方互換性メソッド（Phase 1互換）
    # ================================================================
    
    def detect_full_scan(self) -> SignednessEvidence:
        """
        全P-codeスキャンで証拠収集（Phase 1互換、非推奨）
        
        Returns:
            SignednessEvidence: 収集した証拠と判定結果
        """
        evidence = SignednessEvidence()
        self._visited_ops.clear()
        
        try:
            self._debug_print("Starting full P-code scan (Phase 1 compatible)")
            self._scan_all_pcode_ops(evidence)
            evidence.determine_signedness()
            
            if self.debug:
                self._debug_print(f"Detection complete: {evidence.result.value}")
                self._debug_print(f"Summary: {evidence.get_summary()}")
        
        except Exception as e:
            self._debug_print(f"Error during detection: {e}")
            evidence.result = SignednessType.UNKNOWN
        
        return evidence
    
    def _scan_all_pcode_ops(self, evidence: SignednessEvidence) -> None:
        """全てのPcodeOpをスキャンして証拠を収集（fast-pathチェックなし）"""
        basic_blocks = self.high_function.getBasicBlocks()
        
        if basic_blocks is None:
            self._debug_print("No basic blocks found")
            return
        
        for bb in basic_blocks:
            self._scan_basic_block_simple(bb, evidence)
    
    def _scan_basic_block_simple(
        self, 
        basic_block, 
        evidence: SignednessEvidence
    ) -> None:
        """基本ブロックをスキャン（シンプル版）"""
        try:
            pcode_iter = basic_block.getIterator()
            while pcode_iter.hasNext():
                pcode_op = pcode_iter.next()
                mnemonic = pcode_op.getMnemonic()
                
                op_key = self._get_op_key(pcode_op)
                if op_key in self._visited_ops:
                    continue
                self._visited_ops.add(op_key)
                
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
                            f"Found {category.value}: {mnemonic} at {address}"
                        )
        except Exception as e:
            self._debug_print(f"Error scanning basic block: {e}")
    
    def detect_from_return_chain(
        self, 
        return_varnode,
        max_depth: int = 50
    ) -> SignednessEvidence:
        """
        戻り値のデータフローチェーンのみをトレースして証拠を収集
        
        Args:
            return_varnode: 戻り値のVarnode
            max_depth: 最大トレース深度
        
        Returns:
            SignednessEvidence: 収集した証拠と判定結果
        """
        evidence = SignednessEvidence()
        self._visited_ops.clear()
        
        try:
            # fast-path検出の準備
            self.fastpath_detector.collect_upper_zero_checks()
            
            visited: Set[str] = set()
            self._trace_and_collect(
                return_varnode, evidence, visited, 0, max_depth
            )
            evidence.determine_signedness()
        except Exception as e:
            self._debug_print(f"Error in return chain detection: {e}")
            evidence.result = SignednessType.UNKNOWN
        
        return evidence