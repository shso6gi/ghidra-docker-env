# -*- coding: utf-8 -*-
"""符号性検出ロジック（Phase 2対応）"""

from typing import Optional, Set, Any, List, Dict, Tuple

from .evidence import (
    SignednessType,
    EvidenceCategory,
    PcodeEvidence,
    SignednessEvidence,
    OPCODE_EVIDENCE_MAP,
    FASTPATH_UNSIGNED_OPCODES,
)


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
    
    # 下位ビットを抽出するマスク値
    LOWER_MASK_VALUES = frozenset([
        0xFFFFFFFF,      # 32ビット
        0xFFFF,          # 16ビット
        0xFF,            # 8ビット
        0x7FFFFFFF,      # 31ビット（符号ビット除く）
    ])
    
    def __init__(self, high_function, debug: bool = False):
        """
        Args:
            high_function: GhidraのHighFunctionオブジェクト
            debug: デバッグ出力を有効にする
        """
        self.high_function = high_function
        self.debug = debug
        self._visited_ops: Set[str] = set()
        # Phase 2: 条件分岐キャッシュ
        self._branch_conditions: Optional[Dict[str, Any]] = None
        self._upper_zero_check_varnodes: Optional[Set[str]] = None
    
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
    
    def _get_varnode_identity_key(self, varnode) -> Optional[str]:
        """
        Phase 2: Varnodeの同一性キーを生成
        
        同じ変数/レジスタを指すVarnodeは同じキーを返す
        """
        if varnode is None:
            return None
        
        try:
            # 定義元がある場合はそのキー
            def_op = varnode.getDef()
            if def_op is not None:
                return self._get_op_key(def_op)
            
            # 入力パラメータや定数の場合
            addr = varnode.getAddress()
            if addr is not None:
                space = addr.getAddressSpace()
                space_name = space.getName() if space else "unknown"
                return f"{space_name}:{varnode.getOffset()}:{varnode.getSize()}"
            
            return None
        except Exception:
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
            
            # 条件分岐の上位ビットゼロチェックを事前収集
            self._collect_upper_zero_check_conditions()
            
            # RETURNを見つけてそこからデータフローを辿る
            return_ops = self._find_return_ops()
            self._debug_print(f"Found {len(return_ops)} RETURN operations")
            
            for return_op in return_ops:
                self._collect_evidence_from_return(return_op, evidence)
            
            evidence.determine_signedness()
            
            if self.debug:
                self._debug_print(f"Detection complete: {evidence.result.value}")
                self._debug_print(f"Summary: {evidence.get_summary()}")
                self._print_excluded_fastpath_summary(evidence)
        
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
        """
        RETURNからデータフローを辿って証拠を収集
        """
        # RETURNの入力（戻り値）を取得
        if return_op.getNumInputs() < 2:
            self._debug_print("RETURN has no return value (void)")
            return
        
        return_varnode = return_op.getInput(1)
        self._debug_print(f"Tracing return value from RETURN at {self._get_op_address(return_op)}")
        
        visited: Set[str] = set()
        self._trace_and_collect_evidence(
            return_varnode, evidence, visited, depth=0, max_depth=50
        )
    
    def _trace_and_collect_evidence(
        self,
        varnode,
        evidence: SignednessEvidence,
        visited: Set[str],
        depth: int,
        max_depth: int
    ) -> None:
        """
        Varnodeを再帰的にトレースして証拠を収集
        
        Phase 2: fast-path unsigned パターンの検出と除外を含む
        """
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
            category = OPCODE_EVIDENCE_MAP[mnemonic]
            address = self._get_op_address(def_op)
            
            pcode_evidence = PcodeEvidence(
                opcode=mnemonic,
                category=category,
                address=address,
            )
            
            # Phase 2: fast-path unsigned チェック
            if (mnemonic in FASTPATH_UNSIGNED_OPCODES and 
                category == EvidenceCategory.UNSIGNED):
                
                exclusion_reason = self._check_fastpath_unsigned(def_op)
                if exclusion_reason:
                    evidence.add_excluded_fastpath(pcode_evidence, exclusion_reason)
                    self._debug_print(
                        f"Excluded fast-path unsigned: {mnemonic} at {address} - {exclusion_reason}",
                        indent=1
                    )
                else:
                    evidence.add_evidence(pcode_evidence)
                    if self.debug:
                        self._debug_print(
                            f"Found {category.value} evidence: {mnemonic} at {address}",
                            indent=1
                        )
            else:
                evidence.add_evidence(pcode_evidence)
                if self.debug and category != EvidenceCategory.IGNORED:
                    self._debug_print(
                        f"Found {category.value} evidence: {mnemonic} at {address}",
                        indent=1
                    )
        
        # 入力を再帰的にトレース
        for i in range(def_op.getNumInputs()):
            input_vn = def_op.getInput(i)
            self._trace_and_collect_evidence(
                input_vn, evidence, visited, depth + 1, max_depth
            )
    
    def _collect_upper_zero_check_conditions(self) -> None:
        """
        Phase 2: 上位ビットゼロチェックの条件を事前収集
        
        パターン:
        - (x >> 32) == 0
        - ((x | y) >> 32) == 0
        - SUBPIECE(x, 4) == 0 (上位32ビット)
        """
        self._upper_zero_check_varnodes = set()
        
        basic_blocks = self.high_function.getBasicBlocks()
        if basic_blocks is None:
            return
        
        for bb in basic_blocks:
            try:
                pcode_iter = bb.getIterator()
                while pcode_iter.hasNext():
                    pcode_op = pcode_iter.next()
                    mnemonic = pcode_op.getMnemonic()
                    
                    # CBRANCH の条件をチェック
                    if mnemonic == "CBRANCH":
                        if pcode_op.getNumInputs() >= 2:
                            cond_vn = pcode_op.getInput(1)
                            self._analyze_branch_condition(cond_vn)
                    
                    # INT_EQUAL x, 0 のパターンをチェック
                    elif mnemonic == "INT_EQUAL":
                        self._check_equality_zero_pattern(pcode_op)
                        
            except Exception:
                continue
    
    def _analyze_branch_condition(self, cond_varnode) -> None:
        """条件分岐の条件を解析して上位ビットゼロチェックを検出"""
        if cond_varnode is None:
            return
        
        def_op = cond_varnode.getDef()
        if def_op is None:
            return
        
        mnemonic = def_op.getMnemonic()
        
        # INT_EQUAL x, 0 パターン
        if mnemonic == "INT_EQUAL":
            self._check_equality_zero_pattern(def_op)
        
        # BOOL_NEGATE でラップされている場合
        elif mnemonic == "BOOL_NEGATE":
            if def_op.getNumInputs() >= 1:
                inner_vn = def_op.getInput(0)
                self._analyze_branch_condition(inner_vn)
    
    def _check_equality_zero_pattern(self, pcode_op) -> None:
        """
        INT_EQUAL x, 0 パターンをチェックして
        x が上位ビット抽出の場合、その元のVarnodeを記録
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
        
        # other_vn が上位ビット抽出かチェック
        source_key = self._get_upper_bits_source(other_vn)
        if source_key:
            if self._upper_zero_check_varnodes is not None:
                self._upper_zero_check_varnodes.add(source_key)
                self._debug_print(f"Found upper-bits-zero-check for: {source_key}", indent=1)
    
    def _get_upper_bits_source(self, varnode) -> Optional[str]:
        """
        Varnodeが上位ビット抽出の場合、元のVarnodeのキーを返す
        
        パターン:
        - INT_RIGHT x, 32 -> x の上位32ビット
        - SUBPIECE x, 4 -> x の上位部分（64ビット -> 上位32ビット）
        """
        if varnode is None:
            return None
        
        def_op = varnode.getDef()
        if def_op is None:
            return None
        
        mnemonic = def_op.getMnemonic()
        
        # INT_RIGHT x, shift_amount パターン
        if mnemonic == "INT_RIGHT":
            if def_op.getNumInputs() >= 2:
                source_vn = def_op.getInput(0)
                shift_vn = def_op.getInput(1)
                
                if shift_vn.isConstant():
                    shift_amount = shift_vn.getOffset()
                    # 上位ビットへのシフト（32ビット以上）
                    if shift_amount >= 32:
                        return self._get_varnode_identity_key(source_vn)
        
        # SUBPIECE x, offset パターン（上位バイト抽出）
        elif mnemonic == "SUBPIECE":
            if def_op.getNumInputs() >= 2:
                source_vn = def_op.getInput(0)
                offset_vn = def_op.getInput(1)
                
                if offset_vn.isConstant():
                    byte_offset = offset_vn.getOffset()
                    # オフセット4以上 = 上位32ビット
                    if byte_offset >= 4:
                        return self._get_varnode_identity_key(source_vn)
        
        # INT_OR, INT_AND などでラップされている場合は再帰チェック
        elif mnemonic in ("INT_OR", "INT_AND", "INT_XOR"):
            if def_op.getNumInputs() >= 1:
                # 最初の入力をチェック
                source_key = self._get_upper_bits_source(def_op.getInput(0))
                if source_key:
                    return source_key
                # 2番目の入力もチェック
                if def_op.getNumInputs() >= 2:
                    source_key = self._get_upper_bits_source(def_op.getInput(1))
                    if source_key:
                        return source_key
        
        return None
    
    def _check_fastpath_unsigned(self, pcode_op) -> Optional[str]:
        """
        Phase 2: fast-path unsigned パターンかどうかを判定
        
        条件:
        1. 入力が SUBPIECE(x, 0) または AND(x, mask) 系で下位化されている
        2. 同一オペランドに対する上位ビットゼロ判定が条件側に存在
        
        Returns:
            除外理由（該当しない場合はNone）
        """
        # 入力の下位化パターンと元のVarnodeを取得
        source_info = self._get_lowered_source_varnode(pcode_op)
        if source_info is None:
            return None
        
        source_key, lowering_type = source_info
        
        # 上位ビットゼロチェックがあるか確認
        if self._upper_zero_check_varnodes and source_key in self._upper_zero_check_varnodes:
            return f"fast-path {lowering_type} with upper-bits-zero-check"
        
        return None
    
    def _get_lowered_source_varnode(self, pcode_op) -> Optional[Tuple[str, str]]:
        """
        fast-path パターンの入力から元のVarnodeを取得
        
        Returns:
            (source_varnode_key, lowering_type) または None
        """
        if pcode_op.getNumInputs() < 1:
            return None
        
        # 最初の入力（被除数/被シフト数）をチェック
        input_vn = pcode_op.getInput(0)
        if input_vn is None:
            return None
        
        input_def = input_vn.getDef()
        if input_def is None:
            return None
        
        input_mnemonic = input_def.getMnemonic()
        
        # SUBPIECE(x, 0) パターン - 下位バイト抽出
        if input_mnemonic == "SUBPIECE":
            if input_def.getNumInputs() >= 2:
                offset_vn = input_def.getInput(1)
                if offset_vn.isConstant() and offset_vn.getOffset() == 0:
                    source_vn = input_def.getInput(0)
                    source_key = self._get_varnode_identity_key(source_vn)
                    if source_key:
                        return (source_key, "SUBPIECE(x,0)")
        
        # INT_AND(x, mask) パターン - 下位ビットマスク
        elif input_mnemonic == "INT_AND":
            if input_def.getNumInputs() >= 2:
                # どちらがマスクか確認
                left_vn = input_def.getInput(0)
                right_vn = input_def.getInput(1)
                
                mask_vn = None
                source_vn = None
                
                if right_vn.isConstant():
                    mask_vn = right_vn
                    source_vn = left_vn
                elif left_vn.isConstant():
                    mask_vn = left_vn
                    source_vn = right_vn
                
                if mask_vn is not None and source_vn is not None:
                    mask_val = mask_vn.getOffset()
                    if mask_val in self.LOWER_MASK_VALUES:
                        source_key = self._get_varnode_identity_key(source_vn)
                        if source_key:
                            return (source_key, f"AND(x,0x{mask_val:X})")
        
        # COPY を透過的に処理
        elif input_mnemonic == "COPY":
            if input_def.getNumInputs() >= 1:
                copy_source = input_def.getInput(0)
                copy_def = copy_source.getDef() if copy_source else None
                if copy_def:
                    # 再帰的にチェック（COPYの先を見る）
                    # 無限ループ防止のため、浅くチェック
                    return self._get_lowered_source_from_def(copy_def)
        
        return None
    
    def _get_lowered_source_from_def(self, def_op) -> Optional[Tuple[str, str]]:
        """定義オペレーションから下位化パターンを検出（ヘルパー）"""
        if def_op is None:
            return None
        
        mnemonic = def_op.getMnemonic()
        
        if mnemonic == "SUBPIECE":
            if def_op.getNumInputs() >= 2:
                offset_vn = def_op.getInput(1)
                if offset_vn.isConstant() and offset_vn.getOffset() == 0:
                    source_vn = def_op.getInput(0)
                    source_key = self._get_varnode_identity_key(source_vn)
                    if source_key:
                        return (source_key, "SUBPIECE(x,0)")
        
        elif mnemonic == "INT_AND":
            if def_op.getNumInputs() >= 2:
                left_vn = def_op.getInput(0)
                right_vn = def_op.getInput(1)
                
                mask_vn = None
                source_vn = None
                
                if right_vn.isConstant():
                    mask_vn = right_vn
                    source_vn = left_vn
                elif left_vn.isConstant():
                    mask_vn = left_vn
                    source_vn = right_vn
                
                if mask_vn is not None and source_vn is not None:
                    mask_val = mask_vn.getOffset()
                    if mask_val in self.LOWER_MASK_VALUES:
                        source_key = self._get_varnode_identity_key(source_vn)
                        if source_key:
                            return (source_key, f"AND(x,0x{mask_val:X})")
        
        return None
    
    def _print_excluded_fastpath_summary(self, evidence: SignednessEvidence) -> None:
        """Phase 2: 除外されたfast-path証拠のサマリを出力"""
        if not evidence.excluded_fastpath:
            return
        
        self._debug_print(f"Excluded fast-path evidence: {len(evidence.excluded_fastpath)} item(s)")
        
        # オペコード別にカウント
        opcode_counts = evidence.get_excluded_opcode_counts()
        for opcode, count in opcode_counts.items():
            self._debug_print(f"  {opcode}: {count}", indent=1)
    
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
                self._process_pcode_op_simple(pcode_op, evidence)
        except Exception as e:
            self._debug_print(f"Error scanning basic block: {e}")
    
    def _process_pcode_op_simple(self, pcode_op, evidence: SignednessEvidence) -> None:
        """単一のPcodeOpを処理（fast-pathチェックなし）"""
        op_key = self._get_op_key(pcode_op)
        
        # 重複チェック
        if op_key in self._visited_ops:
            return
        self._visited_ops.add(op_key)
        
        mnemonic = pcode_op.getMnemonic()
        
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
        
        Phase 2対応版：fast-pathチェックを含む
        
        Args:
            return_varnode: 戻り値のVarnode
            max_depth: 最大トレース深度
        
        Returns:
            SignednessEvidence: 収集した証拠と判定結果
        """
        evidence = SignednessEvidence()
        self._visited_ops.clear()
        
        try:
            # 条件分岐の上位ビットゼロチェックを収集
            self._collect_upper_zero_check_conditions()
            
            visited: Set[str] = set()
            self._trace_and_collect_evidence(
                return_varnode, evidence, visited, 0, max_depth
            )
            evidence.determine_signedness()
        except Exception as e:
            self._debug_print(f"Error in return chain detection: {e}")
            evidence.result = SignednessType.UNKNOWN
        
        return evidence