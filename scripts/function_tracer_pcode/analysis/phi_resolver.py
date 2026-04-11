# -*- coding: utf-8 -*-
"""PHI（MULTIEQUAL）の処理専用モジュール"""

from typing import List, Optional, Set, Dict, Any
from ..model import Expression, Condition, ExpressionType
from .condition import ConditionSimplifier, ConditionNormalizer


class ExpandedBranch:
    """完全に展開されたPHI分岐"""
    
    def __init__(self, conditions: List[Condition], value: Expression):
        self.conditions = conditions
        self.value = value
    
    def is_valid(self) -> bool:
        """条件が矛盾していないかチェック"""
        return not ConditionSimplifier.is_contradiction(self.conditions)
    
    def get_simplified_conditions(self) -> List[Condition]:
        """簡略化された条件リストを取得"""
        return ConditionSimplifier.simplify_conditions(self.conditions)
    
    def __repr__(self):
        conds = [c.to_string() for c in self.conditions]
        return f"ExpandedBranch(conds={conds}, value={self.value.to_string()})"

    def get_condition_signature(self) -> str:
        canonical_strs = []
        for cond in self.conditions:
            canonical = ConditionNormalizer.normalize(cond)
            canonical_str = f"{canonical[0]}|{canonical[1]}|{canonical[2]}|{canonical[3]}"
            canonical_strs.append(canonical_str)
        canonical_strs.sort()
        return ";;".join(canonical_strs)


class PhiBranch:
    """PHIの各分岐を表現（後方互換性用）"""
    
    def __init__(self, condition: Optional[Condition], value: Expression, path_conditions: Optional[List[Condition]] = None):
        self.condition = condition
        self.value = value
        self.path_conditions = path_conditions or []
    
    def get_all_conditions(self) -> List[Condition]:
        result = self.path_conditions.copy()
        if self.condition:
            result.append(self.condition)
        return result


class PhiHandler:
    """PHI（MULTIEQUAL）ノードを展開して解決"""
    
    def __init__(self, tracer, condition_tracker):
        self.tracer = tracer
        self.condition_tracker = condition_tracker
        self.debug = tracer.debug
        self._expanding_ops: Set[str] = set()
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[PhiHandler] {msg}")
    
    def _same_varnode_id(self, vn1, vn2) -> bool:
        """VarnodeのID（space+offset+size）一致チェック"""
        if vn1 is None or vn2 is None:
            return False
        addr1, addr2 = vn1.getAddress(), vn2.getAddress()
        return (
            addr1.getAddressSpace().getName() == addr2.getAddressSpace().getName()
            and vn1.getOffset() == vn2.getOffset()
            and vn1.getSize() == vn2.getSize()
        )
    
    def _check_self_reference(self, input_varnode, output_varnode,
                               multiequal_op, depth) -> tuple:
        """
        自己参照チェック（優先度順）。
        Returns: (is_self_ref: bool, reason: str)
        """
        if input_varnode is None or output_varnode is None:
            return (False, "")
        
        # 1. オブジェクト同一性（最強）
        if input_varnode is output_varnode:
            return (True, "same_object")
        
        # 2. equals
        try:
            if input_varnode == output_varnode:
                return (True, "equals")
        except:
            pass
        
        # 3. VarnodeID一致 → 定義opで最終判定
        if self._same_varnode_id(input_varnode, output_varnode):
            input_def = input_varnode.getDef()
            if input_def is None:
                return (False, "id_match_but_no_def")
            # 定義opのオブジェクト同一性
            if input_def is multiequal_op:
                return (True, "def_object_same")
            # keyが同じでもオブジェクトが異なれば別SSAバージョン
            input_def_key = self.tracer._get_stable_op_key(input_def)
            multiequal_key = self.tracer._get_stable_op_key(multiequal_op)
            if input_def_key == multiequal_key:
                return (True, f"logical_self_ref_{input_def.getMnemonic()}")
            return (False, f"different_def_{input_def.getMnemonic()}")
        
        return (False, "")
    
    def _format_varnode_info(self, varnode, label="varnode") -> str:
        """Varnode情報を整形（ログ用）"""
        if varnode is None:
            return f"{label}: None"
        addr = varnode.getAddress()
        high_var = varnode.getHigh()
        var_name = high_var.getName() if high_var else "?"
        return (
            f"{label}: {addr.getAddressSpace().getName()}:0x{varnode.getOffset():x} "
            f"size={varnode.getSize()} obj_id={id(varnode)} '{var_name}'"
        )
    
    def expand_multiequal(
        self,
        multiequal_op,
        base_conditions: Optional[List[Condition]] = None,
        depth: int = 0
    ) -> List[ExpandedBranch]:
        """MULTIEQUALを完全に展開"""
        if base_conditions is None:
            base_conditions = []
        
        op_key = self.tracer._get_stable_op_key(multiequal_op)
        
        if op_key in self._expanding_ops:
            self._debug_print(f"Circular reference detected", depth)
            return [ExpandedBranch(base_conditions, Expression.unknown("phi_circular"))]
        
        self._expanding_ops.add(op_key)
        
        try:
            return self._expand_internal(multiequal_op, base_conditions, depth)
        finally:
            self._expanding_ops.discard(op_key)
    
    def _expand_internal(
        self,
        multiequal_op,
        base_conditions: List[Condition],
        depth: int
    ) -> List[ExpandedBranch]:
        """MULTIEQUAL展開の内部処理（自己参照検出付き）"""
        self._debug_print("=" * 60, depth)
        self._debug_print("Expanding MULTIEQUAL", depth)
        
        op_key = self.tracer._get_stable_op_key(multiequal_op)
        self._debug_print(f"MULTIEQUAL op_key: {op_key}", depth)
        
        output_varnode = multiequal_op.getOutput()
        if self.debug:
            self._debug_print(self._format_varnode_info(output_varnode, "Output"), depth)
        
        phi_parent = multiequal_op.getParent()
        if not phi_parent:
            self._debug_print("ERROR: No parent block", depth)
            self.tracer.emit_unknown_event(
                reason="phi_no_parent", varnode=output_varnode,
                def_op=multiequal_op, depth=depth,
                note="MULTIEQUAL has no parent block", context="phi_handler"
            )
            return [ExpandedBranch(base_conditions, Expression.unknown("phi_no_parent"))]
        
        phi_index = phi_parent.getIndex()
        self._debug_print(f"PHI block index: {phi_index}", depth)
        
        num_inputs = multiequal_op.getNumInputs()
        in_size = phi_parent.getInSize()
        
        self._debug_print(f"MULTIEQUAL inputs: {num_inputs}, Block in-edges: {in_size}", depth)
        
        all_branches: List[ExpandedBranch] = []
        self_ref_count = 0
        self_ref_reasons = []
        
        for i in range(num_inputs):
            input_varnode = multiequal_op.getInput(i)
            
            self._debug_print(f"", depth)
            self._debug_print(f"--- Processing Input[{i}] ---", depth + 1)
            
            if self.debug:
                self._debug_print(
                    self._format_varnode_info(input_varnode, f"Input[{i}]"), depth + 1
                )
            
            # ★ 自己参照チェック
            is_self_ref, self_ref_reason = self._check_self_reference(
                input_varnode, output_varnode, multiequal_op, depth
            )
            
            if is_self_ref:
                self_ref_count += 1
                self_ref_reasons.append(f"input[{i}]={self_ref_reason}")
                self._debug_print(
                    f"Self-reference detected: {self_ref_reason}", depth + 1
                )
            
            # 入力ブロックの条件を収集
            input_conditions = base_conditions.copy()
            
            if i < in_size:
                in_block = phi_parent.getIn(i)
                if in_block:
                    in_block_info = self.condition_tracker.get_block_by_hash(in_block)
                    if in_block_info:
                        self._debug_print(
                            f"In-edge block: index={in_block.getIndex()}", depth + 1
                        )
                        path_conds = self.condition_tracker.get_path_conditions_to_block(
                            in_block_info
                        )
                        input_conditions.extend(path_conds)
                        
                        edge_cond = self._get_edge_condition(in_block_info, phi_parent)
                        if edge_cond:
                            input_conditions.append(edge_cond)
                        
                        if self.debug:
                            cond_strs = [c.to_string() for c in input_conditions]
                            self._debug_print(
                                f"Input conditions ({len(input_conditions)}): {cond_strs}",
                                depth + 1
                            )
            
            # 矛盾チェック
            if ConditionSimplifier.is_contradiction(input_conditions):
                self._debug_print(f"Conditions are contradictory, skipping", depth + 1)
                continue
            
            # 自己参照スキップ
            if is_self_ref:
                self._debug_print(f"Skipping self-reference input", depth + 1)
                continue
            
            # 入力値を展開
            self._debug_print(f"Tracing input value...", depth + 1)
            expanded_values = self._trace_input_value(
                input_varnode, input_conditions, depth + 1
            )
            
            for ev in expanded_values:
                if ev.is_valid():
                    self._debug_print(
                        f"Valid branch: {ev.value.to_string()}", depth + 1
                    )
                    all_branches.append(ev)
        
        # ★ 統計サマリー
        if self.debug:
            self._debug_print(f"", depth)
            self._debug_print(f"MULTIEQUAL summary: self_refs={self_ref_count}/{num_inputs}, "
                              f"valid={len(all_branches)}", depth)
            if self_ref_reasons:
                for r in self_ref_reasons:
                    self._debug_print(f"  - {r}", depth + 1)
        
        # 全入力が自己参照 → debug時はエラー
        if self.debug and self_ref_count == num_inputs and num_inputs > 0:
            raise RuntimeError(
                f"All {num_inputs} MULTIEQUAL inputs are self-references: "
                f"{self_ref_reasons}"
            )
        
        # マージ
        if all_branches:
            merged = self._merge_branches(all_branches)
            self._debug_print(f"Expanded to {len(merged)} valid branches", depth)
            return merged
        
        # 有効なブランチなし
        self.tracer.emit_unknown_event(
            reason="phi_no_valid_branch", varnode=output_varnode,
            def_op=multiequal_op, depth=depth,
            note=f"self_refs={self_ref_count}/{num_inputs}",
            context="phi_handler"
        )
        return [ExpandedBranch(base_conditions, Expression.unknown("phi_no_valid_branch"))]
    
    def _trace_input_value(
        self,
        varnode,
        conditions: List[Condition],
        depth: int
    ) -> List[ExpandedBranch]:
        """入力Varnodeをトレース（キャッシュを使わない）"""
        if varnode is None:
            return [ExpandedBranch(conditions, Expression.unknown("null"))]
        
        def_op = varnode.getDef()
        
        if def_op is None:
            # 入力変数
            value = self.tracer.trace_varnode(varnode, depth, use_cache=False)
            return [ExpandedBranch(conditions, value)]
        
        mnemonic = def_op.getMnemonic()
        
        if mnemonic == "MULTIEQUAL":
            # ネストされたMULTIEQUAL
            return self.expand_multiequal(def_op, conditions, depth)
        
        elif mnemonic == "COPY":
            if def_op.getNumInputs() >= 1:
                return self._trace_input_value(def_op.getInput(0), conditions, depth)
            return [ExpandedBranch(conditions, Expression.unknown("copy_no_input"))]
        
        else:
            # 通常の演算 - 入力にMULTIEQUALがあるかチェック
            return self._trace_operation_with_phi(def_op, conditions, depth)
    
    def _trace_operation_with_phi(
        self,
        pcode_op,
        conditions: List[Condition],
        depth: int
    ) -> List[ExpandedBranch]:
        """演算をトレース（入力にPHIがあれば展開）"""
        mnemonic = pcode_op.getMnemonic()
        num_inputs = pcode_op.getNumInputs()
        
        # 各入力を展開
        input_expansions: List[List[ExpandedBranch]] = []
        has_phi = False
        
        for i in range(num_inputs):
            input_varnode = pcode_op.getInput(i)
            
            # 入力がMULTIEQUALを持つかチェック
            input_def = input_varnode.getDef() if input_varnode else None
            if input_def and input_def.getMnemonic() == "MULTIEQUAL":
                expanded = self.expand_multiequal(input_def, [], depth)
                has_phi = True
            else:
                # 通常のトレース（キャッシュなし）
                value = self.tracer.trace_varnode(input_varnode, depth, use_cache=False)
                expanded = [ExpandedBranch([], value)]
            
            input_expansions.append(expanded)
        
        # PHIがなければ単純にトレース
        if not has_phi:
            value = self.tracer._trace_pcode_op(pcode_op, depth, use_cache=False)
            return [ExpandedBranch(conditions, value)]
        
        # PHIがある場合は組み合わせを展開
        return self._combine_expansions(mnemonic, input_expansions, conditions)
    
    def _combine_expansions(
        self,
        mnemonic: str,
        input_expansions: List[List[ExpandedBranch]],
        base_conditions: List[Condition]
    ) -> List[ExpandedBranch]:
        """入力の展開を組み合わせて結果を生成"""
        if len(input_expansions) == 1:
            result = []
            for exp in input_expansions[0]:
                combined = base_conditions + exp.conditions
                if not ConditionSimplifier.is_contradiction(combined):
                    result.append(ExpandedBranch(combined, exp.value))
            return result if result else [ExpandedBranch(base_conditions, Expression.unknown(f"{mnemonic}_fail"))]
        
        if len(input_expansions) == 2:
            result = []
            for left_exp in input_expansions[0]:
                for right_exp in input_expansions[1]:
                    combined_conds = base_conditions + left_exp.conditions + right_exp.conditions
                    
                    if ConditionSimplifier.is_contradiction(combined_conds):
                        continue
                    
                    new_value = Expression.binary_op(mnemonic, left_exp.value, right_exp.value)
                    result.append(ExpandedBranch(combined_conds, new_value))
            
            return result if result else [ExpandedBranch(base_conditions, Expression.unknown(f"{mnemonic}_fail"))]
        
        # 3つ以上の入力
        return [ExpandedBranch(base_conditions, Expression.unknown(f"{mnemonic}_too_many_inputs"))]
    
    def _merge_branches(self, branches: List[ExpandedBranch]) -> List[ExpandedBranch]:
        """同じ値かつ同じ条件集合を持つ分岐のみマージ"""
        if not branches:
            return []
        
        value_groups: Dict[tuple, List[ExpandedBranch]] = {}
        for branch in branches:
            try:
                value_key = branch.value.to_smt()
            except Exception:
                value_key = branch.value.to_string()
            cond_key = branch.get_condition_signature()
            group_key = (value_key, cond_key)
            if group_key not in value_groups:
                value_groups[group_key] = []
            value_groups[group_key].append(branch)
        
        result = []
        for _group_key, group in value_groups.items():
            best = min(group, key=lambda b: len(b.conditions))
            result.append(best)
        
        return result
    
    def _get_edge_condition(self, from_block_info, to_block) -> Optional[Condition]:
        """fromブロックからtoブロックへのエッジ条件を取得"""
        from_block = from_block_info.block
        
        if from_block.getOutSize() <= 1:
            return None
        
        if not from_block_info.has_conditional_branch():
            return None
        
        to_index = to_block.getIndex()
        
        true_out = from_block.getTrueOut()
        false_out = from_block.getFalseOut()
        
        true_index = true_out.getIndex() if true_out else -1
        false_index = false_out.getIndex() if false_out else -1
        
        if to_index == true_index:
            return Condition(from_block_info.branch_condition, negated=False)
        
        if to_index == false_index:
            return Condition(from_block_info.branch_condition, negated=True)
        
        return None
    
    # 後方互換性のためのメソッド
    def resolve_multiequal(self, multiequal_op, depth: int = 0) -> List[PhiBranch]:
        """MULTIEQUALを解決（後方互換性）"""
        expanded = self.expand_multiequal(multiequal_op, [], depth)
        
        result = []
        for eb in expanded:
            simplified_conds = eb.get_simplified_conditions()
            result.append(PhiBranch(
                condition=None,
                value=eb.value,
                path_conditions=simplified_conds
            ))
        
        return result
