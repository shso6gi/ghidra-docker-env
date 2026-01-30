# -*- coding: utf-8 -*-
"""PHI（MULTIEQUAL）の処理専用モジュール"""

from typing import List, Optional, Set, Dict, Any
from .expression import Expression, Condition, ExpressionType
from .condition_simplifier import ConditionSimplifier


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
    
    def expand_multiequal(
        self,
        multiequal_op,
        base_conditions: Optional[List[Condition]] = None,
        depth: int = 0
    ) -> List[ExpandedBranch]:
        """MULTIEQUALを完全に展開"""
        if base_conditions is None:
            base_conditions = []
        
        op_key = self.tracer._get_op_key(multiequal_op)
        
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
        """MULTIEQUAL展開の内部処理"""
        self._debug_print("=" * 40, depth)
        self._debug_print("Expanding MULTIEQUAL", depth)
        
        phi_parent = multiequal_op.getParent()
        if not phi_parent:
            return [ExpandedBranch(base_conditions, Expression.unknown("phi_no_parent"))]
        
        phi_index = phi_parent.getIndex()
        self._debug_print(f"PHI block index: {phi_index}", depth)
        
        num_inputs = multiequal_op.getNumInputs()
        in_size = phi_parent.getInSize()
        
        self._debug_print(f"MULTIEQUAL inputs: {num_inputs}, Block in-edges: {in_size}", depth)
        
        all_branches: List[ExpandedBranch] = []
        
        for i in range(num_inputs):
            input_varnode = multiequal_op.getInput(i)
            
            self._debug_print(f"", depth)
            self._debug_print(f"Processing Input[{i}]: {input_varnode}", depth + 1)
            
            # 入力の定義情報を取得
            input_def = input_varnode.getDef()
            if input_def:
                self._debug_print(f"Defined by: {input_def.getMnemonic()} at {input_def.getSeqnum()}", depth + 1)
            
            # 入力ブロックの条件を収集
            input_conditions = base_conditions.copy()
            
            if i < in_size:
                in_block = phi_parent.getIn(i)
                if in_block:
                    in_block_info = self.condition_tracker.get_block_by_hash(in_block)
                    if in_block_info:
                        self._debug_print(f"In-edge block: index={in_block.getIndex()}", depth + 1)
                        
                        # パス条件を取得
                        path_conds = self.condition_tracker.get_path_conditions_to_block(in_block_info)
                        input_conditions.extend(path_conds)
                        
                        # エッジ条件を追加
                        edge_cond = self._get_edge_condition(in_block_info, phi_parent)
                        if edge_cond:
                            input_conditions.append(edge_cond)
                        
                        if self.debug:
                            cond_strs = [c.to_string() for c in input_conditions]
                            self._debug_print(f"Input conditions: {cond_strs}", depth + 1)
            
            # 矛盾チェック
            if ConditionSimplifier.is_contradiction(input_conditions):
                self._debug_print(f"Conditions are contradictory, skipping", depth + 1)
                continue
            
            # 入力値を展開（キャッシュを使わない）
            expanded_values = self._trace_input_value(input_varnode, input_conditions, depth + 1)
            
            for ev in expanded_values:
                if ev.is_valid():
                    self._debug_print(f"Valid branch: {ev.value.to_string()}", depth + 1)
                    all_branches.append(ev)
        
        # マージ
        if all_branches:
            merged = self._merge_branches(all_branches)
            self._debug_print(f"Expanded to {len(merged)} valid branches", depth)
            return merged
        
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
        """同じ値を持つ分岐をマージ"""
        if not branches:
            return []
        
        value_groups: Dict[str, List[ExpandedBranch]] = {}
        for branch in branches:
            val_str = branch.value.to_string()
            if val_str not in value_groups:
                value_groups[val_str] = []
            value_groups[val_str].append(branch)
        
        result = []
        for val_str, group in value_groups.items():
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