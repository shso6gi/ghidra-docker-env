# -*- coding: utf-8 -*-
"""式木全体のPHI展開モジュール（網羅性改善版）"""

from typing import List, Optional, Set, Dict, Tuple, Any
from ..model import Expression, Condition, ExpressionType
from ..analysis.condition import ConditionSimplifier, ConditionNormalizer


class ExpandedValue:
    """展開された値と条件のペア"""
    
    def __init__(self, value: Expression, conditions: List[Condition]):
        self.value = value
        self.conditions = conditions
    
    def is_valid(self) -> bool:
        """条件が矛盾していないかチェック"""
        return not ConditionSimplifier.is_contradiction(self.conditions)
    
    def get_condition_signature(self) -> str:
        """
        条件のシグネチャを取得（重複排除用）
        
        条件を正規化して、ソート済みの文字列として返す
        """
        canonical_strs = []
        for cond in self.conditions:
            canonical = ConditionNormalizer.normalize(cond)
            # (left, op, right, pos) をタプル文字列化
            canonical_str = f"{canonical[0]}|{canonical[1]}|{canonical[2]}|{canonical[3]}"
            canonical_strs.append(canonical_str)
        
        # ソートして順序に依存しないようにする
        canonical_strs.sort()
        return ";;".join(canonical_strs)
    
    def __repr__(self):
        conds = [c.to_string() for c in self.conditions]
        return f"ExpandedValue(value={self.value.to_string()}, conds={conds})"


class ExpressionExpander:
    """
    式木全体を展開し、PHIノードを解決する
    """
    
    # 展開の上限設定
    MAX_CASES_PER_MULTIEQUAL = 16  # 1つのMULTIEQUALから生成する最大ケース数
    
    def __init__(self, tracer, condition_tracker, debug: bool = False):
        self.tracer = tracer
        self.condition_tracker = condition_tracker
        self.debug = debug
        self._expanding_ops: Set[str] = set()
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[Expander] {msg}")
    
    def expand_from_varnode(
        self,
        varnode,
        base_conditions: List[Condition],
        depth: int = 0
    ) -> List[ExpandedValue]:
        """Varnodeから式を展開"""
        if varnode is None:
            return [ExpandedValue(Expression.unknown("null"), base_conditions)]
        
        if depth > 30:
            self._debug_print(f"Max depth reached", depth)
            return [ExpandedValue(Expression.unknown("max_depth"), base_conditions)]
        
        def_op = varnode.getDef()
        
        if def_op is None:
            value = self.tracer.trace_varnode(varnode, depth, use_cache=False)
            return [ExpandedValue(value, base_conditions)]
        
        mnemonic = def_op.getMnemonic()
        self._debug_print(f"Expanding {mnemonic} at depth {depth}", depth)
        
        if mnemonic == "MULTIEQUAL":
            # MULTIEQUALは制御フローの合流点
            return self._expand_multiequal(def_op, depth)
        
        elif mnemonic in ("COPY", "CAST"):
            if def_op.getNumInputs() >= 1:
                return self.expand_from_varnode(def_op.getInput(0), base_conditions, depth + 1)
            return [ExpandedValue(Expression.unknown(f"{mnemonic}_no_input"), base_conditions)]
        
        else:
            return self._expand_operation(def_op, base_conditions, depth)
    
    def _expand_multiequal(
        self,
        multiequal_op,
        depth: int
    ) -> List[ExpandedValue]:
        """MULTIEQUALを展開"""
        op_key = self.tracer._get_op_key(multiequal_op)
        
        if op_key in self._expanding_ops:
            self._debug_print(f"Circular MULTIEQUAL detected: {op_key}", depth)
            return [ExpandedValue(Expression.unknown("phi_circular"), [])]
        
        self._expanding_ops.add(op_key)
        
        try:
            return self._expand_multiequal_internal(multiequal_op, depth)
        finally:
            self._expanding_ops.discard(op_key)
    
    def _expand_multiequal_internal(
        self,
        multiequal_op,
        depth: int
    ) -> List[ExpandedValue]:
        """
        MULTIEQUAL展開の内部処理（網羅性改善版）
        
        各MULTIEQUAL入力について、前任ブロックへの全有効パスを列挙し、
        それぞれを別の展開値として扱う。
        
        重要：値だけでなく条件も含めて重複排除を行う。
        """
        phi_parent = multiequal_op.getParent()
        if not phi_parent:
            return [ExpandedValue(Expression.unknown("phi_no_parent"), [])]
        
        num_inputs = multiequal_op.getNumInputs()
        in_size = phi_parent.getInSize()
        
        self._debug_print("=" * 50, depth)
        self._debug_print(f"MULTIEQUAL expansion: inputs={num_inputs}, in_edges={in_size}", depth)
        self._debug_print("=" * 50, depth)
        
        all_expanded: List[ExpandedValue] = []
        
        for i in range(num_inputs):
            input_varnode = multiequal_op.getInput(i)
            
            self._debug_print(f"Input[{i}] ----", depth)
            
            # 前任ブロック情報を取得
            if i >= in_size:
                self._debug_print(f"  No corresponding in_edge (i={i} >= in_size={in_size})", depth + 1)
                continue
            
            in_block = phi_parent.getIn(i)
            if not in_block:
                self._debug_print(f"  in_block is None", depth + 1)
                continue
            
            in_block_info = self.condition_tracker.get_block_by_hash(in_block)
            if not in_block_info:
                self._debug_print(f"  in_block_info not found", depth + 1)
                continue
            
            self._debug_print(f"  pred_block: index={in_block_info.index}", depth + 1)
            
            # 値をトレース（デバッグ用）
            try:
                traced_value = self.tracer.trace_varnode(input_varnode, depth + 1, use_cache=False)
                value_str = traced_value.to_string()
                self._debug_print(f"  traced_value: {value_str}", depth + 1)
                
                # SMT表現も取得（エラー時はスキップ）
                try:
                    smt_str = traced_value.to_smt()
                    if len(smt_str) > 100:
                        smt_str = smt_str[:100] + "..."
                    self._debug_print(f"  traced_smt: {smt_str}", depth + 1)
                except Exception as e:
                    self._debug_print(f"  traced_smt: (error: {e})", depth + 1)
            except Exception as e:
                self._debug_print(f"  traced_value: (error: {e})", depth + 1)
            
            # ★★★ 改善点：全有効パスを取得 ★★★
            all_valid_paths = self.condition_tracker.get_all_valid_paths_to_block(
                target_block=in_block_info
            )
            
            self._debug_print(f"  valid_paths: {len(all_valid_paths)}", depth + 1)
            
            # エッジ条件を取得（共通）
            edge_cond = self._get_edge_condition(in_block_info, phi_parent)
            if edge_cond:
                edge_str = ConditionNormalizer.get_simplified_string(edge_cond)
                self._debug_print(f"  edge_condition: {edge_str}", depth + 1)
            
            # 各パスについて展開
            cases_emitted = 0
            for path_idx, path_conditions in enumerate(all_valid_paths):
                # パス条件 + エッジ条件を結合
                input_conditions = path_conditions.copy()
                if edge_cond:
                    input_conditions.append(edge_cond)
                
                if self.debug:
                    self._debug_print(f"  Path[{path_idx}]: {len(path_conditions)} condition(s)", depth + 1)
                    for pc in path_conditions:
                        pc_str = ConditionNormalizer.get_simplified_string(pc)
                        self._debug_print(f"    - {pc_str}", depth + 2)
                
                # 矛盾チェック
                if ConditionSimplifier.is_contradiction(input_conditions):
                    self._debug_print(f"  Path[{path_idx}] -> SKIP (contradictory)", depth + 1)
                    continue
                
                # 入力を再帰的に展開
                expanded_inputs = self._expand_input_varnode(
                    input_varnode, 
                    input_conditions, 
                    depth + 1
                )
                
                for ev in expanded_inputs:
                    if ev.is_valid():
                        all_expanded.append(ev)
                        cases_emitted += 1
                        if self.debug:
                            val_str = ev.value.to_string()
                            if len(val_str) > 80:
                                val_str = val_str[:80] + "..."
                            self._debug_print(
                                f"  Path[{path_idx}] -> EMIT: {val_str}",
                                depth + 1
                            )
                    else:
                        self._debug_print(
                            f"  Path[{path_idx}] -> SKIP (invalid after expansion)",
                            depth + 1
                        )
            
            self._debug_print(f"  cases_emitted: {cases_emitted}", depth + 1)
        
        if all_expanded:
            # ★★★ 改善点：値と条件の両方を考慮して重複排除 ★★★
            merged = self._deduplicate_expanded_values(all_expanded, depth)
            self._debug_print("=" * 50, depth)
            self._debug_print(f"MULTIEQUAL -> {len(merged)} branches (after dedup)", depth)
            self._debug_print("=" * 50, depth)
            return merged
        
        self._debug_print("=" * 50, depth)
        self._debug_print(f"MULTIEQUAL -> 0 branches (no valid branches)", depth)
        self._debug_print("=" * 50, depth)
        return [ExpandedValue(Expression.unknown("phi_no_valid_branch"), [])]
    
    def _deduplicate_expanded_values(
        self, 
        values: List[ExpandedValue],
        depth: int
    ) -> List[ExpandedValue]:
        """
        展開値の重複排除（値と条件の両方を考慮）
        
        Args:
            values: 展開値のリスト
            depth: デバッグ用の深さ
        
        Returns:
            重複排除後のリスト（上限あり）
        """
        if not values:
            return []
        
        self._debug_print(f"Deduplicating {len(values)} expanded values...", depth)
        
        # (value_smt, condition_signature) でグループ化
        groups: Dict[Tuple[str, str], List[ExpandedValue]] = {}
        
        for ev in values:
            try:
                value_smt = ev.value.to_smt()
            except:
                value_smt = ev.value.to_string()
            
            cond_sig = ev.get_condition_signature()
            key = (value_smt, cond_sig)
            
            if key not in groups:
                groups[key] = []
            groups[key].append(ev)
        
        self._debug_print(f"  Grouped into {len(groups)} unique (value, condition) pairs", depth)
        
        # 各グループから代表を1つ選ぶ（条件が最も短いもの）
        result = []
        for key, group in groups.items():
            best = min(group, key=lambda e: len(e.conditions))
            result.append(best)
        
        # 上限チェック
        if len(result) > self.MAX_CASES_PER_MULTIEQUAL:
            self._debug_print(
                f"  WARNING: Too many cases ({len(result)}), limiting to {self.MAX_CASES_PER_MULTIEQUAL}",
                depth
            )
            # 条件が短い順にソート
            result = sorted(result, key=lambda e: len(e.conditions))
            result = result[:self.MAX_CASES_PER_MULTIEQUAL]
        
        self._debug_print(f"  Final result: {len(result)} unique cases", depth)
        return result
    
    def _expand_input_varnode(
        self,
        varnode,
        conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """MULTIEQUAL入力のVarnodeを再帰的に展開"""
        if varnode is None:
            return [ExpandedValue(Expression.unknown("null"), conditions)]
        
        if depth > 30:
            self._debug_print(f"Max depth in input varnode", depth)
            value = self.tracer.trace_varnode(varnode, depth, use_cache=False)
            return [ExpandedValue(value, conditions)]
        
        # Varnodeのサイズを取得
        varnode_size = varnode.getSize()
        
        def_op = varnode.getDef()
        
        if def_op is None:
            value = self.tracer.trace_varnode(varnode, depth, use_cache=False)
            # サイズを確実に設定
            if value.size == 0:
                value.size = varnode_size
            return [ExpandedValue(value, conditions)]
        
        mnemonic = def_op.getMnemonic()
        
        if mnemonic == "MULTIEQUAL":
            # ネストされたMULTIEQUALを展開し、条件を組み合わせる
            self._debug_print(f"Nested MULTIEQUAL found", depth)
            nested_expanded = self._expand_multiequal(def_op, depth)
            result = []
            for ev in nested_expanded:
                combined_conditions = conditions + ev.conditions
                if not ConditionSimplifier.is_contradiction(combined_conditions):
                    # サイズを確実に設定
                    if ev.value.size == 0:
                        ev.value.size = varnode_size
                    result.append(ExpandedValue(ev.value, combined_conditions))
            return result if result else [ExpandedValue(Expression.unknown("nested_phi_fail"), conditions)]
        
        elif mnemonic in ("COPY", "CAST"):
            if def_op.getNumInputs() >= 1:
                result = self._expand_input_varnode(def_op.getInput(0), conditions, depth + 1)
                # サイズを更新（出力サイズを使用）
                output = def_op.getOutput()
                if output:
                    output_size = output.getSize()
                    for ev in result:
                        if ev.value.size == 0:
                            ev.value.size = output_size
                return result
            return [ExpandedValue(Expression.unknown(f"{mnemonic}_no_input"), conditions)]
        
        else:
            # 通常の演算 - 入力にMULTIEQUALがあるかチェックして展開
            result = self._expand_input_operation(def_op, conditions, depth)
            # 出力サイズを設定
            output = def_op.getOutput()
            if output:
                output_size = output.getSize()
                for ev in result:
                    if ev.value.size == 0:
                        ev.value.size = output_size
            return result
    
    def _expand_input_operation(
        self,
        pcode_op,
        conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """MULTIEQUAL入力内の演算を展開"""
        mnemonic = pcode_op.getMnemonic()
        num_inputs = pcode_op.getNumInputs()
        
        # 出力サイズを取得
        output = pcode_op.getOutput()
        output_size = output.getSize() if output else 0
        
        self._debug_print(f"Expanding operation {mnemonic} (depth={depth}, output_size={output_size})", depth)
        
        # MULTIEQUALが含まれるかチェック
        has_multiequal = self._op_contains_multiequal(pcode_op)
        
        if not has_multiequal:
            # MULTIEQUALがなければ単純にトレース
            self._debug_print(f"  No MULTIEQUAL in inputs, simple trace", depth)
            value = self.tracer._trace_pcode_op(pcode_op, depth, use_cache=False)
            # 出力サイズを設定
            if value.size == 0 and output_size > 0:
                value.size = output_size
            return [ExpandedValue(value, conditions)]
        
        self._debug_print(f"  MULTIEQUAL found in inputs, expanding recursively", depth)
        
        # MULTIEQUALがあれば各入力を再帰的に展開
        input_expansions: List[List[ExpandedValue]] = []
        
        for i in range(num_inputs):
            input_varnode = pcode_op.getInput(i)
            # 各入力を再帰的に展開（条件は空で開始、後で組み合わせる）
            expanded = self._expand_input_varnode(input_varnode, [], depth + 1)
            input_expansions.append(expanded)
            self._debug_print(f"  Input[{i}] expanded to {len(expanded)} values", depth)
        
        # 組み合わせを生成
        output = pcode_op.getOutput()
        output_size = output.getSize() if output else 0
        return self._combine_input_expansions_with_conditions(
            mnemonic,
            input_expansions,
            conditions,
            depth,
            output_size=output_size,
        )
    
    def _op_contains_multiequal(self, pcode_op, depth: int = 0) -> bool:
        """PcodeOpの入力ツリーにMULTIEQUALが含まれるかチェック"""
        if depth > 15:
            return False
        
        if pcode_op is None:
            return False
        
        mnemonic = pcode_op.getMnemonic()
        if mnemonic == "MULTIEQUAL":
            return True
        
        for i in range(pcode_op.getNumInputs()):
            input_varnode = pcode_op.getInput(i)
            if input_varnode:
                input_def = input_varnode.getDef()
                if input_def and self._op_contains_multiequal(input_def, depth + 1):
                    return True
        
        return False
    
    def _expand_operation(
        self,
        pcode_op,
        base_conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """通常の演算を展開（トップレベルから呼ばれる場合）"""
        mnemonic = pcode_op.getMnemonic()
        num_inputs = pcode_op.getNumInputs()
        
        self._debug_print(f"Operation {mnemonic} with {num_inputs} inputs", depth)
        
        # MULTIEQUALが含まれるかチェック
        has_multiequal = self._op_contains_multiequal(pcode_op)
        
        if not has_multiequal:
            value = self.tracer._trace_pcode_op(pcode_op, depth, use_cache=False)
            return [ExpandedValue(value, base_conditions)]
        
        # 各入力を展開
        input_expansions: List[List[ExpandedValue]] = []
        
        for i in range(num_inputs):
            input_varnode = pcode_op.getInput(i)
            expanded = self.expand_from_varnode(input_varnode, [], depth + 1)
            input_expansions.append(expanded)
            
            if len(expanded) > 1:
                self._debug_print(f"  Input[{i}] has {len(expanded)} expansions", depth)
        
        output = pcode_op.getOutput()
        output_size = output.getSize() if output else 0
        return self._combine_input_expansions_with_conditions(
            mnemonic,
            input_expansions,
            base_conditions,
            depth,
            output_size=output_size,
        )
    
    def _combine_input_expansions_with_conditions(
        self,
        mnemonic: str,
        input_expansions: List[List[ExpandedValue]],
        base_conditions: List[Condition],
        depth: int,
        output_size: int = 0,
    ) -> List[ExpandedValue]:
        """入力の展開を組み合わせて結果を生成"""
        self._debug_print(f"Combining expansions for {mnemonic}", depth)
        
        if len(input_expansions) == 0:
            return [ExpandedValue(Expression.unknown(f"{mnemonic}_no_input"), base_conditions)]
        
        if len(input_expansions) == 1:
            result = []
            for ev in input_expansions[0]:
                combined_conds = base_conditions + ev.conditions
                if not ConditionSimplifier.is_contradiction(combined_conds):
                    if mnemonic in ("INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT"):
                        new_value = Expression.unary_op(mnemonic, ev.value)
                    else:
                        new_value = ev.value
                    result.append(ExpandedValue(new_value, combined_conds))
            return result if result else [ExpandedValue(Expression.unknown(f"{mnemonic}_contradiction"), base_conditions)]
        
        if len(input_expansions) == 2:
            result = []
            for left_ev in input_expansions[0]:
                for right_ev in input_expansions[1]:
                    combined_conds = base_conditions + left_ev.conditions + right_ev.conditions
                    
                    if ConditionSimplifier.is_contradiction(combined_conds):
                        self._debug_print(f"  Combination contradictory, skip", depth)
                        continue
                    
                    if mnemonic == "LOAD":
                        new_value = Expression.memory(
                            right_ev.value,
                            output_size if output_size > 0 else 4,
                        )
                    else:
                        new_value = Expression.binary_op(mnemonic, left_ev.value, right_ev.value)
                        if output_size > 0 and new_value.size == 0:
                            new_value.size = output_size
                    simplified_conds = ConditionSimplifier.simplify_conditions(combined_conds)
                    result.append(ExpandedValue(new_value, simplified_conds))
                    self._debug_print(f"  Combined: {new_value.to_string()}", depth)
            
            return result if result else [ExpandedValue(Expression.unknown(f"{mnemonic}_contradiction"), base_conditions)]
        
        # 3つ以上の入力
        self._debug_print(f"  Too many inputs ({len(input_expansions)}), falling back", depth)
        first_expansions = input_expansions[0]
        result = []
        for ev in first_expansions:
            other_values = []
            for exp_list in input_expansions[1:]:
                if exp_list:
                    other_values.append(exp_list[0].value)
            
            all_values = [ev.value] + other_values
            new_value = Expression.call(mnemonic, all_values)
            combined_conds = base_conditions + ev.conditions
            result.append(ExpandedValue(new_value, combined_conds))
        
        return result if result else [ExpandedValue(Expression.unknown(f"{mnemonic}_fail"), base_conditions)]
    
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
        
        condition = None
        if to_index == true_index:
            condition = Condition(from_block_info.branch_condition, negated=False)
        elif to_index == false_index:
            condition = Condition(from_block_info.branch_condition, negated=True)
        
        if self.debug and condition:
            cond_str = ConditionNormalizer.get_simplified_string(condition)
            self._debug_print(
                f"Edge: block {from_block_info.index} -> {to_index}: {cond_str}", 2
            )
        return condition
