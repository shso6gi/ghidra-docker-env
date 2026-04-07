# -*- coding: utf-8 -*-
"""条件分岐の追跡"""

from typing import Dict, List, Optional, Set, Any
from ...model import Expression, Condition


class BasicBlockInfo:
    """基本ブロック情報"""
    
    def __init__(self, block):
        self.block = block
        self.start = block.getStart()
        self.stop = block.getStop()
        self.index = block.getIndex()
        self.pcode_ops = []
        self.in_edges = []
        self.out_edges = []
        self.branch_condition: Optional[Expression] = None
        self.branch_condition_varnode = None
        self.true_out_index: int = -1
        self.false_out_index: int = -1
    
    def load_ops(self):
        pcode_iter = self.block.getIterator()
        while pcode_iter.hasNext():
            self.pcode_ops.append(pcode_iter.next())
    
    def load_edges(self):
        for i in range(self.block.getInSize()):
            in_block = self.block.getIn(i)
            if in_block:
                self.in_edges.append(in_block)
        
        for i in range(self.block.getOutSize()):
            out_block = self.block.getOut(i)
            if out_block:
                self.out_edges.append(out_block)
    
    def has_conditional_branch(self) -> bool:
        return (self.branch_condition is not None and 
                self.true_out_index >= 0 and 
                self.false_out_index >= 0)
    
    def __repr__(self):
        return f"BasicBlockInfo(index={self.index}, start={self.start})"


class ConditionTracker:
    """条件分岐を追跡"""
    
    # クラス定数：パス展開の上限設定
    MAX_VALID_PATHS = 8  # 1つのブロックへの最大有効パス数
    MAX_CONDITIONS_PER_PATH = 20  # 1パスあたりの最大条件数
    
    def __init__(self, tracer):
        self.tracer = tracer
        self.high_function = tracer.high_function
        self.debug = tracer.debug
        
        self.block_map: Dict[Any, BasicBlockInfo] = {}
        self.block_by_hash: Dict[int, BasicBlockInfo] = {}
        self.block_by_index: Dict[int, BasicBlockInfo] = {}
        self.entry_block: Optional[BasicBlockInfo] = None
        
        self._built = False

    def build(self):
        """ブロック情報を構築。tracer.phi_handler セット後に呼び出すこと。"""
        if self._built:
            return
        self._build_block_info()
        self._built = True
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[CondTracker] {msg}")
    
    def _build_block_info(self):
        """ブロック情報を構築"""
        basic_blocks = self.high_function.getBasicBlocks()
        
        self._debug_print("=" * 50)
        self._debug_print("Building block info")
        self._debug_print("=" * 50)
        
        for bb in basic_blocks:
            info = BasicBlockInfo(bb)
            info.load_ops()
            info.load_edges()
            
            block_hash = bb.hashCode()
            
            self.block_map[bb.getStart()] = info
            self.block_by_hash[block_hash] = info
            self.block_by_index[info.index] = info
            
            if not info.in_edges:
                self.entry_block = info
            
            self._debug_print(f"Block {bb.getStart()} (index={info.index}):")
            self._debug_print(f"  In: {[b.getIndex() for b in info.in_edges]}", 1)
            self._debug_print(f"  Out: {[b.getIndex() for b in info.out_edges]}", 1)
            
            self._detect_branch_condition(info)
        
        self._debug_print(f"Entry block: index={self.entry_block.index if self.entry_block else 'None'}")
        self._debug_print("=" * 50)
    
    def _detect_branch_condition(self, block_info: BasicBlockInfo):
        """条件分岐を検出"""
        block = block_info.block
        
        if block.getOutSize() < 2:
            return
        
        try:
            true_out = block.getTrueOut()
            false_out = block.getFalseOut()
        except Exception as e:
            self._debug_print(f"  Error getting true/false out: {e}", 1)
            return
        
        if not true_out or not false_out:
            return
        
        block_info.true_out_index = true_out.getIndex()
        block_info.false_out_index = false_out.getIndex()
        
        self._debug_print(f"  TrueOut: index={block_info.true_out_index}", 1)
        self._debug_print(f"  FalseOut: index={block_info.false_out_index}", 1)
        
        for pcode_op in block_info.pcode_ops:
            if pcode_op.getMnemonic() == "CBRANCH":
                if pcode_op.getNumInputs() >= 2:
                    cond_varnode = pcode_op.getInput(1)
                    cond_expr = self.tracer.trace_varnode(cond_varnode)
                    block_info.branch_condition = cond_expr
                    block_info.branch_condition_varnode = cond_varnode
                    self._debug_print(f"  CBRANCH condition: {cond_expr.to_string()}", 1)
                    break

    def refine_branch_conditions(
        self,
        call_resolver=None,
        parameters: Optional[List[Dict[str, Any]]] = None,
        effect_summary=None,
        read_memory_value=None,
        image_base: Optional[int] = None,
    ) -> int:
        """CALL を含む分岐条件を、安全な要約が得られる場合のみ再構築する。"""
        from ...transform import ExpressionExpander
        from ...analysis.condition.simplifier import ConditionSimplifier
        from ...model.render_smt import expression_returns_bool

        expander = ExpressionExpander(
            self.tracer,
            self,
            debug=self.debug,
            call_resolver=call_resolver,
            effect_summary=effect_summary,
            parameters=parameters,
            read_memory_value=read_memory_value,
            image_base=image_base,
        )

        changed = 0
        for block_info in self.block_by_index.values():
            raw_condition = block_info.branch_condition
            cond_varnode = block_info.branch_condition_varnode
            if raw_condition is None or cond_varnode is None:
                continue
            if not self._expression_contains_unknown_or_call(raw_condition):
                continue

            expanded_values = expander.expand_from_varnode(cond_varnode, [])
            refined = self._build_refined_branch_condition(
                expanded_values,
                output_size=cond_varnode.getSize() if hasattr(cond_varnode, "getSize") else 1,
                expression_returns_bool=expression_returns_bool,
                condition_simplifier=ConditionSimplifier,
            )
            if refined is None:
                continue

            if self.debug:
                self._debug_print(
                    f"  Refined branch condition for block {block_info.index}: "
                    f"{raw_condition.to_string()} -> {refined.to_string()}",
                    1,
                )
            block_info.branch_condition = refined
            changed += 1

        if self.debug:
            self._debug_print(f"Refined {changed} branch condition(s)")
        return changed

    def _build_refined_branch_condition(
        self,
        expanded_values,
        output_size: int,
        expression_returns_bool,
        condition_simplifier,
    ) -> Optional[Expression]:
        valid_branches = []
        seen = set()

        for expanded in expanded_values:
            value = getattr(expanded, "value", None)
            conditions = list(getattr(expanded, "conditions", []) or [])
            if value is None:
                continue
            if not expression_returns_bool(value):
                continue
            if self._expression_contains_unknown_or_call(value):
                continue

            simplified_conditions = condition_simplifier.simplify_conditions(conditions)
            if condition_simplifier.is_contradiction(simplified_conditions):
                continue
            if any(
                self._expression_contains_unknown_or_call(cond.expression)
                for cond in simplified_conditions
            ):
                continue

            key = (
                tuple(cond.to_string() for cond in simplified_conditions),
                value.to_string(),
            )
            if key in seen:
                continue
            seen.add(key)
            valid_branches.append((simplified_conditions, value))

        if not valid_branches:
            return None

        if len(valid_branches) == 1:
            only_conditions, only_value = valid_branches[0]
            if only_conditions:
                return None
            only_value.size = only_value.size or output_size
            return only_value

        branches = []
        conditional_branches = []
        fallback_branches = []
        for branch_conditions, branch_value in valid_branches:
            branch_condition = Condition.combine_and(branch_conditions)
            if branch_condition is None:
                fallback_branches.append((None, branch_value))
            else:
                conditional_branches.append((branch_condition, branch_value))

        if not conditional_branches:
            return None

        branches.extend(conditional_branches)
        branches.extend(fallback_branches)

        phi_expr = Expression.phi(branches)
        phi_expr.size = output_size or phi_expr.size
        return phi_expr

    def _expression_contains_unknown_or_call(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False

        expr_kind = expr.expr_type.__class__
        if expr.expr_type in (expr_kind.UNKNOWN, expr_kind.CALL):
            return True

        if expr.expr_type == expr_kind.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_contains_unknown_or_call(cond.expression):
                    return True
                if self._expression_contains_unknown_or_call(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unknown_or_call(operand):
                return True

        return False
    
    def get_block_by_hash(self, block) -> Optional[BasicBlockInfo]:
        """ブロックオブジェクトから情報を取得"""
        if block is None:
            return None
        return self.block_by_hash.get(block.hashCode())
    
    def get_block_by_index(self, index: int) -> Optional[BasicBlockInfo]:
        """インデックスからブロック情報を取得"""
        return self.block_by_index.get(index)
    
    def get_path_conditions_to_block(self, target_block: BasicBlockInfo) -> List[Condition]:
        """
        エントリーからターゲットブロックまでのパス条件を取得（単一パス）
        
        有効なパスの中で最も条件が少ないものを返す。
        複数パスが必要な場合は get_all_valid_paths_to_block() を使用すること。
        """
        from .simplifier import ConditionSimplifier
        
        if self.entry_block is None:
            return []
        
        if target_block.index == self.entry_block.index:
            return []
        
        all_paths: List[List[Condition]] = []
        self._find_paths_with_conditions(
            current=self.entry_block,
            target=target_block,
            current_conditions=[],
            all_paths=all_paths,
            visited=set()
        )
        
        if self.debug:
            self._debug_print(f"get_path_conditions_to_block for block {target_block.index}:")
            self._debug_print(f"  Found {len(all_paths)} total paths", 1)
        
        # 矛盾しないパスをフィルタリング（詳細ログ付き）
        valid_paths = []
        for i, path in enumerate(all_paths):
            if self.debug:
                self._debug_print(f"  Checking path {i} for contradictions...", 1)
            is_contradictory = ConditionSimplifier.is_contradiction(path)
            if not is_contradictory:
                valid_paths.append(path)
                if self.debug:
                    self._debug_print(f"    -> Path {i} is VALID", 2)
            else:
                if self.debug:
                    self._debug_print(f"    -> Path {i} is CONTRADICTORY (filtered)", 2)
        
        # 有効なパスがあればそれを返す
        if valid_paths:
            # 最も条件が少ないパスを選択
            best_path = min(valid_paths, key=len)
            if self.debug:
                best_conds = [ConditionSimplifier.get_simplified_condition_string(c) for c in best_path]
                self._debug_print(f"  Selected valid path ({len(best_path)} conditions): {best_conds}", 1)
            return best_path
        
        # 有効なパスがない場合は最初のパスを返す（フォールバック）
        if all_paths:
            if self.debug:
                self._debug_print(f"  WARNING: No valid paths, using first path as fallback", 1)
            return all_paths[0]
        return []
    
    def get_all_valid_paths_to_block(
        self, 
        target_block: BasicBlockInfo,
        limit_paths: Optional[int] = None
    ) -> List[List[Condition]]:
        """
        エントリーからターゲットブロックまでの全ての有効なパスを取得
        
        Args:
            target_block: 目標ブロック
            limit_paths: パス数の上限（Noneの場合はMAX_VALID_PATHSを使用）
        
        Returns:
            有効なパスのリスト（各パスは条件のリスト）
            パス爆発を防ぐため、以下のフィルタリングを適用：
            1. 矛盾する条件を含むパスを除外
            2. 条件数が多すぎるパスを除外
            3. 短い順にソートして上位N件を返す
        """
        from .simplifier import ConditionSimplifier
        
        if limit_paths is None:
            limit_paths = self.MAX_VALID_PATHS
        
        if self.entry_block is None:
            return []
        
        if target_block.index == self.entry_block.index:
            return [[]]
        
        all_paths: List[List[Condition]] = []
        self._find_paths_with_conditions(
            current=self.entry_block,
            target=target_block,
            current_conditions=[],
            all_paths=all_paths,
            visited=set()
        )
        
        self._debug_print(f"get_all_valid_paths_to_block for block {target_block.index}:")
        self._debug_print(f"  Found {len(all_paths)} total paths", 1)
        
        # Step 1: 矛盾しないパスのみ
        valid_paths = []
        for i, path in enumerate(all_paths):
            if not ConditionSimplifier.is_contradiction(path):
                valid_paths.append(path)
            elif self.debug:
                self._debug_print(f"  Path {i} rejected (contradiction)", 2)
        
        self._debug_print(f"  {len(valid_paths)} paths are valid (non-contradictory)", 1)
        
        # Step 2: 条件数が多すぎるパスを除外
        filtered_paths = []
        for path in valid_paths:
            if len(path) <= self.MAX_CONDITIONS_PER_PATH:
                filtered_paths.append(path)
            elif self.debug:
                self._debug_print(f"  Path with {len(path)} conditions rejected (exceeds limit {self.MAX_CONDITIONS_PER_PATH})", 2)
        
        valid_paths = filtered_paths
        self._debug_print(f"  {len(valid_paths)} paths remain after condition limit filter", 1)
        
        if not valid_paths:
            self._debug_print(f"  WARNING: No valid paths found!", 1)
            return []
        
        # Step 3: 短い順にソート（条件が少ない = よりシンプル）
        valid_paths = sorted(valid_paths, key=len)
        
        # Step 4: パス数制限
        if len(valid_paths) > limit_paths:
            self._debug_print(f"  Limiting to {limit_paths} paths (shortest first)", 1)
            valid_paths = valid_paths[:limit_paths]
        
        # デバッグ出力
        if self.debug:
            self._debug_print(f"  Returning {len(valid_paths)} valid paths:", 1)
            for i, path in enumerate(valid_paths):
                conds = [ConditionSimplifier.get_simplified_condition_string(c) 
                        for c in path]
                self._debug_print(f"    Path {i} ({len(path)} conditions): {conds}", 2)
        
        return valid_paths
    
    def _find_paths_with_conditions(
        self,
        current: BasicBlockInfo,
        target: BasicBlockInfo,
        current_conditions: List[Condition],
        all_paths: List[List[Condition]],
        visited: Set[int]
    ):
        """パスを探索して条件を収集"""
        if current.index in visited:
            return
        
        visited = visited | {current.index}
        
        if current.index == target.index:
            all_paths.append(current_conditions.copy())
            return
        
        for out_block in current.out_edges:
            out_info = self.get_block_by_hash(out_block)
            if out_info is None:
                continue
            
            new_conditions = current_conditions.copy()
            
            if current.has_conditional_branch():
                out_index = out_block.getIndex()
                
                # branch_conditionがNoneでないことを明示的にチェック
                branch_cond = current.branch_condition
                if branch_cond is not None:
                    if out_index == current.true_out_index:
                        new_conditions.append(
                            Condition(branch_cond, negated=False)
                        )
                    elif out_index == current.false_out_index:
                        new_conditions.append(
                            Condition(branch_cond, negated=True)
                        )
            
            self._find_paths_with_conditions(
                current=out_info,
                target=target,
                current_conditions=new_conditions,
                all_paths=all_paths,
                visited=visited
            )
    
    def get_path_conditions_to_return(self, return_op) -> List[Condition]:
        """RETURNに至るパス条件を収集"""
        return_parent = return_op.getParent()
        if return_parent:
            return_block_info = self.get_block_by_hash(return_parent)
            if return_block_info:
                self._debug_print(f"RETURN block: index={return_block_info.index}")
                return self.get_path_conditions_to_block(return_block_info)
        return []

    def get_all_valid_paths_to_return(
        self,
        return_op,
        limit_paths: Optional[int] = None
    ) -> List[List[Condition]]:
        """RETURNに至る全ての有効パス条件を収集"""
        return_parent = return_op.getParent()
        if return_parent:
            return_block_info = self.get_block_by_hash(return_parent)
            if return_block_info:
                self._debug_print(f"RETURN block: index={return_block_info.index}")
                return self.get_all_valid_paths_to_block(
                    return_block_info,
                    limit_paths=limit_paths,
                )
        return []
