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
    
    def __init__(self, tracer):
        self.tracer = tracer
        self.high_function = tracer.high_function
        self.debug = tracer.debug
        
        self.block_map: Dict[Any, BasicBlockInfo] = {}
        self.block_by_hash: Dict[int, BasicBlockInfo] = {}
        self.block_by_index: Dict[int, BasicBlockInfo] = {}
        self.entry_block: Optional[BasicBlockInfo] = None
        
        self._build_block_info()
    
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
                    self._debug_print(f"  CBRANCH condition: {cond_expr.to_string()}", 1)
                    break
    
    def get_block_by_hash(self, block) -> Optional[BasicBlockInfo]:
        """ブロックオブジェクトから情報を取得"""
        if block is None:
            return None
        return self.block_by_hash.get(block.hashCode())
    
    def get_block_by_index(self, index: int) -> Optional[BasicBlockInfo]:
        """インデックスからブロック情報を取得"""
        return self.block_by_index.get(index)
    
    def get_path_conditions_to_block(self, target_block: BasicBlockInfo) -> List[Condition]:
        """エントリーからターゲットブロックまでのパス条件を取得（有効なパスのみ）"""
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
        
        if self.debug and all_paths:
            self._debug_print(f"Paths to block {target_block.index}:")
            for i, path in enumerate(all_paths):
                conds = [c.to_string() for c in path]
                self._debug_print(f"  Path {i}: {conds}")
        
        # 矛盾しないパスをフィルタリング
        valid_paths = []
        for path in all_paths:
            if not ConditionSimplifier.is_contradiction(path):
                valid_paths.append(path)
            elif self.debug:
                self._debug_print(f"  -> Path filtered (contradiction)")
        
        # 有効なパスがあればそれを返す
        if valid_paths:
            # 最も条件が少ないパスを選択
            best_path = min(valid_paths, key=len)
            if self.debug:
                self._debug_print(f"  Selected valid path: {[c.to_string() for c in best_path]}")
            return best_path
        
        # 有効なパスがない場合は最初のパスを返す（フォールバック）
        if all_paths:
            return all_paths[0]
        return []
    
    def get_all_valid_paths_to_block(self, target_block: BasicBlockInfo) -> List[List[Condition]]:
        """エントリーからターゲットブロックまでの全ての有効なパスを取得"""
        from .simplifier import ConditionSimplifier
        
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
        
        # 矛盾しないパスのみ返す
        valid_paths = [p for p in all_paths if not ConditionSimplifier.is_contradiction(p)]
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