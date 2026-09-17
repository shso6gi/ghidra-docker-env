# -*- coding: utf-8 -*-
"""PHI（MULTIEQUAL）の処理専用モジュール"""

from itertools import product
from typing import List, Optional, Set, Dict, Any, Hashable, Tuple
from scripts.function_tracer_pcode.core import Expression, Condition, PcodeOpRef, UnknownValueRef
from scripts.function_tracer_pcode.core.intrinsics import resolve_pcode_intrinsic
from scripts.function_tracer_pcode.analysis.debug import (
    summarize_conditions,
    summarize_expression,
)
from scripts.function_tracer_pcode.analysis.condition import (
    ConditionSimplifier,
    ConditionNormalizer,
)


# Re-exports kept for callers that import these names from this module.
from scripts.function_tracer_pcode.core import ExpressionType


class _PhiExpansionBudgetOrigin:
    def __init__(self, key: Tuple[Any, ...]):
        self._key = key

    def stable_key(self) -> Tuple[Any, ...]:
        return self._key


def _pcode_op_stable_key(pcode_op) -> Tuple[Any, ...]:
    ref = PcodeOpRef.from_pcode_op(pcode_op)
    if ref is None:
        return ("pcode_op", None, None, None, None, None)
    return ref.stable_key()


def _pcode_op_ref_from_tracer(tracer: Any, pcode_op: Any) -> Optional[PcodeOpRef]:
    make_ref = getattr(tracer, "_make_pcode_op_ref", None)
    if callable(make_ref):
        try:
            ref = make_ref(pcode_op)
        except Exception:
            ref = None
        if ref is not None:
            return ref
    return PcodeOpRef.from_pcode_op(pcode_op)


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
        # ``repr()`` は logging / 例外 / デバッガから暗黙に呼ばれる。full render
        # だと debug を切っていても巨大 DAG を展開しうるので、有界サマリーを返す
        # （Issue #22）。
        return (
            f"ExpandedBranch(conds={summarize_conditions(self.conditions)}, "
            f"value={summarize_expression(self.value)})"
        )

    def get_condition_signature(self) -> Hashable:
        return ConditionNormalizer.conditions_signature(self.conditions)


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
        self._expanding_ops: Set[Tuple[Any, ...]] = set()
        self._expansion_cache: Dict[tuple, List[ExpandedBranch]] = {}
        self._expansion_cache_limit = 2048
        self._combined_branch_limit = 256
        self._debug_message_limit = 4000
        self._debug_message_count = 0
        self._debug_suppressed = False
    
    def _debug_print(self, msg: str, indent: int = 0):
        if not self.debug:
            return
        if self._debug_message_count >= self._debug_message_limit:
            if not self._debug_suppressed:
                prefix = "  " * indent
                print(
                    f"{prefix}[PhiHandler] debug output suppressed after "
                    f"{self._debug_message_limit} messages"
                )
                self._debug_suppressed = True
            return
        self._debug_message_count += 1
        prefix = "  " * indent
        print(f"{prefix}[PhiHandler] {msg}")

    def _debug_available(self) -> bool:
        """debug 出力が有効か（抑止上限も含む）。message 構築ごとこれで囲む。"""

        return self.debug and self._debug_message_count < self._debug_message_limit

    def _condition_signature(self, conditions: List[Condition]) -> Hashable:
        return ConditionNormalizer.conditions_signature(conditions)

    def _debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
        return summarize_expression(expr, max_depth=max_depth)

    def _cache_key(self, multiequal_op, base_conditions: List[Condition]) -> tuple:
        op_ref = _pcode_op_ref_from_tracer(self.tracer, multiequal_op)
        op_key = op_ref.stable_key() if op_ref is not None else _pcode_op_stable_key(multiequal_op)
        return (op_key, self._condition_signature(base_conditions))

    def _clone_branches(self, branches: List[ExpandedBranch]) -> List[ExpandedBranch]:
        return [ExpandedBranch(list(branch.conditions), branch.value) for branch in branches]
    
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
            input_def_key = _pcode_op_stable_key(input_def)
            multiequal_key = _pcode_op_stable_key(multiequal_op)
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
        
        op_key = _pcode_op_stable_key(multiequal_op)
        cache_key = self._cache_key(multiequal_op, base_conditions)

        cached = self._expansion_cache.get(cache_key)
        if cached is not None:
            self._debug_print(f"Cache hit for MULTIEQUAL: {op_key}", depth)
            return self._clone_branches(cached)
        
        if op_key in self._expanding_ops:
            self._debug_print("Circular reference detected", depth)
            return [
                ExpandedBranch(
                    base_conditions,
                    Expression.unknown(
                        "phi_circular",
                        runtime_ref=UnknownValueRef.phi_circular(
                            pcode_op_ref=_pcode_op_ref_from_tracer(self.tracer, multiequal_op),
                        ),
                    ),
                )
            ]
        
        self._expanding_ops.add(op_key)
        
        try:
            expanded = self._expand_internal(multiequal_op, base_conditions, depth)
            if len(self._expansion_cache) >= self._expansion_cache_limit:
                self._expansion_cache.clear()
            self._expansion_cache[cache_key] = self._clone_branches(expanded)
            return self._clone_branches(expanded)
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
        
        op_key = _pcode_op_stable_key(multiequal_op)
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
            
            self._debug_print("", depth)
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
            
            # 自己参照スキップ
            if is_self_ref:
                self._debug_print("Skipping self-reference input", depth + 1)
                continue

            input_condition_sets: List[List[Condition]] = [list(base_conditions)]
            if i < in_size:
                in_block = phi_parent.getIn(i)
                if in_block:
                    in_block_info = self.condition_tracker.get_block_by_hash(in_block)
                    if in_block_info:
                        self._debug_print(
                            f"In-edge block: index={in_block.getIndex()}", depth + 1
                        )
                        all_valid_paths = self.condition_tracker.get_all_valid_paths_to_block(
                            in_block_info
                        )
                        edge_cond = self._get_edge_condition(in_block_info, phi_parent)

                        input_condition_sets = []
                        for path_conds in all_valid_paths or [[]]:
                            input_conditions = list(base_conditions) + list(path_conds)
                            if edge_cond:
                                input_conditions.append(edge_cond)
                            input_condition_sets.append(input_conditions)

            for cond_index, input_conditions in enumerate(input_condition_sets):
                if self._debug_available():
                    self._debug_print(
                        f"Input conditions[{cond_index}] ({len(input_conditions)}): "
                        f"{summarize_conditions(input_conditions)}",
                        depth + 1
                    )

                if ConditionSimplifier.is_contradiction(input_conditions):
                    self._debug_print("Conditions are contradictory, skipping", depth + 1)
                    continue

                # 入力値を展開
                self._debug_print("Tracing input value...", depth + 1)
                expanded_values = self._trace_input_value(
                    input_varnode, input_conditions, depth + 1
                )

                for ev in expanded_values:
                    if ev.is_valid():
                        if self._debug_available():
                            self._debug_print(
                                f"Valid branch: {self._debug_expr_summary(ev.value)}",
                                depth + 1,
                            )
                        all_branches.append(ev)
        
        # ★ 統計サマリー
        if self.debug:
            self._debug_print("", depth)
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
                expanded = self.expand_multiequal(input_def, conditions, depth)
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
        output = pcode_op.getOutput()
        output_size = output.getSize() if output is not None else 0
        return self._combine_expansions(
            mnemonic,
            input_expansions,
            conditions,
            opcode=getattr(pcode_op, "getOpcode", lambda: None)(),
            pcode_op=pcode_op,
            output_size=output_size,
            origin_ref=self._phi_expansion_budget_origin(
                mnemonic,
                opcode=getattr(pcode_op, "getOpcode", lambda: None)(),
                pcode_op=pcode_op,
                base_conditions=conditions,
                output_size=output_size,
            ),
        )
    
    def _combine_expansions(
        self,
        mnemonic: str,
        input_expansions: List[List[ExpandedBranch]],
        base_conditions: List[Condition],
        opcode: Optional[int] = None,
        pcode_op: Optional[Any] = None,
        output_size: int = 0,
        origin_ref: Optional[Any] = None,
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
            left_count = len(input_expansions[0])
            right_count = len(input_expansions[1])
            if left_count * right_count > self._combined_branch_limit:
                return self._branch_budget_unknown(
                    mnemonic,
                    base_conditions,
                    output_size=output_size,
                    branch_count=left_count * right_count,
                    origin_ref=origin_ref,
                )
            result = []
            for left_exp in input_expansions[0]:
                for right_exp in input_expansions[1]:
                    combined_conds = base_conditions + left_exp.conditions + right_exp.conditions
                    
                    if ConditionSimplifier.is_contradiction(combined_conds):
                        continue
                    
                    new_value = self._build_combined_expression(
                        mnemonic,
                        [left_exp.value, right_exp.value],
                        output_size=output_size,
                        opcode=opcode,
                        pcode_op=pcode_op,
                    )
                    result.append(ExpandedBranch(combined_conds, new_value))
            
            return result if result else [ExpandedBranch(base_conditions, Expression.unknown(f"{mnemonic}_fail"))]

        branch_count = 1
        for expansion in input_expansions:
            branch_count *= len(expansion)
            if branch_count > self._combined_branch_limit:
                return self._branch_budget_unknown(
                    mnemonic,
                    base_conditions,
                    output_size=output_size,
                    branch_count=branch_count,
                    origin_ref=origin_ref,
                )

        result = []
        for expansion_tuple in product(*input_expansions):
            combined_conds: List[Condition] = list(base_conditions)
            operands: List[Expression] = []
            for expanded in expansion_tuple:
                combined_conds.extend(expanded.conditions)
                operands.append(expanded.value)

            if ConditionSimplifier.is_contradiction(combined_conds):
                continue

            new_value = self._build_combined_expression(
                mnemonic,
                operands,
                output_size=output_size,
                opcode=opcode,
                pcode_op=pcode_op,
            )
            if output_size > 0 and getattr(new_value, "size", 0) == 0:
                new_value.size = output_size
            result.append(ExpandedBranch(combined_conds, new_value))

        return result if result else [ExpandedBranch(base_conditions, Expression.unknown(f"{mnemonic}_fail"))]

    def _branch_budget_unknown(
        self,
        mnemonic: str,
        base_conditions: List[Condition],
        *,
        output_size: int,
        branch_count: int,
        origin_ref: Optional[Any] = None,
    ) -> List[ExpandedBranch]:
        reason = "phi_expansion_budget_exceeded"
        self._debug_print(
            f"{mnemonic} PHI expansion budget exceeded: branches={branch_count}, "
            f"limit={self._combined_branch_limit}",
        )
        emit_unknown_event = getattr(self.tracer, "emit_unknown_event", None)
        if callable(emit_unknown_event):
            emit_unknown_event(
                reason=reason,
                depth=0,
                note=(
                    f"mnemonic={mnemonic}, branches={branch_count}, "
                    f"limit={self._combined_branch_limit}"
                ),
                context="phi_handler",
            )
        if origin_ref is None:
            origin_ref = self._phi_expansion_budget_origin(
                mnemonic,
                opcode=None,
                pcode_op=None,
                base_conditions=base_conditions,
                output_size=output_size,
            )
        value = Expression.unknown(
            reason,
            runtime_ref=UnknownValueRef.budget_exceeded(
                operation="phi_expansion",
                origin_kind="phi_expansion_site",
                origin_ref=origin_ref,
            ),
        )
        if output_size > 0:
            value.size = output_size
        return [ExpandedBranch(list(base_conditions), value)]

    def _phi_expansion_budget_origin(
        self,
        mnemonic: str,
        *,
        opcode: Optional[int],
        pcode_op: Optional[Any],
        base_conditions: List[Condition],
        output_size: int,
    ) -> _PhiExpansionBudgetOrigin:
        pcode_ref = _pcode_op_ref_from_tracer(self.tracer, pcode_op) if pcode_op is not None else None
        pcode_key = pcode_ref.stable_key() if pcode_ref is not None else (
            _pcode_op_stable_key(pcode_op) if pcode_op is not None else None
        )
        return _PhiExpansionBudgetOrigin(
            (
                "phi_expansion_budget_origin",
                str(mnemonic),
                None if opcode is None else int(opcode),
                pcode_key,
                int(output_size or 0),
                ConditionNormalizer.conditions_signature(base_conditions),
            )
        )

    def _build_combined_expression(
        self,
        mnemonic: str,
        operands: List[Expression],
        *,
        output_size: int = 0,
        opcode: Optional[int] = None,
        pcode_op: Optional[Any] = None,
    ) -> Expression:
        if mnemonic == "CALLOTHER":
            userop_name = None
            resolver = getattr(self.tracer, "_resolve_callother_userop_name", None)
            if callable(resolver) and pcode_op is not None:
                try:
                    userop_name = resolver(pcode_op)
                except Exception:
                    userop_name = None
            if userop_name:
                intrinsic = resolve_pcode_intrinsic(mnemonic=userop_name)
                if intrinsic is not None:
                    return Expression.intrinsic(
                        intrinsic.mnemonic,
                        operands[1:] if operands else [],
                        size=output_size,
                        opcode=intrinsic.opcode,
                    )
        intrinsic = resolve_pcode_intrinsic(opcode=opcode, mnemonic=mnemonic)
        if intrinsic is not None:
            return Expression.intrinsic(
                intrinsic.mnemonic,
                operands,
                size=output_size,
                opcode=intrinsic.opcode,
            )
        if len(operands) == 1:
            return operands[0]
        if len(operands) == 2:
            return Expression.binary_op(mnemonic, operands[0], operands[1])
        return Expression.intrinsic(
            mnemonic,
            operands,
            size=output_size,
            opcode=opcode,
        )
    
    def _merge_branches(self, branches: List[ExpandedBranch]) -> List[ExpandedBranch]:
        """同じ値かつ同じ条件集合を持つ分岐のみマージ"""
        if not branches:
            return []
        
        value_groups: Dict[tuple, List[ExpandedBranch]] = {}
        for branch in branches:
            value_key = ConditionNormalizer.expression_signature(branch.value)
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
