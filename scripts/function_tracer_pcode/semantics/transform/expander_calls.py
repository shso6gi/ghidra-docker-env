"""CALL / CALLIND expansion, deferred call recording and indirect output locations."""

from __future__ import annotations

from typing import List, Optional, Dict, Tuple
from scripts.function_tracer_pcode.core import (
    Expression,
    Condition,
    ExpressionType,
    StorageInfo,
    CallTargetRef,
)
from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.effects.summary import (
    _reduce_expression_under_conditions,
    _resolve_call_target_ref,
    _recover_call_argument_expressions,
    _resolve_call_argument_expression,
    _expression_maps_to_parameter,
    resolve_call_targets,
    _expressions_equivalent,
    canonicalize_location,
    rewrite_location_read_from_effects,
)
from scripts.function_tracer_pcode.semantics.transform.expander_support import (
    ExpandedValue,
    _pcode_op_ref_from_tracer,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_conditions


class CallExpansionMixin:
    """CALL / CALLIND expansion, deferred call recording and indirect output locations."""

    def _record_deferred_call(
        self,
        target_ref: CallTargetRef,
        args: List[Expression],
        call_target_expr: Optional[Expression],
        pcode_op_ref,
    ):
        if self.record_deferred_call is None:
            return None
        if self._record_deferred_call_accepts_pcode_ref:
            return self.record_deferred_call(target_ref, args, call_target_expr, pcode_op_ref)
        return self.record_deferred_call(target_ref, args, call_target_expr)

    def _expand_call_operation(
        self,
        pcode_op,
        base_conditions: List[Condition],
        depth: int,
        output_size: int = 0,
    ) -> List[ExpandedValue]:
        """CALL/CALLIND を callee の return case に展開する。"""
        resolved_targets = resolve_call_targets(
            self.tracer,
            pcode_op,
            conditions=base_conditions,
            parameters=self.parameters,
            read_memory_value=self.read_memory_value,
            image_base=self.image_base,
            debug=self.debug,
        )
        if self._debug_available() and resolved_targets:
            for target_ref, target_conditions in resolved_targets:
                self._debug_print(
                    f"Resolved {pcode_op.getMnemonic()} target -> {target_ref.display_name()} "
                    f"with conditions {summarize_conditions(target_conditions)}",
                    depth,
                )

        if not resolved_targets or self.call_resolver is None:
            target_ref = _resolve_call_target_ref(self.tracer, pcode_op)
            record_target_ref = target_ref or CallTargetRef.unknown()
            target_label = record_target_ref.display_name()
            deferred_target_expr = self._recover_deferred_call_target_expression(pcode_op)
            explicit_args = [
                _resolve_call_argument_expression(
                    pcode_op.getInput(index),
                    self.tracer,
                    self.parameters,
                )
                for index in range(1, pcode_op.getNumInputs())
            ]
            deferred_unknown_ref = None
            deferred_unknown_label = None
            if self.record_deferred_call is not None:
                deferred_args = self._recover_deferred_call_arguments(
                    pcode_op,
                    record_target_ref,
                    explicit_args,
                )
                make_ref = getattr(self.tracer, "_make_pcode_op_ref", None)
                pcode_op_ref = make_ref(pcode_op) if callable(make_ref) else None
                deferred_unknown = self._record_deferred_call(
                    record_target_ref,
                    deferred_args,
                    deferred_target_expr,
                    pcode_op_ref,
                )
                if isinstance(deferred_unknown, str):
                    deferred_unknown_label = deferred_unknown
                else:
                    deferred_unknown_ref = deferred_unknown
                    if hasattr(deferred_unknown, "display_name"):
                        deferred_unknown_label = deferred_unknown.display_name()
            self.tracer.emit_unknown_event(
                reason="call_out_of_scope",
                varnode=pcode_op.getOutput(),
                def_op=pcode_op,
                depth=depth,
                note=f"{pcode_op.getMnemonic()} target={target_label}",
                context="expander",
            )
            return [
                ExpandedValue(
                    Expression.unknown(
                        (
                            deferred_unknown_label
                            if deferred_unknown_label is not None
                            else f"call_out_of_scope:{target_label}"
                        ),
                        runtime_ref=deferred_unknown_ref,
                    ),
                    base_conditions,
                )
            ]

        arg_expansions: List[List[ExpandedValue]] = []
        explicit_input_varnodes = [
            pcode_op.getInput(index)
            for index in range(1, pcode_op.getNumInputs())
        ]
        canonical_explicit_args: List[Optional[Expression]] = []
        if self.parameters:
            for input_varnode in explicit_input_varnodes:
                try:
                    canonical_explicit_args.append(
                        _resolve_call_argument_expression(
                            input_varnode,
                            self.tracer,
                            self.parameters,
                        )
                    )
                except Exception:
                    canonical_explicit_args.append(None)

        for index in range(1, pcode_op.getNumInputs()):
            arg_expansions.append(
                self._expand_input_varnode(pcode_op.getInput(index), [], depth + 1)
            )

        result: List[ExpandedValue] = []
        fallback_args_by_target: Dict[CallTargetRef, List[Expression]] = {}

        def resolve_with_args(
            arg_index: int,
            current_args: List[Expression],
            current_conditions: List[Condition],
        ) -> None:
            if arg_index >= len(arg_expansions):
                for target_ref, target_conditions in resolved_targets:
                    merged_target_conditions = ConditionSimplifier.simplify_conditions(
                        current_conditions + target_conditions
                    )
                    if ConditionSimplifier.is_contradiction(merged_target_conditions):
                        continue

                    effective_args = list(current_args)
                    if self.parameters and canonical_explicit_args:
                        stabilized_args: List[Expression] = []
                        for index, arg in enumerate(effective_args):
                            input_varnode = (
                                explicit_input_varnodes[index]
                                if index < len(explicit_input_varnodes)
                                else None
                            )
                            canonical_arg = (
                                canonical_explicit_args[index]
                                if index < len(canonical_explicit_args)
                                else None
                            )
                            should_replace = (
                                input_varnode is not None
                                and getattr(input_varnode, "getDef", lambda: None)() is not None
                                and canonical_arg is not None
                                and canonical_arg.expr_type not in {ExpressionType.UNKNOWN, ExpressionType.CALL}
                                and not self._expression_contains_unknown_or_call(canonical_arg)
                                and (
                                    canonical_arg.expr_type != ExpressionType.VARIABLE
                                    or _expression_maps_to_parameter(canonical_arg, self.parameters)
                                )
                                and _expression_maps_to_parameter(arg, self.parameters)
                                and not _expressions_equivalent(arg, canonical_arg)
                            )
                            if should_replace:
                                assert canonical_arg is not None
                                if self.debug:
                                    self._debug_print(
                                        "Stabilized explicit CALL arg from original input: "
                                        f"{self._debug_expr_summary(arg)} -> {self._debug_expr_summary(canonical_arg)}",
                                        depth,
                                    )
                                stabilized_args.append(canonical_arg)
                            else:
                                stabilized_args.append(arg)
                        effective_args = stabilized_args
                    if self.resolve_callee_parameters is not None:
                        callee_parameters = list(self.resolve_callee_parameters(target_ref) or [])
                        if callee_parameters:
                            effective_args = _recover_call_argument_expressions(
                                pcode_op,
                                self.tracer,
                                self.parameters,
                                callee_parameters,
                                effective_args,
                                condition_tracker=self.condition_tracker,
                                current_conditions=merged_target_conditions,
                            )
                    fallback_args_by_target.setdefault(
                        target_ref,
                        list(effective_args),
                    )

                    if self.call_resolver is None:
                        continue
                    resolved = self.call_resolver(target_ref, effective_args)
                    if not resolved:
                        if self.debug:
                            self._debug_print(
                                f"Call summary unavailable for resolved target '{target_ref.display_name()}'",
                                depth,
                            )
                        continue
                    for ev in resolved:
                        merged_conditions = ConditionSimplifier.simplify_conditions(
                            merged_target_conditions + ev.conditions
                        )
                        if ConditionSimplifier.is_contradiction(merged_conditions):
                            continue
                        value = self._coerce_value_to_output_size(ev.value, output_size)
                        result.append(ExpandedValue(value, merged_conditions))
                return

            for ev in arg_expansions[arg_index]:
                merged_conditions = current_conditions + ev.conditions
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                resolve_with_args(
                    arg_index + 1,
                    current_args + [ev.value],
                    merged_conditions,
                )

        resolve_with_args(0, [], list(base_conditions))

        if result:
            return self._deduplicate_expanded_values(
                result,
                depth,
                label=f"{pcode_op.getMnemonic()} call expansions",
                pcode_op_ref=_pcode_op_ref_from_tracer(self.tracer, pcode_op),
            )

        fallback_target = self._select_deferred_call_target(resolved_targets, pcode_op)
        fallback_label = fallback_target.display_name()
        deferred_unknown_ref = None
        deferred_unknown_label = None
        if self.record_deferred_call is not None:
            deferred_target_expr = self._recover_deferred_call_target_expression(pcode_op)
            deferred_args = fallback_args_by_target.get(fallback_target)
            if deferred_args is None:
                recovered_seed_args = [arg for arg in (canonical_explicit_args or []) if arg is not None]
                deferred_args = self._recover_deferred_call_arguments(
                    pcode_op,
                    fallback_target,
                    recovered_seed_args,
                )
            make_ref = getattr(self.tracer, "_make_pcode_op_ref", None)
            pcode_op_ref = make_ref(pcode_op) if callable(make_ref) else None
            deferred_unknown = self._record_deferred_call(
                fallback_target,
                deferred_args,
                deferred_target_expr,
                pcode_op_ref,
            )
            if isinstance(deferred_unknown, str):
                deferred_unknown_label = deferred_unknown
            else:
                deferred_unknown_ref = deferred_unknown
                if hasattr(deferred_unknown, "display_name"):
                    deferred_unknown_label = deferred_unknown.display_name()
        self.tracer.emit_unknown_event(
            reason="call_out_of_scope",
            varnode=pcode_op.getOutput(),
            def_op=pcode_op,
            depth=depth,
            note=f"{pcode_op.getMnemonic()} target={fallback_label}",
            context="expander",
        )
        return [
            ExpandedValue(
                Expression.unknown(
                    (
                        deferred_unknown_label
                        if deferred_unknown_label is not None
                        else f"call_out_of_scope:{fallback_label}"
                    ),
                    runtime_ref=deferred_unknown_ref,
                ),
                base_conditions,
            )
        ]

    def _select_deferred_call_target(
        self,
        resolved_targets: List[Tuple[CallTargetRef, List[Condition]]],
        pcode_op,
    ) -> CallTargetRef:
        unique_targets = [
            target_ref
            for target_ref, _target_conditions in (resolved_targets or [])
            if target_ref is not None
        ]
        unique_keys = {target_ref.stable_key(): target_ref for target_ref in unique_targets}
        if len(unique_keys) == 1:
            return next(iter(unique_keys.values()))
        return _resolve_call_target_ref(self.tracer, pcode_op) or CallTargetRef.unknown()

    def _recover_deferred_call_arguments(
        self,
        pcode_op,
        target_ref: CallTargetRef,
        explicit_args: List[Expression],
    ) -> List[Expression]:
        deferred_args = list(explicit_args or [])
        if self.resolve_callee_parameters is None or target_ref is None:
            return deferred_args

        callee_parameters = list(self.resolve_callee_parameters(target_ref) or [])
        if not callee_parameters:
            return deferred_args

        recovered = _recover_call_argument_expressions(
            pcode_op,
            self.tracer,
            self.parameters,
            callee_parameters,
            deferred_args,
            condition_tracker=self.condition_tracker,
        )
        if recovered:
            return recovered
        return deferred_args

    def _recover_deferred_call_target_expression(
        self,
        pcode_op,
    ) -> Optional[Expression]:
        if pcode_op is None or pcode_op.getNumInputs() < 1:
            return None
        try:
            target_varnode = pcode_op.getInput(0)
        except Exception:
            return None
        if target_varnode is None:
            return None
        try:
            return self.tracer.trace_varnode(target_varnode, use_cache=False)
        except Exception:
            return None

    def _infer_indirect_output_location(
        self,
        output_varnode,
        output_size: int,
    ):
        if output_varnode is None or output_size <= 0:
            return None

        storage_info = None
        try:
            storage_info = self.tracer._get_storage_info_from_varnode(output_varnode)
        except Exception:
            storage_info = None
        if storage_info is None:
            storage_info = self._fallback_storage_info_from_varnode(output_varnode, output_size)

        high_name = None
        try:
            high_var = output_varnode.getHigh()
            if high_var is not None:
                high_name = high_var.getName()
        except Exception:
            high_name = None

        probe_name = high_name or f"indirect_out_{id(output_varnode):x}"
        probe = Expression.variable(
            probe_name,
            size=output_size,
            storage_info=storage_info,
        )
        location = canonicalize_location(probe, self.parameters, size=output_size)
        if self.debug and location is None:
            self._debug_print(
                "Failed to infer INDIRECT output location: "
                f"name={probe_name} storage={storage_info}",
                0,
            )
        return location

    def _fallback_storage_info_from_varnode(
        self,
        varnode,
        output_size: int,
    ) -> Optional[StorageInfo]:
        if varnode is None:
            return None
        try:
            addr = varnode.getAddress()
            if addr is None:
                return None
            space = addr.getAddressSpace()
            if space is None:
                return None
            space_name = space.getName()
            size = max(1, int(output_size or varnode.getSize() or 0))
            if space_name == "stack":
                return StorageInfo(
                    is_register=False,
                    space_name="stack",
                    offset=int(varnode.getOffset()),
                    size=size,
                    size_bits=size * 8,
                )
            if space_name == "register":
                reg_name = None
                try:
                    reg = self.tracer.program.getRegister(addr, size)
                    reg_name = reg.getName() if reg is not None else None
                except Exception:
                    reg_name = None
                return StorageInfo(
                    is_register=True,
                    space_name="register",
                    offset=int(varnode.getOffset()),
                    size=size,
                    size_bits=size * 8,
                    register_name=reg_name,
                    base_register_name=reg_name,
                    base_register_offset=int(varnode.getOffset()),
                    base_register_size=size,
                    base_register_size_bits=size * 8,
                    bit_offset_in_base=0,
                )
        except Exception:
            return None
        return None

    def _resolve_indirect_post_state_read(
        self,
        output_varnode,
        fallback_expr: Expression,
        conditions: List[Condition],
        depth: int,
        output_size: int = 0,
    ) -> Expression:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return fallback_expr
        if not self.parameters:
            return fallback_expr

        location = self._infer_indirect_output_location(output_varnode, output_size)
        if location is None:
            if self.debug:
                self._debug_print(
                    f"INDIRECT post-state read fell back to pre-state value: {self._debug_expr_summary(fallback_expr)}",
                    depth,
                )
            return fallback_expr

        resolved = rewrite_location_read_from_effects(
            location,
            fallback_expr,
            conditions,
            self.effect_summary.effects,
            self.parameters,
        )
        reduced = _reduce_expression_under_conditions(resolved, conditions)
        resolved = reduced if reduced is not None else resolved
        if self._expression_contains_unknown_or_call(resolved):
            return fallback_expr

        if self.debug and not _expressions_equivalent(resolved, fallback_expr):
            self._debug_print(
                f"Resolved INDIRECT post-state read via effect summary: {self._debug_expr_summary(fallback_expr)} -> {self._debug_expr_summary(resolved)}",
                depth,
            )
        return resolved
