"""Call-site recovery: argument expressions, call targets and unresolved-call unknowns."""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Any
from scripts.function_tracer_pcode.core import (
    Expression,
    ExpressionType,
    StorageInfo,
    CallTargetRef,
    UnknownValueRef,
    PcodeOpRef,
)
from scripts.function_tracer_pcode.core.signature import get_data_type_display_name
from scripts.function_tracer_pcode.analysis.tracer_support import _callable_accepts_positional_args


class CallRecoveryMixin:
    """Call-site recovery: argument expressions, call targets and unresolved-call unknowns."""

    def _record_deferred_call(
        self,
        target_ref: CallTargetRef,
        args: List[Expression],
        call_target_expr: Optional[Expression],
        pcode_op_ref: Optional[PcodeOpRef],
    ):
        if self.record_deferred_call is None:
            return None
        if _callable_accepts_positional_args(self.record_deferred_call, 4):
            return self.record_deferred_call(target_ref, args, call_target_expr, pcode_op_ref)
        return self.record_deferred_call(target_ref, args, call_target_expr)

    def _recover_call_argument_expressions(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
        target_ref: Optional[CallTargetRef] = None,
    ) -> List[Expression]:
        recovered: List[Expression] = []
        if pcode_op is None:
            return recovered
        for index in range(1, pcode_op.getNumInputs()):
            try:
                recovered.append(
                    self.trace_varnode(pcode_op.getInput(index), depth + 1, use_cache)
                )
            except Exception:
                recovered.append(Expression.unknown(f"call_arg_{index}_unknown"))
        if recovered:
            return recovered
        return self._recover_implicit_call_argument_expressions(
            pcode_op,
            target_ref,
        )

    def _recover_implicit_call_argument_expressions(
        self,
        pcode_op,
        target_ref: Optional[CallTargetRef],
    ) -> List[Expression]:
        """Recover omitted ABI-register call arguments through path-covered evidence."""

        target_function = self._resolve_call_target_function(target_ref)
        if target_function is None:
            if self._debug_available():
                self._debug_print("  [CallArgRecovery] no target function for implicit CALL args")
            return []
        parameters = self._call_target_parameters(target_function)
        if not parameters:
            if self._debug_available():
                self._debug_print("  [CallArgRecovery] target function has no parameter objects")
            return []

        shared_recovered = self._recover_implicit_call_arguments_with_effect_model(
            pcode_op,
            parameters,
        )
        if len(shared_recovered) >= len(parameters):
            if self._debug_available():
                self._debug_print(
                    "  [CallArgRecovery] recovered implicit CALL args via shared effect model: "
                    + ", ".join(arg.to_string() for arg in shared_recovered[: len(parameters)])
                )
            return shared_recovered[: len(parameters)]
        if self._debug_available():
            self._debug_print(
                "  [CallArgRecovery] shared effect-model recovery did not cover all params "
                f"(got={len(shared_recovered)}, expected={len(parameters)})"
            )
        return []

    def _recover_implicit_call_arguments_with_effect_model(
        self,
        pcode_op,
        parameters: Sequence[Any],
    ) -> List[Expression]:
        caller_parameters = self._caller_parameter_dicts_for_call_recovery()
        callee_parameters = [
            descriptor
            for parameter in parameters
            for descriptor in [self._call_parameter_descriptor(parameter)]
            if descriptor is not None
        ]
        if not caller_parameters or len(callee_parameters) != len(parameters):
            return []
        try:
            from scripts.function_tracer_pcode.analysis.effects.summary import (
                _recover_call_argument_expressions as recover_call_args,
            )

            recovered = recover_call_args(
                pcode_op,
                self,
                caller_parameters,
                callee_parameters,
                [],
                condition_tracker=getattr(self, "condition_tracker", None),
            )
        except Exception:
            return []
        return list(recovered or [])

    def _caller_parameter_dicts_for_call_recovery(self) -> List[Dict[str, Any]]:
        result: List[Dict[str, Any]] = []
        for descriptor in self._parameter_descriptors:
            result.append(
                {
                    "name": descriptor.name,
                    "index": descriptor.index,
                    "size": descriptor.size_bytes,
                    "data_type": descriptor.data_type,
                    "data_type_obj": descriptor.data_type_obj,
                    "is_signed": descriptor.is_signed,
                    "storage": descriptor.storage_info,
                    "storage_info": descriptor.storage_info,
                }
            )
        return result

    def _call_parameter_descriptor(self, parameter) -> Optional[Dict[str, Any]]:
        storage_info = self._call_parameter_storage_info(parameter)
        if storage_info is None:
            return None
        name = ""
        for accessor in ("getName", "getNameString"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                name = str(getter() or "")
            except Exception:
                name = ""
            if name:
                break
        index = -1
        for accessor in ("getOrdinal", "getIndex"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                index = int(getter())
            except Exception:
                index = -1
            if index >= 0:
                break
        size_bytes = 0
        for accessor in ("getLength", "getSize"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                size_bytes = int(getter())
            except Exception:
                size_bytes = 0
            if size_bytes > 0:
                break
        if size_bytes <= 0:
            size_bytes = max(1, int(getattr(storage_info, "size", 0) or 0))
        data_type_obj = None
        try:
            data_type_obj = parameter.getDataType()
        except Exception:
            data_type_obj = None
        data_type = get_data_type_display_name(data_type_obj)
        return {
            "name": name or f"param_{index + 1 if index >= 0 else len(name)}",
            "index": index,
            "size": max(1, int(size_bytes)),
            "data_type": data_type,
            "data_type_obj": data_type_obj,
            "is_signed": self._coerce_descriptor_signedness(data_type_obj, data_type),
            "storage": storage_info,
            "storage_info": storage_info,
        }

    def _resolve_call_target_function(
        self,
        target_ref: Optional[CallTargetRef],
    ):
        function_obj = getattr(target_ref, "function_obj", None)
        if function_obj is not None:
            return function_obj
        address_offset = getattr(target_ref, "entry_offset", None)
        if address_offset is None:
            address_offset = getattr(target_ref, "address_offset", None)
        if address_offset is None or self.program is None:
            return None
        try:
            address_factory = self.program.getAddressFactory()
            default_space = address_factory.getDefaultAddressSpace()
            address = default_space.getAddress(int(address_offset))
            function_manager = self.program.getFunctionManager()
            return function_manager.getFunctionAt(address)
        except Exception:
            return None

    def _call_target_parameters(self, target_function) -> List[Any]:
        get_parameters = getattr(target_function, "getParameters", None)
        if callable(get_parameters):
            try:
                return list(get_parameters() or [])
            except Exception:
                return []
        return []

    def _call_parameter_storage_info(self, parameter) -> Optional[StorageInfo]:
        storage = None
        for accessor in ("getVariableStorage", "getStorage"):
            getter = getattr(parameter, accessor, None)
            if not callable(getter):
                continue
            try:
                storage = getter()
            except Exception:
                storage = None
            if storage is not None:
                break
        return self._get_storage_info_from_variable_storage(storage)

    def _recover_call_target_expression(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
    ) -> Optional[Expression]:
        if pcode_op is None or pcode_op.getNumInputs() < 1:
            return None
        try:
            return self.trace_varnode(pcode_op.getInput(0), depth + 1, use_cache)
        except Exception:
            return None

    def _resolve_call_target_ref_from_expression(
        self,
        expr: Optional[Expression],
        *,
        allow_containing: bool = True,
        allow_code_address: bool = True,
    ) -> Optional[CallTargetRef]:
        if expr is None or expr.expr_type != ExpressionType.CONSTANT:
            return None
        try:
            address_value = int(expr.value)
        except (TypeError, ValueError):
            return None
        if address_value < 0 or self.program is None:
            return None

        try:
            address_factory = self.program.getAddressFactory()
            default_space = address_factory.getDefaultAddressSpace()
            address = default_space.getAddress(address_value)
        except Exception:
            address = None
        if address is None:
            return None

        try:
            function_manager = self.program.getFunctionManager()
        except Exception:
            function_manager = None
        if function_manager is not None:
            for accessor in ("getFunctionAt", "getReferencedFunction"):
                getter = getattr(function_manager, accessor, None)
                if callable(getter):
                    try:
                        function = getter(address)
                    except Exception:
                        function = None
                    if function is not None:
                        return CallTargetRef.from_function(function)
            if allow_containing:
                getter = getattr(function_manager, "getFunctionContaining", None)
                if callable(getter):
                    try:
                        function = getter(address)
                    except Exception:
                        function = None
                    if function is not None:
                        return CallTargetRef.from_function(function)

        if not allow_code_address:
            return None
        return CallTargetRef.from_code_address(address_value)

    def _resolve_call_target_ref_from_op(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
        *,
        allow_containing: bool = True,
        allow_code_address: bool = True,
    ) -> CallTargetRef:
        try:
            target_varnode = pcode_op.getInput(0)
        except Exception:
            target_varnode = None
        direct_ref = self.resolve_call_target_ref(
            target_varnode,
            allow_containing=allow_containing,
            allow_code_address=allow_code_address,
        ) if target_varnode is not None else None
        if direct_ref is not None and not direct_ref.is_unknown():
            return direct_ref

        target_expr = self._recover_call_target_expression(
            pcode_op,
            depth,
            use_cache,
        )
        expr_ref = self._resolve_call_target_ref_from_expression(
            target_expr,
            allow_containing=allow_containing,
            allow_code_address=allow_code_address,
        )
        if expr_ref is not None:
            return expr_ref
        return direct_ref or CallTargetRef.unknown()

    def _build_unresolved_call_unknown(
        self,
        pcode_op,
        depth: int,
        use_cache: bool,
        *,
        reason: str,
        target_ref: CallTargetRef,
    ) -> Expression:
        target_label = target_ref.display_name()
        runtime_ref = None
        display_name = None

        if self.record_deferred_call is not None:
            deferred_args = self._recover_call_argument_expressions(
                pcode_op,
                depth,
                use_cache,
                target_ref,
            )
            deferred_target_expr = self._recover_call_target_expression(
                pcode_op,
                depth,
                use_cache,
            )
            recorded = self._record_deferred_call(
                target_ref,
                deferred_args,
                deferred_target_expr,
                self._make_pcode_op_ref(pcode_op),
            )
            if isinstance(recorded, str):
                display_name = recorded
            else:
                runtime_ref = recorded
                if hasattr(recorded, "display_name"):
                    display_name = recorded.display_name()

        if runtime_ref is None:
            runtime_ref = UnknownValueRef.out_of_scope_call(
                reason=reason,
                target_ref=target_ref,
                display_hint=target_label,
            )
        if display_name is None:
            display_name = runtime_ref.display_name() if hasattr(runtime_ref, "display_name") else f"{reason}:{target_label}"

        return Expression.unknown(display_name, runtime_ref=runtime_ref)

    def resolve_call_target_ref(
        self,
        addr_varnode,
        *,
        allow_containing: bool = True,
        allow_code_address: bool = True,
    ) -> Optional[CallTargetRef]:
        """CALL/CALLIND の target を object ベースで解決する。"""
        if addr_varnode is None or self.program is None:
            return None

        address = None
        try:
            if addr_varnode.isConstant():
                address = addr_varnode.getAddress()
            else:
                candidate = addr_varnode.getAddress()
                space = candidate.getAddressSpace() if candidate else None
                if space and not (
                    space.isRegisterSpace()
                    or space.isUniqueSpace()
                    or space.isConstantSpace()
                ):
                    address = candidate
        except Exception:
            address = None

        if address is None:
            return None

        try:
            function_manager = self.program.getFunctionManager()
            if function_manager is not None:
                get_function_at = getattr(function_manager, "getFunctionAt", None)
                if callable(get_function_at):
                    func = get_function_at(address)
                    if func is not None:
                        return CallTargetRef.from_function(func)
                get_referenced_function = getattr(function_manager, "getReferencedFunction", None)
                if callable(get_referenced_function):
                    func = get_referenced_function(address)
                    if func is not None:
                        return CallTargetRef.from_function(func)
                if allow_containing:
                    get_function_containing = getattr(function_manager, "getFunctionContaining", None)
                    if callable(get_function_containing):
                        func = get_function_containing(address)
                        if func is not None:
                            return CallTargetRef.from_function(func)
        except Exception:
            pass

        if not allow_code_address:
            return None

        try:
            return CallTargetRef.from_code_address(int(address.getOffset()))
        except Exception:
            return None
