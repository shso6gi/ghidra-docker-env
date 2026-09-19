# -*- coding: utf-8 -*-
"""P-codeトレースロジック"""

from __future__ import annotations
from dataclasses import dataclass
import inspect
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple, Any, TYPE_CHECKING
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Expression,
    ExpressionType,
    Condition,
    StorageInfo,
    CallTargetRef,
    UnknownValueRef,
    AddressValueRef,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PcodeOpRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
)
from scripts.function_tracer_pcode.core.intrinsics import resolve_pcode_intrinsic
from scripts.function_tracer_pcode.core.signature import (
    get_data_type_display_name,
    is_unsigned_data_type,
)
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation
from scripts.function_tracer_pcode.config.settings import MAX_TRACE_DEPTH
from scripts.function_tracer_pcode.analysis.debug.unknown_trace import (
    UnknownTracker,
    UnknownEvent,
    UnknownReason,
    VarnodeInfo,
    PcodeOpInfo,
)
from scripts.function_tracer_pcode.analysis.tracer_calls import CallRecoveryMixin
from scripts.function_tracer_pcode.analysis.tracer_storage import ParameterStorageMixin
from scripts.function_tracer_pcode.analysis.tracer_addresses import AddressRefMixin
from scripts.function_tracer_pcode.analysis.tracer_support import (
    _callable_accepts_positional_args,
    ParameterStorageDescriptor,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_expression

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.analysis.phi_resolver import PhiHandler


class VarnodeKey:
    """Varnodeを識別するためのキー"""
    
    def __init__(self, space_id: Optional[int], space_name: str, offset: int, size: int):
        self.space_id = space_id
        self.space_name = space_name
        self.offset = offset
        self.size = size
    
    def __hash__(self):
        return hash((self.space_id, self.space_name, self.offset, self.size))
    
    def __eq__(self, other):
        if not isinstance(other, VarnodeKey):
            return False
        return (self.space_id == other.space_id and
                self.space_name == other.space_name and
                self.offset == other.offset and 
                self.size == other.size)
    
    def __repr__(self):
        return f"VarnodeKey({self.space_id},{self.space_name},0x{self.offset:x},{self.size})"
    
    @classmethod
    def from_varnode(cls, varnode) -> 'VarnodeKey':
        """GhidraのVarnodeからキーを作成"""
        addr = varnode.getAddress()
        space = addr.getAddressSpace()
        return cls(
            space_id=int(space.getSpaceID()) if space is not None else None,
            space_name=str(space.getName()) if space is not None else "unknown",
            offset=varnode.getOffset(),
            size=varnode.getSize()
        )


class PcodeTracer(CallRecoveryMixin, ParameterStorageMixin, AddressRefMixin):
    """
    P-codeのデータフロー解析とトレースを行うクラス
    """
    
    def __init__(
        self,
        program,
        high_function,
        debug: bool = False,
        *,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
        binary_id: Optional[str] = None,
    ):
        self.program = program
        self.high_function = high_function
        self.debug = debug
        self._function_binary_id = binary_id
        self.record_deferred_call: Optional[
            Callable[[Any, List[Expression], Optional[Expression], Optional[PcodeOpRef]], Any]
        ] = None
        self._debug_message_limit = 4000
        self._debug_message_count = 0
        self._debug_suppressed = False
        
        # トレース済みのキャッシュ（一意なキー -> Expression）
        self._trace_cache: Dict[Tuple[Any, ...], Expression] = {}
        
        # トレース中のスタック（循環検出用）
        self._trace_stack: Set[Tuple[Any, ...]] = set()
        
        # Unknown発生追跡
        self.unknown_tracker = UnknownTracker()
        if debug:
            self.unknown_tracker.enable()
        
        # PHI handler（analyzerから設定される）
        self.phi_handler: Optional['PhiHandler'] = None
        self.condition_tracker = None
        self._parameter_descriptors: List[ParameterStorageDescriptor] = []
        self._bound_parameter_values: Dict[int, Expression] = {
            int(index): self._clone_expression(expr)
            for index, expr in (bound_parameter_values or {}).items()
            if expr is not None
        }
        self._bound_parameter_storage_values: Dict[Tuple[Any, ...], Expression] = {
            tuple(key): self._clone_expression(expr)
            for key, expr in (bound_parameter_storage_values or {}).items()
            if key is not None and expr is not None
        }
        (
            self._function_program_id,
            self._function_entry_space,
            self._function_entry_offset,
        ) = self._resolve_current_function_scope()
        self._parameter_descriptors = self._collect_parameter_descriptors()
        
        self._collect_debug_info()

    def _resolve_callother_userop_name(self, pcode_op: Any) -> Optional[str]:
        if pcode_op is None:
            return None
        try:
            if pcode_op.getNumInputs() < 1:
                return None
            userop_id = int(pcode_op.getInput(0).getOffset())
        except Exception:
            return None
        language = getattr(self.program, "getLanguage", lambda: None)()
        get_name = getattr(language, "getUserDefinedOpName", None)
        if callable(get_name):
            try:
                name = get_name(userop_id)
            except Exception:
                name = None
            if name:
                return str(name)
        return None

    def _get_op_order_key(self, pcode_op) -> Optional[int]:
        """Return a comparable intra-address P-code op order, if available.

        This is intentionally narrower than ``PcodeOpRef.stable_key()``. Memory
        read ordering and live-in checks need a monotonic integer order for
        comparisons, not a structural identity tuple.
        """
        if pcode_op is None:
            return None
        seqnum = getattr(pcode_op, "getSeqnum", lambda: None)()
        if seqnum is not None:
            order = getattr(seqnum, "getOrder", lambda: None)()
            coerced = self._coerce_op_order_value(order)
            if coerced is not None:
                return coerced
        order = getattr(pcode_op, "getOrder", lambda: None)()
        return self._coerce_op_order_value(order)

    @staticmethod
    def _coerce_op_order_value(value) -> Optional[int]:
        if value is None:
            return None
        try:
            return int(value)
        except (TypeError, ValueError):
            return None

    def _clone_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PHI and expr.value:
            cloned_branches = []
            for cond, value in expr.value:
                cloned_cond = None
                if cond is not None:
                    cloned_cond = Condition(
                        self._clone_expression(cond.expression),
                        cond.negated,
                    )
                cloned_branches.append((cloned_cond, self._clone_expression(value)))
            cloned = Expression.phi(cloned_branches)
            cloned.size = expr.size
            cloned.data_type = expr.data_type
            cloned.data_type_obj = getattr(expr, "data_type_obj", None)
            cloned.storage_info = getattr(expr, "storage_info", None)
            cloned.read_order_key = getattr(expr, "read_order_key", None)
            cloned.runtime_ref = getattr(expr, "runtime_ref", None)
            cloned.opcode = getattr(expr, "opcode", None)
            return cloned

        cloned = Expression(
            expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=[
                self._clone_expression(operand)
                for operand in (expr.operands or [])
            ],
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            data_type_obj=getattr(expr, "data_type_obj", None),
            storage_info=getattr(expr, "storage_info", None),
            read_order_key=getattr(expr, "read_order_key", None),
            runtime_ref=getattr(expr, "runtime_ref", None),
            opcode=getattr(expr, "opcode", None),
        )
        return cloned

    def _debug_print(self, msg: str) -> None:
        if not self.debug:
            return
        if self._debug_message_count >= self._debug_message_limit:
            if not self._debug_suppressed:
                print(
                    f"[PcodeTracer] debug output suppressed after "
                    f"{self._debug_message_limit} messages"
                )
                self._debug_suppressed = True
            return
        self._debug_message_count += 1
        print(msg)

    def _debug_available(self) -> bool:
        return self.debug and self._debug_message_count < self._debug_message_limit

    def _get_op_key(self, pcode_op) -> Tuple[Any, ...]:
        """PcodeOpの一意なキーを生成（同一seqnumの異なるopを区別）"""
        seq = pcode_op.getSeqnum()
        if seq:
            target = seq.getTarget()
            time = getattr(seq, "getTime", lambda: None)()
            order = seq.getOrder()
            obj_id = id(pcode_op)
            target_offset = None
            if target is not None:
                get_offset = getattr(target, "getOffset", None)
                if callable(get_offset):
                    try:
                        target_offset = int(get_offset())
                    except Exception:
                        target_offset = None
            return (
                "pcode_op_instance",
                target_offset,
                None if time is None else int(time),
                None if order is None else int(order),
                obj_id,
            )
        obj_id = id(pcode_op)
        return (
            "pcode_op_instance",
            None,
            None,
            None,
            pcode_op.hashCode(),
            pcode_op.getMnemonic(),
            obj_id,
        )

    def _make_pcode_op_ref(self, pcode_op) -> Optional[PcodeOpRef]:
        return PcodeOpRef.from_pcode_op(
            pcode_op,
            binary_id=self._function_binary_id,
            program_uid=self._function_program_id,
            function_entry_space=self._function_entry_space,
            function_entry_offset=self._function_entry_offset,
        )
    
    def _collect_debug_info(self):
        """デバッグ用の情報を収集"""
        if self.debug:
            self._debug_print("\n" + "=" * 60)
            self._debug_print("DEBUG: PcodeTracer Initialization")
            self._debug_print("=" * 60)
            
            local_map = self.high_function.getLocalSymbolMap()
            if local_map:
                self._debug_print("\nLocal Symbols:")
                for sym in local_map.getSymbols():
                    if not self._debug_available():
                        break
                    self._debug_print(
                        f"  - {sym.getName()}: type={sym.getDataType()}, "
                        f"isParam={sym.isParameter()}, storage={sym.getStorage()}"
                    )
                    
                    high_var = sym.getHighVariable()
                    if high_var:
                        rep = high_var.getRepresentative()
                        if rep:
                            self._debug_print(
                                f"    Representative Varnode: {rep}, "
                                f"addr={rep.getAddress()}, size={rep.getSize()}"
                            )
            self._debug_print("=" * 60 + "\n")
    
    def clear_cache(self):
        """キャッシュをクリア"""
        self._trace_cache.clear()
        self._trace_stack.clear()

    def emit_unknown_event(self, reason, varnode=None, def_op=None,
                           depth=0, note=None, context="tracer"):
        """Unknown発生イベントを記録"""
        event = UnknownEvent(
            reason=UnknownReason.from_string(reason),
            reason_str=reason, depth=depth,
            varnode=VarnodeInfo.from_varnode(varnode),
            def_op=PcodeOpInfo.from_pcodeop(def_op),
            note=note, context=context
        )
        self.unknown_tracker.record(event)
        if self.debug:
            self._debug_print(event.format_detail(indent=depth))
    
    def trace_varnode(self, varnode, depth: int = 0, use_cache: bool = True) -> Expression:
        """
        Varnodeを逆順にトレースして式を構築
        
        Args:
            varnode: トレース対象のVarnode
            depth: 現在のトレース深度
            use_cache: キャッシュを使用するか
        
        Returns:
            Expression: 展開された式
        """
        if varnode is None:
            self.emit_unknown_event(reason="null", depth=depth,
                                    note="Null varnode passed to trace_varnode")
            return Expression.unknown("null")
        
        if depth > MAX_TRACE_DEPTH:
            self.emit_unknown_event(reason="max_depth_exceeded", varnode=varnode,
                                    depth=depth, note=f"Exceeded {MAX_TRACE_DEPTH}")
            return Expression.unknown("max_depth_exceeded")
        
        if self._debug_available():
            self._debug_print_varnode(varnode, depth)
        
        return self._trace_varnode_internal(varnode, depth, use_cache)
    
    def _debug_print_varnode(self, varnode, depth: int):
        """Varnodeのデバッグ情報を出力"""
        if not self._debug_available():
            return
        indent = "  " * depth
        self._debug_print(f"\n{indent}DEBUG trace_varnode (depth={depth}):")
        self._debug_print(f"{indent}  varnode: {varnode}")
        self._debug_print(f"{indent}  address: {varnode.getAddress()}")
        self._debug_print(f"{indent}  size: {varnode.getSize()}")
        self._debug_print(f"{indent}  isConstant: {varnode.isConstant()}")
        self._debug_print(f"{indent}  isRegister: {varnode.isRegister()}")
        self._debug_print(f"{indent}  isUnique: {varnode.isUnique()}")
        self._debug_print(f"{indent}  isAddress: {varnode.isAddress()}")
        self._debug_print(f"{indent}  isInput: {varnode.isInput()}")
        
        def_op = varnode.getDef()
        self._debug_print(f"{indent}  getDef(): {def_op}")
        if def_op:
            self._debug_print(f"{indent}    def mnemonic: {def_op.getMnemonic()}")
            self._debug_print(f"{indent}    def seqnum: {def_op.getSeqnum()}")
        
        high_var = varnode.getHigh()
        self._debug_print(f"{indent}  getHigh(): {high_var}")
        if high_var:
            self._debug_print(f"{indent}    high name: {high_var.getName()}")
            self._debug_print(f"{indent}    high type: {type(high_var).__name__}")
            symbol = high_var.getSymbol()
            self._debug_print(f"{indent}    symbol: {symbol}")
            if symbol:
                self._debug_print(f"{indent}      symbol name: {symbol.getName()}")
                self._debug_print(f"{indent}      isParameter: {symbol.isParameter()}")
        
        # ストレージ情報を出力
        storage_info = self._get_storage_info_from_varnode(varnode)
        if storage_info:
            self._debug_print(f"{indent}  storage_info:")
            self._debug_print(f"{indent}    is_register: {storage_info.is_register}")
            self._debug_print(f"{indent}    register_name: {storage_info.register_name}")
            self._debug_print(f"{indent}    base_register_name: {storage_info.base_register_name}")
            self._debug_print(f"{indent}    bit_offset_in_base: {storage_info.bit_offset_in_base}")
            self._debug_print(f"{indent}    size_bits: {storage_info.size_bits}")
    
    def _trace_varnode_internal(self, varnode, depth: int, use_cache: bool = True) -> Expression:
        """Varnodeトレースの内部処理"""
        
        # 1. 定数かどうかチェック（最優先）
        if varnode.isConstant():
            value = varnode.getOffset()
            if self._debug_available():
                self._debug_print(f"  -> Constant: 0x{value:x}")
            return Expression.constant(
                value,
                varnode.getSize(),
                runtime_ref=self._make_address_runtime_ref_for_offset(value),
            )
        
        # ストレージ情報を取得
        storage_info = self._get_storage_info_from_varnode(varnode)
        
        # 2. 定義元のPcodeOpを取得
        def_op = varnode.getDef()
        
        if def_op is not None:
            if self._debug_available():
                self._debug_print(f"  -> Has def: {def_op.getMnemonic()}")
            return self._trace_pcode_op(def_op, depth + 1, use_cache)
        
        # 3. 定義がない場合は、入力変数
        if self._debug_available():
            self._debug_print("  -> No def, checking high variable")
        
        high_var = varnode.getHigh()
        if high_var:
            symbol = high_var.getSymbol()
            if symbol:
                sym_name = symbol.getName()
                
                if symbol.isParameter():
                    param_idx = -1
                    try:
                        param_idx = symbol.getCategoryIndex()
                    except:
                        pass
                    dtype_obj = symbol.getDataType() if symbol.getDataType() else None
                    dtype = str(dtype_obj) if dtype_obj else None
                    
                    if self._debug_available():
                        self._debug_print(f"  -> Parameter: {sym_name} (index={param_idx})")

                    bound_expr = self._resolve_bound_parameter_expression(
                        name=sym_name,
                        index=param_idx,
                        data_type=dtype,
                        data_type_obj=dtype_obj,
                        size_bytes=varnode.getSize(),
                        storage_info=storage_info,
                    )
                    if bound_expr is not None:
                        if self._debug_available():
                            self._debug_print(
                                "  -> Bound parameter argument: "
                                f"{summarize_expression(bound_expr)}"
                            )
                        return bound_expr
                    
                    return Expression.parameter(
                        sym_name, param_idx, dtype, dtype_obj, varnode.getSize(),
                        storage_info=storage_info,
                        runtime_ref=self._make_parameter_location_ref(
                            sym_name,
                            index=param_idx,
                        ),
                    )
                else:
                    dtype_obj = symbol.getDataType() if symbol.getDataType() else None
                    dtype = str(dtype_obj) if dtype_obj else None
                    runtime_ref = self._make_address_runtime_ref(
                        display_name=sym_name,
                        symbol=symbol,
                        high_var=high_var,
                    )
                    
                    if self._debug_available():
                        self._debug_print(f"  -> Variable (from symbol): {sym_name}")

                    if (
                        isinstance(runtime_ref, AddressValueRef)
                        and runtime_ref.has_concrete_address()
                        and varnode.isAddress()
                    ):
                        return self._global_object_value_expression(
                            varnode,
                            runtime_ref,
                            display_name=sym_name,
                            data_type=dtype,
                            data_type_obj=dtype_obj,
                            storage_info=storage_info,
                        )
                    
                    return Expression.variable(
                        sym_name, dtype, dtype_obj, varnode.getSize(),
                        storage_info=storage_info,
                        runtime_ref=runtime_ref,
                    )
            
            name = high_var.getName()
            if name and name != "UNNAMED":
                runtime_ref = self._make_address_runtime_ref(
                    display_name=name,
                    high_var=high_var,
                )
                if self._debug_available():
                    self._debug_print(f"  -> Variable (from high name): {name}")
                if (
                    isinstance(runtime_ref, AddressValueRef)
                    and runtime_ref.has_concrete_address()
                    and varnode.isAddress()
                ):
                    high_dtype_obj = None
                    try:
                        high_dtype_obj = high_var.getDataType()
                    except Exception:
                        high_dtype_obj = None
                    return self._global_object_value_expression(
                        varnode,
                        runtime_ref,
                        display_name=name,
                        data_type=str(high_dtype_obj) if high_dtype_obj is not None else None,
                        data_type_obj=high_dtype_obj,
                        storage_info=storage_info,
                    )
                return Expression.variable(
                    name, size=varnode.getSize(),
                    storage_info=storage_info,
                    runtime_ref=runtime_ref,
                )

        storage_backed_param = self._resolve_storage_backed_parameter_expression(
            storage_info,
        )
        if storage_backed_param is not None:
            if self._debug_available():
                self._debug_print(
                    "  -> Parameter (storage-backed fallback): "
                    f"{summarize_expression(storage_backed_param)}"
                )
            return storage_backed_param
        
        # 4. レジスタの場合（入力変数として扱う）
        if varnode.isRegister():
            reg = self.program.getRegister(varnode.getAddress(), varnode.getSize())
            if reg:
                reg_name = reg.getName()
                if self._debug_available():
                    self._debug_print(f"  -> Register (input): {reg_name}")
                    self._debug_print(f"     isInput: {varnode.isInput()}")
                    self._debug_print(f"     storage_info: {storage_info}")
                
                # 入力varnodeの場合は変数として扱う
                return Expression.variable(
                    reg_name, size=varnode.getSize(),
                    storage_info=storage_info
                )
        
        # 5. アドレス空間の変数（メモリ）
        if varnode.isAddress():
            addr = varnode.getAddress()
            runtime_ref = self._make_address_runtime_ref(
                display_name=str(addr) if addr is not None else None,
                high_var=high_var,
            )
            if self._debug_available():
                self._debug_print(f"  -> Memory address: {addr}")
            return Expression.constant(
                addr.getOffset(),
                varnode.getSize(),
                runtime_ref=runtime_ref,
            )
        
        # 6. ユニーク変数
        if varnode.isUnique():
            offset = varnode.getOffset()
            if self._debug_available():
                self._debug_print(f"  -> Unique (untraced): 0x{offset:x}")
            return Expression.unknown(f"unique_0x{offset:x}")
        
        # 7. 不明
        if self._debug_available():
            self._debug_print("  -> Unknown")
        
        key = VarnodeKey.from_varnode(varnode)
        return Expression.unknown(f"untraced_{key.space_name}_0x{key.offset:x}")
    
    def _trace_pcode_op(self, pcode_op, depth: int, use_cache: bool = True) -> Expression:
        """PcodeOpをトレースして式を構築"""
        op_key = self._get_op_key(pcode_op)
        
        # キャッシュチェック
        if use_cache and op_key in self._trace_cache:
            if self._debug_available():
                self._debug_print(f"  -> Cache hit for {pcode_op.getMnemonic()} (key={op_key})")
            return self._trace_cache[op_key]
        
        # 循環検出
        if op_key in self._trace_stack:
            if self._debug_available():
                self._debug_print(f"  -> Circular reference detected (key={op_key})")
            self.emit_unknown_event(reason="circular_reference", def_op=pcode_op,
                                    depth=depth, note=f"Key {op_key} already in stack")
            return Expression.unknown("circular_reference")
        
        self._trace_stack.add(op_key)
        
        try:
            result = self._trace_pcode_op_internal(pcode_op, depth, use_cache)
            if use_cache:
                self._trace_cache[op_key] = result
            return result
        finally:
            self._trace_stack.discard(op_key)
    
    def _trace_pcode_op_internal(self, pcode_op, depth: int, use_cache: bool = True) -> Expression:
        """PcodeOpトレースの内部処理"""
        mnemonic = pcode_op.getMnemonic()
        
        if self._debug_available():
            indent = "  " * depth
            self._debug_print(f"\n{indent}DEBUG trace_pcode_op (depth={depth}):")
            self._debug_print(f"{indent}  mnemonic: {mnemonic}")
            self._debug_print(f"{indent}  num_inputs: {pcode_op.getNumInputs()}")
            self._debug_print(f"{indent}  key: {self._get_op_key(pcode_op)}")
        
        inputs = []
        for i in range(pcode_op.getNumInputs()):
            input_varnode = pcode_op.getInput(i)
            inputs.append(input_varnode)
        
        # COPY
        if mnemonic == "COPY":
            if inputs:
                return self.trace_varnode(inputs[0], depth, use_cache)
            return Expression.unknown("copy_no_input")
        
        # 二項演算
        binary_ops = {
            "INT_ADD", "INT_SUB", "INT_MULT", "INT_DIV", "INT_SDIV",
            "INT_REM", "INT_SREM", "INT_AND", "INT_OR", "INT_XOR",
            "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
            "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS",
            "INT_LESSEQUAL", "INT_SLESSEQUAL",
            "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV",
            "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL",
            "BOOL_AND", "BOOL_OR", "BOOL_XOR",
        }
        
        if mnemonic in binary_ops:
            if len(inputs) >= 2:
                left = self.trace_varnode(inputs[0], depth, use_cache)
                right = self.trace_varnode(inputs[1], depth, use_cache)
                return Expression.binary_op(mnemonic, left, right)
            return Expression.unknown(f"{mnemonic}_insufficient_inputs")
        
        # 単項演算
        unary_ops = {
            "INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT",
            "FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT",
            "TRUNC", "FLOAT_FLOAT2FLOAT", "FLOAT_INT2FLOAT", "FLOAT_CEIL", "FLOAT_FLOOR",
            "POPCOUNT", "LZCOUNT",
        }
        
        if mnemonic in unary_ops:
            if inputs:
                operand = self.trace_varnode(inputs[0], depth, use_cache)
                result = Expression.unary_op(mnemonic, operand)
                # 出力サイズを取得（INT_ZEXT/INT_SEXTなどで重要）
                output = pcode_op.getOutput()
                if output:
                    result.size = output.getSize()
                return result
            return Expression.unknown(f"{mnemonic}_no_input")
        
        # CALL
        if mnemonic == "CALL":
            if inputs:
                target_ref = self._resolve_call_target_ref_from_op(
                    pcode_op,
                    depth,
                    use_cache,
                    allow_containing=True,
                    allow_code_address=True,
                )
                func_name = target_ref.display_name()
                self.emit_unknown_event(
                    reason="call_out_of_scope",
                    varnode=pcode_op.getOutput(),
                    def_op=pcode_op,
                    depth=depth,
                    note=f"CALL target={func_name}",
                )
                return self._build_unresolved_call_unknown(
                    pcode_op,
                    depth,
                    use_cache,
                    reason="call_out_of_scope",
                    target_ref=target_ref,
                )
            return Expression.unknown("call_no_target")

        # CALLIND
        if mnemonic == "CALLIND":
            if inputs:
                target_ref = self._resolve_call_target_ref_from_op(
                    pcode_op,
                    depth,
                    use_cache,
                    allow_containing=True,
                    allow_code_address=True,
                )
                target_name = target_ref.display_name()
                self.emit_unknown_event(
                    reason="callind_out_of_scope",
                    varnode=pcode_op.getOutput(),
                    def_op=pcode_op,
                    depth=depth,
                    note=f"CALLIND target={target_name}",
                )
                return self._build_unresolved_call_unknown(
                    pcode_op,
                    depth,
                    use_cache,
                    reason="callind_out_of_scope",
                    target_ref=target_ref,
                )
            return Expression.unknown("callind_no_target")
        
        # LOAD
        if mnemonic == "LOAD":
            if len(inputs) >= 2:
                addr = self.trace_varnode(inputs[1], depth, use_cache)
                output = pcode_op.getOutput()
                size = output.getSize() if output else 4
                order_key = self._get_op_order_key(pcode_op)
                return Expression.memory(
                    addr,
                    size,
                    read_order_key=order_key,
                    runtime_ref=ObservedMemoryReadRef(
                        order_key=order_key,
                        pcode_op_ref=self._make_pcode_op_ref(pcode_op),
                    ),
                )
            return Expression.unknown("load_insufficient_inputs")
        
        # STORE
        if mnemonic == "STORE":
            return Expression.unknown("store_no_output")
        
        # MULTIEQUAL - PhiHandlerで展開
        if mnemonic == "MULTIEQUAL":
            if self._debug_available():
                self._debug_print(f"\n{' ' * depth}  MULTIEQUAL detected - expanding via PhiHandler")
            
            if self.phi_handler is None:
                self.emit_unknown_event(
                    reason="phi_no_handler", varnode=pcode_op.getOutput(),
                    def_op=pcode_op, depth=depth, note="phi_handler is None"
                )
                if self.debug:
                    raise RuntimeError("phi_handler is None")
                return Expression.unknown("phi_no_handler_CRITICAL")
            
            try:
                phi_branches = self.phi_handler.resolve_multiequal(pcode_op, depth)
                
                if not phi_branches:
                    self.emit_unknown_event(
                        reason="phi_no_branches", varnode=pcode_op.getOutput(),
                        def_op=pcode_op, depth=depth,
                        note="PhiHandler returned empty"
                    )
                    return Expression.unknown("phi_no_branches")
                
                if len(phi_branches) == 1:
                    return phi_branches[0].value
                
                # 複数分岐 → PHI式構築
                branches = []
                for pb in phi_branches:
                    all_conds = pb.get_all_conditions()
                    if all_conds:
                        combined_cond = Condition.combine_and(all_conds)
                        branches.append((combined_cond, pb.value))
                    else:
                        branches.append((None, pb.value))
                
                output = pcode_op.getOutput()
                phi_expr = Expression.phi(branches)
                phi_expr.size = output.getSize() if output else 0
                return phi_expr
            
            except AnalysisLimitation:
                # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                raise
            except Exception as e:
                if self.debug:
                    import traceback as tb
                    tb.print_exc()
                self.emit_unknown_event(
                    reason="phi_expansion_error", varnode=pcode_op.getOutput(),
                    def_op=pcode_op, depth=depth, note=str(e)
                )
                if self.debug:
                    raise
                return Expression.unknown(f"phi_error:{str(e)[:50]}")
        
        # CAST
        if mnemonic == "CAST":
            if inputs:
                return self.trace_varnode(inputs[0], depth, use_cache)
            return Expression.unknown("cast_no_input")
        
        # PTRADD
        if mnemonic == "PTRADD":
            if len(inputs) >= 3:
                base = self.trace_varnode(inputs[0], depth, use_cache)
                index = self.trace_varnode(inputs[1], depth, use_cache)
                element_size = self.trace_varnode(inputs[2], depth, use_cache)
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else max(
                    base.size if base is not None else 0,
                    index.size if index is not None else 0,
                    element_size.size if element_size is not None else 0,
                )
                intrinsic = Expression.intrinsic(
                    "PTRADD",
                    [base, index, element_size],
                    size=output_size,
                    opcode=PTRADD_OPCODE,
                )
                runtime_ref = self._derive_pointer_runtime_ref(intrinsic)
                if runtime_ref is not None:
                    intrinsic = intrinsic.clone_with(runtime_ref=runtime_ref)
                return intrinsic
            return Expression.unknown("ptradd_insufficient_inputs")

        # PTRSUB
        if mnemonic == "PTRSUB":
            if len(inputs) >= 2:
                base = self.trace_varnode(inputs[0], depth, use_cache)
                offset = self.trace_varnode(inputs[1], depth, use_cache)
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else max(
                    base.size if base is not None else 0,
                    offset.size if offset is not None else 0,
                )
                intrinsic = Expression.intrinsic(
                    "PTRSUB",
                    [base, offset],
                    size=output_size,
                    opcode=PTRSUB_OPCODE,
                )
                runtime_ref = self._derive_pointer_runtime_ref(intrinsic)
                if runtime_ref is not None:
                    intrinsic = intrinsic.clone_with(runtime_ref=runtime_ref)
                return intrinsic
            return Expression.unknown("ptrsub_insufficient_inputs")

        if mnemonic == "CALLOTHER":
            userop_name = self._resolve_callother_userop_name(pcode_op)
            if userop_name:
                intrinsic_spec = resolve_pcode_intrinsic(mnemonic=userop_name)
                if intrinsic_spec is not None and len(inputs) >= 1:
                    operands = [
                        self.trace_varnode(inp, depth, use_cache)
                        for inp in inputs[1:]
                    ]
                    output = pcode_op.getOutput()
                    output_size = output.getSize() if output is not None else 0
                    return Expression.intrinsic(
                        intrinsic_spec.mnemonic,
                        operands,
                        size=output_size,
                        opcode=intrinsic_spec.opcode,
                    )

        # PIECE - サイズ情報を保持
        if mnemonic == "PIECE":
            if len(inputs) >= 2:
                high = self.trace_varnode(inputs[0], depth, use_cache)
                low = self.trace_varnode(inputs[1], depth, use_cache)
                # サイズを取得
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else (high.size + low.size)
                expr = Expression.binary_op("PIECE", high, low)
                expr.size = output_size
                return expr
            return Expression.unknown("piece_insufficient_inputs")
        
        # SUBPIECE - サイズ情報を保持
        if mnemonic == "SUBPIECE":
            if len(inputs) >= 2:
                source = self.trace_varnode(inputs[0], depth, use_cache)
                offset = self.trace_varnode(inputs[1], depth, use_cache)
                # 出力サイズを取得
                output = pcode_op.getOutput()
                output_size = output.getSize() if output else 4
                expr = Expression.binary_op("SUBPIECE", source, offset)
                expr.size = output_size
                return expr
            return Expression.unknown("subpiece_insufficient_inputs")
        
        # その他
        if self._debug_available():
            self._debug_print(f"  -> Unhandled opcode: {mnemonic}")

        if mnemonic == "INDIRECT":
            output = pcode_op.getOutput()
            output_size = output.getSize() if output is not None else 0
            output_location = (
                self._canonical_location_for_varnode(output, output_size)
                if output is not None
                else None
            )
            input_location = None
            if inputs:
                try:
                    input_location = self._canonical_location_for_varnode(
                        inputs[0],
                        inputs[0].getSize(),
                    )
                except AnalysisLimitation:
                    # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                    # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                    raise
                except Exception:
                    input_location = None
            if (
                output is not None
                and output_location is not None
                and input_location is not None
                and output_location == input_location
            ):
                promoted = self._symbolic_post_state_read_for_output_varnode(
                    output,
                    output_size,
                )
                if promoted is not None:
                    return promoted
            base_expr = self.trace_varnode(inputs[0], depth, use_cache) if inputs else None
            if (
                base_expr is not None
                and base_expr.expr_type == ExpressionType.CONSTANT
                and int(getattr(base_expr, "value", 1)) == 0
                and output is not None
            ):
                promoted = self._symbolic_post_state_read_for_output_varnode(
                    output,
                    output_size,
                )
                if promoted is not None:
                    return promoted

        if inputs:
            traced_inputs = [self.trace_varnode(inp, depth, use_cache) for inp in inputs]
            if len(traced_inputs) == 1:
                return Expression.unary_op(mnemonic, traced_inputs[0])
            elif len(traced_inputs) == 2:
                return Expression.binary_op(mnemonic, traced_inputs[0], traced_inputs[1])
            else:
                output = pcode_op.getOutput()
                output_size = output.getSize() if output is not None else 0
                return Expression.intrinsic(
                    mnemonic,
                    traced_inputs,
                    size=output_size,
                    opcode=getattr(pcode_op, "getOpcode", lambda: None)(),
                )

        return Expression.unknown(f"unhandled_{mnemonic}")

    def get_all_pcode_ops(self) -> List[Any]:
        """全てのPcodeOpをリストで取得"""
        ops = []
        basic_blocks = self.high_function.getBasicBlocks()
        
        for bb in basic_blocks:
            pcode_iter = bb.getIterator()
            while pcode_iter.hasNext():
                ops.append(pcode_iter.next())
        
        return ops
    
    def find_return_ops(self) -> List[Any]:
        """RETURNオペレーションを全て取得"""
        returns = []
        
        for pcode_op in self.get_all_pcode_ops():
            if pcode_op.getMnemonic() == "RETURN":
                returns.append(pcode_op)
        
        return returns
