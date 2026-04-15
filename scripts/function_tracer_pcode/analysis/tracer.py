# -*- coding: utf-8 -*-
"""P-codeトレースロジック"""

from __future__ import annotations
from typing import Dict, List, Optional, Set, Tuple, Any, TYPE_CHECKING
from ..model import Expression, ExpressionType, Condition, StorageInfo, CallTargetRef, UnknownValueRef, AddressValueRef
from ..config.settings import MAX_TRACE_DEPTH, DEBUG_MODE
from .debug.unknown_trace import (
    UnknownTracker, UnknownEvent, UnknownReason,
    VarnodeInfo, PcodeOpInfo
)

if TYPE_CHECKING:
    from .phi_resolver import PhiHandler

class VarnodeKey:
    """Varnodeを識別するためのキー"""
    
    def __init__(self, space: str, offset: int, size: int):
        self.space = space
        self.offset = offset
        self.size = size
    
    def __hash__(self):
        return hash((self.space, self.offset, self.size))
    
    def __eq__(self, other):
        if not isinstance(other, VarnodeKey):
            return False
        return (self.space == other.space and 
                self.offset == other.offset and 
                self.size == other.size)
    
    def __repr__(self):
        return f"VarnodeKey({self.space}, 0x{self.offset:x}, {self.size})"
    
    @classmethod
    def from_varnode(cls, varnode) -> 'VarnodeKey':
        """GhidraのVarnodeからキーを作成"""
        addr = varnode.getAddress()
        return cls(
            space=str(addr.getAddressSpace().getName()),
            offset=varnode.getOffset(),
            size=varnode.getSize()
        )


class PcodeTracer:
    """
    P-codeのデータフロー解析とトレースを行うクラス
    """
    
    def __init__(self, program, high_function, debug: bool = False):
        self.program = program
        self.high_function = high_function
        self.debug = debug
        self._debug_message_limit = 4000
        self._debug_message_count = 0
        self._debug_suppressed = False
        
        # トレース済みのキャッシュ（一意なキー -> Expression）
        self._trace_cache: Dict[str, Expression] = {}
        
        # トレース中のスタック（循環検出用）
        self._trace_stack: Set[str] = set()
        
        # Unknown発生追跡
        self.unknown_tracker = UnknownTracker()
        if debug:
            self.unknown_tracker.enable()
        
        # PHI handler（analyzerから設定される）
        self.phi_handler: Optional['PhiHandler'] = None
        
        self._collect_debug_info()

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

    def _make_address_runtime_ref(
        self,
        *,
        display_name: Optional[str] = None,
        symbol: Any = None,
        high_var: Any = None,
    ) -> Optional[AddressValueRef]:
        representative = None
        if high_var is not None:
            try:
                representative = high_var.getRepresentative()
            except Exception:
                representative = None

        probes = (
            (symbol, "getAddress", "symbol_address"),
            (high_var, "getAddress", "high_var_address"),
            (high_var, "getPCAddress", "high_var_pc_address"),
            (representative, "getAddress", "high_var_representative_address"),
            (representative, "getPCAddress", "high_var_representative_pc_address"),
        )
        probe_failures = []
        for owner, method_name, source in probes:
            if owner is None:
                continue
            getter = getattr(owner, method_name, None)
            if not callable(getter):
                probe_failures.append(f"{source}=missing_method")
                continue
            try:
                address = getter()
            except Exception as exc:
                probe_failures.append(f"{source}=error:{type(exc).__name__}")
                continue
            if address is None:
                probe_failures.append(f"{source}=none")
                continue
            try:
                offset = int(address.getOffset())
            except Exception as exc:
                probe_failures.append(f"{source}=bad_offset:{type(exc).__name__}")
                continue
            if offset < 0:
                probe_failures.append(f"{source}=negative_offset")
                continue
            space_name = None
            try:
                space = address.getAddressSpace()
                if space is not None:
                    space_name = space.getName()
            except Exception:
                space_name = None

            symbol_name = None
            if symbol is not None:
                try:
                    symbol_name = symbol.getName()
                except Exception:
                    symbol_name = None
            if not symbol_name:
                symbol_name = self._lookup_symbol_name_for_address(address)

            block_name = None
            is_initialized = None
            can_read = None
            can_write = None
            can_execute = None
            is_volatile = None
            try:
                memory = self.program.getMemory()
                block = memory.getBlock(address) if memory is not None else None
                if block is not None:
                    block_name = block.getName()
                    is_initialized = bool(block.isInitialized())
                    can_read = bool(block.isRead())
                    can_write = bool(block.isWrite())
                    can_execute = bool(block.isExecute())
                    is_volatile = bool(block.isVolatile())
            except Exception:
                pass

            return AddressValueRef(
                address_offset=offset,
                source=source,
                display_hint=display_name,
                space_name=space_name,
                symbol_name=symbol_name,
                block_name=block_name,
                is_initialized=is_initialized,
                can_read=can_read,
                can_write=can_write,
                can_execute=can_execute,
                is_volatile=is_volatile,
            )
        if self.debug and display_name:
            self._debug_print(
                "[PcodeTracer] failed to build AddressValueRef "
                f"name={display_name} probes={probe_failures}"
            )
        return None

    def _lookup_symbol_name_for_address(self, address) -> Optional[str]:
        if address is None:
            return None

        try:
            symbol_table = self.program.getSymbolTable()
        except Exception:
            symbol_table = None
        if symbol_table is not None:
            try:
                primary_symbol = symbol_table.getPrimarySymbol(address)
            except Exception:
                primary_symbol = None
            if primary_symbol is not None:
                try:
                    name = primary_symbol.getName()
                except Exception:
                    name = None
                if name:
                    return name

        try:
            listing = self.program.getListing()
        except Exception:
            listing = None
        if listing is None:
            return None

        for getter_name in ("getDataAt", "getDataContaining"):
            getter = getattr(listing, getter_name, None)
            if not callable(getter):
                continue
            try:
                data = getter(address)
            except Exception:
                data = None
            if data is None:
                continue
            primary_symbol_getter = getattr(data, "getPrimarySymbol", None)
            if callable(primary_symbol_getter):
                try:
                    data_symbol = primary_symbol_getter()
                except Exception:
                    data_symbol = None
                if data_symbol is not None:
                    try:
                        name = data_symbol.getName()
                    except Exception:
                        name = None
                    if name:
                        return name
        return None
    
    def _get_op_key(self, pcode_op) -> str:
        """PcodeOpの一意なキーを生成（同一seqnumの異なるopを区別）"""
        seq = pcode_op.getSeqnum()
        if seq:
            target = seq.getTarget()
            time = getattr(seq, "getTime", lambda: None)()
            order = seq.getOrder()
            obj_id = id(pcode_op)
            return f"{target}:t{time}:o{order}:{obj_id}"
        obj_id = id(pcode_op)
        return f"noseq:{pcode_op.hashCode()}:{pcode_op.getMnemonic()}:{obj_id}"

    def _get_stable_op_key(self, pcode_op) -> str:
        """
        PcodeOp の論理的な安定キーを返す。

        `id()` ベースのキーは同一論理 op を別ラッパーとして取得した場合に
        一致しないため、循環検出や自己参照判定には不向きである。
        その用途では seqnum / mnemonic / output storage を用いた安定キーを使う。
        """
        if pcode_op is None:
            return "null-op"

        seq = pcode_op.getSeqnum()
        output = None
        try:
            output = pcode_op.getOutput()
        except Exception:
            output = None

        output_key = "no-output"
        if output is not None:
            try:
                addr = output.getAddress()
                space = addr.getAddressSpace().getName() if addr is not None else "unknown"
                output_key = f"{space}:{output.getOffset()}:{output.getSize()}"
            except Exception:
                output_key = f"output:{output.hashCode()}"

        if seq:
            target = seq.getTarget()
            time = getattr(seq, "getTime", lambda: None)()
            order = seq.getOrder()
            if time is not None:
                return f"{target}:t{time}:{pcode_op.getMnemonic()}:{output_key}"
            return f"{target}:o{order}:{pcode_op.getMnemonic()}:{output_key}"

        try:
            return f"noseq:{pcode_op.hashCode()}:{pcode_op.getMnemonic()}:{output_key}"
        except Exception:
            return f"noseq:{pcode_op.getMnemonic()}:{output_key}"

    def _get_op_order_key(self, pcode_op) -> Optional[int]:
        """PcodeOp の単調順序キーを返す。"""
        seq = pcode_op.getSeqnum()
        if seq is None:
            return None
        target = seq.getTarget()
        return (target.getOffset() << 8) | seq.getOrder()
    
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
    
    def _get_storage_info_from_varnode(self, varnode) -> Optional[StorageInfo]:
        """VarnodeからStorageInfoを作成"""
        if varnode is None:
            return None
        
        try:
            addr = varnode.getAddress()
            space = addr.getAddressSpace()
            
            storage_info = StorageInfo(
                is_register=space.isRegisterSpace(),
                space_name=space.getName(),
                offset=varnode.getOffset(),
                size=varnode.getSize(),
                size_bits=varnode.getSize() * 8
            )
            
            if space.isRegisterSpace():
                # レジスタ情報を取得
                reg = self.program.getRegister(addr, varnode.getSize())
                if reg:
                    storage_info.register_name = reg.getName()
                    
                    # 親レジスタ情報
                    base_reg = reg.getBaseRegister()
                    if base_reg:
                        storage_info.base_register_name = base_reg.getName()
                        storage_info.base_register_offset = base_reg.getOffset()
                        storage_info.base_register_size = base_reg.getBitLength() // 8
                        storage_info.base_register_size_bits = base_reg.getBitLength()
                        
                        # 親レジスタ内でのビットオフセットを計算
                        # reg.getOffset()はレジスタのバイトオフセット
                        # base_reg.getOffset()は親レジスタのバイトオフセット
                        byte_offset_in_base = reg.getOffset() - base_reg.getOffset()
                        storage_info.bit_offset_in_base = byte_offset_in_base * 8
                    else:
                        # 親レジスタがない場合は自身が親
                        storage_info.base_register_name = reg.getName()
                        storage_info.base_register_offset = reg.getOffset()
                        storage_info.base_register_size = reg.getBitLength() // 8
                        storage_info.base_register_size_bits = reg.getBitLength()
                        storage_info.bit_offset_in_base = 0
            
            return storage_info
        except Exception as e:
            if self.debug:
                self._debug_print(f"  [Warning] Failed to get storage info: {e}")
            return None
    
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
            return Expression.constant(value, varnode.getSize())
        
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
                    
                    return Expression.parameter(
                        sym_name, param_idx, dtype, dtype_obj, varnode.getSize(),
                        storage_info=storage_info
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
                return Expression.variable(
                    name, size=varnode.getSize(),
                    storage_info=storage_info,
                    runtime_ref=runtime_ref,
                )
        
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
            if self._debug_available():
                self._debug_print(f"  -> Memory address: {addr}")
            return Expression.memory(
                Expression.constant(addr.getOffset(), 8),
                varnode.getSize()
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
        return Expression.unknown(f"untraced_{key.space}_0x{key.offset:x}")
    
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
                func_addr = inputs[0]
                target_ref = self.resolve_call_target_ref(
                    func_addr,
                    allow_containing=True,
                    allow_code_address=True,
                ) or CallTargetRef.unknown()
                func_name = target_ref.display_name()
                self.emit_unknown_event(
                    reason="call_out_of_scope",
                    varnode=pcode_op.getOutput(),
                    def_op=pcode_op,
                    depth=depth,
                    note=f"CALL target={func_name}",
                )
                return Expression.unknown(
                    f"call_out_of_scope:{func_name}",
                    runtime_ref=UnknownValueRef.out_of_scope_call(
                        reason="call_out_of_scope",
                        target_ref=target_ref,
                        display_hint=func_name,
                    ),
                )
            return Expression.unknown("call_no_target")

        # CALLIND
        if mnemonic == "CALLIND":
            if inputs:
                target_ref = self.resolve_call_target_ref(
                    inputs[0],
                    allow_containing=True,
                    allow_code_address=True,
                ) or CallTargetRef.unknown()
                target_name = target_ref.display_name()
                self.emit_unknown_event(
                    reason="callind_out_of_scope",
                    varnode=pcode_op.getOutput(),
                    def_op=pcode_op,
                    depth=depth,
                    note=f"CALLIND target={target_name}",
                )
                return Expression.unknown(
                    f"callind_out_of_scope:{target_name}",
                    runtime_ref=UnknownValueRef.out_of_scope_call(
                        reason="callind_out_of_scope",
                        target_ref=target_ref,
                        display_hint=target_name,
                    ),
                )
            return Expression.unknown("callind_no_target")
        
        # LOAD
        if mnemonic == "LOAD":
            if len(inputs) >= 2:
                addr = self.trace_varnode(inputs[1], depth, use_cache)
                output = pcode_op.getOutput()
                size = output.getSize() if output else 4
                return Expression.memory(
                    addr,
                    size,
                    read_order_key=self._get_op_order_key(pcode_op),
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
                mult = Expression.binary_op("INT_MULT", index, element_size)
                return Expression.binary_op("INT_ADD", base, mult)
            return Expression.unknown("ptradd_insufficient_inputs")
        
        # PTRSUB
        if mnemonic == "PTRSUB":
            if len(inputs) >= 2:
                base = self.trace_varnode(inputs[0], depth, use_cache)
                offset = self.trace_varnode(inputs[1], depth, use_cache)
                return Expression.binary_op("INT_ADD", base, offset)
            return Expression.unknown("ptrsub_insufficient_inputs")
        
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
        
        if inputs:
            traced_inputs = [self.trace_varnode(inp, depth, use_cache) for inp in inputs]
            if len(traced_inputs) == 1:
                return Expression.unary_op(mnemonic, traced_inputs[0])
            elif len(traced_inputs) == 2:
                return Expression.binary_op(mnemonic, traced_inputs[0], traced_inputs[1])
            else:
                return Expression.call(mnemonic, traced_inputs)

        return Expression.unknown(f"unhandled_{mnemonic}")

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

    def _get_function_name(self, addr_varnode) -> str:
        """関数アドレスから関数名を取得"""
        target_ref = self.resolve_call_target_ref(
            addr_varnode,
            allow_containing=True,
            allow_code_address=True,
        )
        if target_ref is None:
            return "UNKNOWN_FUNC"
        return target_ref.display_name()
    
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
