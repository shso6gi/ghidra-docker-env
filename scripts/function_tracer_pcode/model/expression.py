# -*- coding: utf-8 -*-
"""式の表現クラス（Python互換出力対応）"""

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import List, Optional, Any, Dict, Tuple, Set

from .storage import StorageInfo


class ExpressionType(Enum):
    """式の種類"""
    CONSTANT = auto()
    PARAMETER = auto()
    VARIABLE = auto()
    BINARY_OP = auto()
    UNARY_OP = auto()
    CALL = auto()
    MEMORY = auto()
    PHI = auto()
    UNKNOWN = auto()



class Expression:
    """
    式を表現するクラス（AST的な構造）
    """
    
    # クラス変数: 定数表示形式 ("dec", "hex", "auto")
    _constant_format: str = "dec"
    _hex_threshold: int = 256
    
    def __init__(
        self,
        expr_type: ExpressionType,
        value: Any = None,
        operator: Optional[str] = None,
        operands: Optional[List['Expression']] = None,
        size: int = 0,
        name: Optional[str] = None,
        data_type: Optional[str] = None,
        storage_info: Optional[StorageInfo] = None
    ):
        self.expr_type = expr_type
        self.value = value
        self.operator = operator
        self.operands = operands or []
        self.size = size
        self.name = name
        self.data_type = data_type
        self.storage_info = storage_info
    
    @classmethod
    def set_constant_format(cls, fmt: str, threshold: int = 256):
        """定数の表示形式を設定"""
        cls._constant_format = fmt
        cls._hex_threshold = threshold
    
    @classmethod
    def constant(cls, value: int, size: int = 4) -> 'Expression':
        return cls(expr_type=ExpressionType.CONSTANT, value=value, size=size)
    
    @classmethod
    def parameter(
        cls,
        name: str,
        index: int = -1,
        data_type: Optional[str] = None,
        size: int = 4,
        storage_info: Optional[StorageInfo] = None
    ) -> 'Expression':
        return cls(
            expr_type=ExpressionType.PARAMETER,
            name=name,
            value=index,
            data_type=data_type,
            size=size,
            storage_info=storage_info
        )
    
    @classmethod
    def variable(
        cls,
        name: str,
        data_type: Optional[str] = None,
        size: int = 4,
        storage_info: Optional[StorageInfo] = None
    ) -> 'Expression':
        return cls(
            expr_type=ExpressionType.VARIABLE,
            name=name,
            data_type=data_type,
            size=size,
            storage_info=storage_info
        )
    
    @classmethod
    def binary_op(cls, operator: str, left: 'Expression', right: 'Expression') -> 'Expression':
        """二項演算式を作成（サイズを適切に継承）"""
        if operator == "PIECE":
            # PIECE: output.size = input0.size + input1.size
            size = (left.size if left.size else 0) + (right.size if right.size else 0)
        elif operator == "SUBPIECE":
            # SUBPIECE: サイズは呼び出し元で設定される（pcode_tracerで出力Varnodeから取得）
            size = 0
        elif operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
            # シフト演算: 結果は第1オペランドと同じサイズ
            size = left.size if left.size else 0
        elif operator in ["INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", 
                          "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL",
                          "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL"]:
            # 比較演算: 結果は1バイト（ブール値）
            size = 1
        elif operator in ["BOOL_AND", "BOOL_OR", "BOOL_XOR"]:
            # 論理演算: 結果は1バイト
            size = 1
        else:
            # その他の二項演算: 大きい方のサイズ
            left_size = left.size if left.size else 0
            right_size = right.size if right.size else 0
            size = max(left_size, right_size)
        return cls(expr_type=ExpressionType.BINARY_OP, operator=operator, operands=[left, right], size=size)
    
    @classmethod
    def unary_op(cls, operator: str, operand: 'Expression') -> 'Expression':
        """単項演算式を作成"""
        # INT_ZEXT/INT_SEXTのサイズは呼び出し元で設定される（pcode_tracerで出力Varnodeから取得）
        return cls(expr_type=ExpressionType.UNARY_OP, operator=operator, operands=[operand], size=operand.size)
    
    @classmethod
    def call(cls, func_name: str, arguments: List['Expression']) -> 'Expression':
        return cls(expr_type=ExpressionType.CALL, name=func_name, operands=arguments)
    
    @classmethod
    def memory(cls, address: 'Expression', size: int = 4) -> 'Expression':
        return cls(expr_type=ExpressionType.MEMORY, operands=[address], size=size)
    
    @classmethod
    def phi(cls, branches: List[tuple]) -> 'Expression':
        """PHIノード（条件分岐による値の選択）を作成"""
        return cls(expr_type=ExpressionType.PHI, value=branches)
    
    @classmethod
    def unknown(cls, description: str = "unknown") -> 'Expression':
        return cls(expr_type=ExpressionType.UNKNOWN, name=description)
    
    def get_bit_width(self) -> int:
        """
        式のビット幅を取得
        
        Returns:
            int: ビット幅（ビット単位）
        """
        # サイズが明示的に設定されている場合
        if self.size and self.size > 0:
            return self.size * 8
        
        # 式の種類ごとにビット幅を推測
        if self.expr_type == ExpressionType.CONSTANT:
            # 定数のサイズが設定されていない場合のフォールバック
            return 32
        
        elif self.expr_type == ExpressionType.PARAMETER:
            return 32  # パラメータのデフォルト
        
        elif self.expr_type == ExpressionType.VARIABLE:
            return 32  # 変数のデフォルト
        
        elif self.expr_type == ExpressionType.BINARY_OP:
            if self.operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
                # シフト演算: 結果は第1オペランドと同じビット幅
                return self.operands[0].get_bit_width()
            elif self.operator == "PIECE":
                # PIECE: 両オペランドの合計
                return self.operands[0].get_bit_width() + self.operands[1].get_bit_width()
            elif self.operator == "SUBPIECE":
                # SUBPIECE: 出力サイズ（設定されているはず）
                return (self.size if self.size else 4) * 8
            elif self.operator in ["INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", 
                                   "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL",
                                   "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL"]:
                # 比較演算: 結果は1ビット（ブール値）
                return 1
            elif self.operator in ["BOOL_AND", "BOOL_OR", "BOOL_XOR"]:
                # 論理演算: 結果は1ビット
                return 1
            else:
                # その他の二項演算: 大きい方のビット幅
                left_bits = self.operands[0].get_bit_width()
                right_bits = self.operands[1].get_bit_width()
                return max(left_bits, right_bits)
        
        elif self.expr_type == ExpressionType.UNARY_OP:
            if self.operator in ["INT_ZEXT", "INT_SEXT"]:
                # 拡張演算: 出力サイズを使用（設定されているはず）
                return (self.size if self.size else 8) * 8
            elif self.operator in ["BOOL_NEGATE"]:
                return 1
            else:
                # その他の単項演算: オペランドと同じ
                return self.operands[0].get_bit_width()
        
        elif self.expr_type == ExpressionType.MEMORY:
            return (self.size if self.size else 4) * 8
        
        elif self.expr_type == ExpressionType.PHI:
            # PHI: 最初の値のビット幅
            if self.value and len(self.value) > 0:
                _, first_val = self.value[0]
                if hasattr(first_val, 'get_bit_width'):
                    return first_val.get_bit_width()
            return 32
        
        return 32  # フォールバック
    
    def _format_constant(self, value: int) -> str:
        """定数を指定された形式でフォーマット"""
        if value < 0:
            # 負の値
            if self._constant_format == "hex":
                return f"(-0x{abs(value):x})"
            return f"({value})"
        
        if self._constant_format == "hex":
            return f"0x{value:x}"
        elif self._constant_format == "auto":
            if value >= self._hex_threshold:
                return f"0x{value:x}"
            return str(value)
        else:  # dec
            return str(value)
    
    def to_string(self, simplify: bool = True) -> str:
        """式をPython互換の文字列に変換"""
        return self._to_string_internal(simplify)
    
    def _to_string_internal(self, simplify: bool) -> str:
        if self.expr_type == ExpressionType.CONSTANT:
            return self._format_constant(self.value)
        
        elif self.expr_type == ExpressionType.PARAMETER:
            return self.name if self.name else f"param_{self.value}"
        
        elif self.expr_type == ExpressionType.VARIABLE:
            return self.name if self.name else "var"
        
        elif self.expr_type == ExpressionType.BINARY_OP:
            left = self.operands[0]
            right = self.operands[1]
            left_str = left._to_string_internal(simplify)
            right_str = right._to_string_internal(simplify)
            
            # PIECE: 2つの値を結合（upper << (lower_bits) | lower）
            if self.operator == "PIECE":
                return self._format_piece(left, right, simplify)
            
            # SUBPIECE: 値の一部を抽出
            if self.operator == "SUBPIECE":
                return self._format_subpiece(left, right, simplify)
            
            op = self._get_python_operator(self.operator)
            return f"({left_str} {op} {right_str})"
        
        elif self.expr_type == ExpressionType.UNARY_OP:
            operand = self.operands[0]._to_string_internal(simplify)
            op = self._get_python_operator(self.operator)
            if op == "not":
                return f"(not {operand})"
            elif op in ("-", "~"):
                return f"({op}{operand})"
            else:
                return f"{op}({operand})"
        
        elif self.expr_type == ExpressionType.CALL:
            args = ", ".join(op._to_string_internal(simplify) for op in self.operands)
            return f"{self.name}({args})"
        
        elif self.expr_type == ExpressionType.MEMORY:
            addr = self.operands[0]._to_string_internal(simplify)
            return f"MEM[{addr}]"
        
        elif self.expr_type == ExpressionType.PHI:
            branches = self.value
            if not branches:
                return "UNKNOWN"
            if len(branches) == 1:
                _, val = branches[0]
                if hasattr(val, '_to_string_internal'):
                    return val._to_string_internal(simplify)
                return str(val)
            
            parts = []
            for cond, val in branches:
                if hasattr(val, '_to_string_internal'):
                    val_str = val._to_string_internal(simplify)
                else:
                    val_str = str(val)
                if cond is not None:
                    if hasattr(cond, '_to_string_internal'):
                        cond_str = cond._to_string_internal(simplify)
                    elif hasattr(cond, 'to_string'):
                        cond_str = cond.to_string()
                    else:
                        cond_str = str(cond)
                    parts.append(f"{val_str} if {cond_str}")
                else:
                    parts.append(val_str)
            return "PHI(" + ", ".join(parts) + ")"
        
        else:
            return self.name if self.name else "UNKNOWN"
    
    def _format_piece(self, high: 'Expression', low: 'Expression', simplify: bool) -> str:
        """
        PIECE を Python 互換形式に変換
        PIECE(high, low) = (high << (low_size * 8)) | low
        """
        high_str = high._to_string_internal(simplify)
        low_str = low._to_string_internal(simplify)
        
        # lowのビット幅からシフト量を計算
        shift_bits = low.get_bit_width()
        
        # 簡略化
        if simplify:
            # high が定数 0 の場合
            if high.expr_type == ExpressionType.CONSTANT and high.value == 0:
                return low_str
            
            # low が定数 0 の場合
            if low.expr_type == ExpressionType.CONSTANT and low.value == 0:
                return f"({high_str} << {shift_bits})"
        
        # 一般形式
        return f"(({high_str} << {shift_bits}) | {low_str})"
    
    def _format_subpiece(self, source: 'Expression', offset: 'Expression', simplify: bool) -> str:
        """
        SUBPIECE を Python 互換形式に変換
        SUBPIECE(source, byte_offset) = (source >> (byte_offset * 8)) & mask
        
        mask は出力サイズに基づく
        """
        source_str = source._to_string_internal(simplify)
        
        # オフセット値を取得
        if offset.expr_type == ExpressionType.CONSTANT:
            byte_offset = offset.value
        else:
            # 非定数オフセットの場合
            offset_str = offset._to_string_internal(simplify)
            output_bits = self.get_bit_width()
            mask = (1 << output_bits) - 1
            mask_str = self._format_constant(mask)
            return f"(({source_str} >> ({offset_str} * 8)) & {mask_str})"
        
        # 出力サイズからマスクを計算
        output_bits = self.get_bit_width()
        mask = (1 << output_bits) - 1
        mask_str = self._format_constant(mask)
        
        shift_bits = byte_offset * 8
        
        # 簡略化
        if simplify and shift_bits == 0:
            # オフセット0の場合はシフト不要
            return f"({source_str} & {mask_str})"
        
        # 一般形式
        return f"(({source_str} >> {shift_bits}) & {mask_str})"
    
    def _get_python_operator(self, operator: Optional[str]) -> str:
        """P-codeオペレータをPython演算子に変換"""
        if operator is None:
            return ""
        op_map: Dict[str, str] = {
            # 算術演算
            "INT_ADD": "+",
            "INT_SUB": "-",
            "INT_MULT": "*",
            "INT_DIV": "//",
            "INT_SDIV": "//",
            "INT_REM": "%",
            "INT_SREM": "%",
            # ビット演算
            "INT_AND": "&",
            "INT_OR": "|",
            "INT_XOR": "^",
            "INT_LEFT": "<<",
            "INT_RIGHT": ">>",
            "INT_SRIGHT": ">>",
            # 比較演算
            "INT_EQUAL": "==",
            "INT_NOTEQUAL": "!=",
            "INT_LESS": "<",
            "INT_SLESS": "<",
            "INT_LESSEQUAL": "<=",
            "INT_SLESSEQUAL": "<=",
            # 論理演算（Python形式）
            "BOOL_AND": "and",
            "BOOL_OR": "or",
            "BOOL_XOR": "^",
            # 単項演算
            "INT_NEGATE": "~",
            "INT_2COMP": "-",
            "BOOL_NEGATE": "not",
            "INT_ZEXT": "int",
            "INT_SEXT": "int",
            "COPY": "",
            # 浮動小数点
            "FLOAT_ADD": "+",
            "FLOAT_SUB": "-",
            "FLOAT_MULT": "*",
            "FLOAT_DIV": "/",
        }
        op: str = operator
        return op_map.get(op, op)
    
    def equals(self, other: 'Expression') -> bool:
        """式が等価かどうかを判定"""
        if not isinstance(other, Expression):
            return False
        if self.expr_type != other.expr_type:
            return False
        if self.operator != other.operator:
            return False
        if self.value != other.value:
            return False
        if self.name != other.name:
            return False
        if len(self.operands) != len(other.operands):
            return False
        for a, b in zip(self.operands, other.operands):
            if not a.equals(b):
                return False
        return True
    
    def to_smt(self) -> str:
        """SMTソルバー用の式に変換"""
        return self._to_smt_internal()
    
    def _to_smt_internal(self) -> str:
        if self.expr_type == ExpressionType.CONSTANT:
            bits = self.get_bit_width()
            # 負の値の処理（2の補数表現に変換）
            value = self.value
            if value < 0:
                value = value & ((1 << bits) - 1)
            return f"(_ bv{value} {bits})"
        
        elif self.expr_type == ExpressionType.PARAMETER:
            return self.name if self.name else f"param_{self.value}"
        
        elif self.expr_type == ExpressionType.VARIABLE:
            return self.name if self.name else "var"
        
        elif self.expr_type == ExpressionType.BINARY_OP:
            left = self.operands[0]
            right = self.operands[1]
            
            # PIECE -> concat
            if self.operator == "PIECE":
                left_smt = left._to_smt_internal()
                right_smt = right._to_smt_internal()
                return f"(concat {left_smt} {right_smt})"
            
            # SUBPIECE -> extract
            if self.operator == "SUBPIECE":
                source_smt = left._to_smt_internal()
                if right.expr_type == ExpressionType.CONSTANT:
                    byte_offset = right.value
                    output_size = self.size if self.size else 4
                    high_bit = (byte_offset + output_size) * 8 - 1
                    low_bit = byte_offset * 8
                    return f"((_ extract {high_bit} {low_bit}) {source_smt})"
                else:
                    return f"(subpiece {source_smt} {right._to_smt_internal()})"
            
            # ビット幅を取得
            left_bits = left.get_bit_width()
            right_bits = right.get_bit_width()
            
            left_smt = left._to_smt_internal()
            right_smt = right._to_smt_internal()
            
            # シフト演算: シフト量のビット幅を第1オペランドに合わせる
            if self.operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
                result_bits = left_bits
                if right_bits != result_bits:
                    if right_bits > result_bits:
                        # シフト量が大きい場合は下位ビットを抽出
                        right_smt = f"((_ extract {result_bits - 1} 0) {right_smt})"
                    else:
                        # シフト量が小さい場合はゼロ拡張
                        right_smt = f"((_ zero_extend {result_bits - right_bits}) {right_smt})"
                
                op = self._get_smt_operator(self.operator)
                return f"({op} {left_smt} {right_smt})"
            
            # ビット演算・算術演算: 両オペランドのビット幅を揃える
            if self.operator in ["INT_AND", "INT_OR", "INT_XOR", 
                                 "INT_ADD", "INT_SUB", "INT_MULT",
                                 "INT_DIV", "INT_SDIV", "INT_REM", "INT_SREM"]:
                if left_bits != right_bits:
                    target_bits = max(left_bits, right_bits)
                    if left_bits < target_bits:
                        left_smt = f"((_ zero_extend {target_bits - left_bits}) {left_smt})"
                    if right_bits < target_bits:
                        right_smt = f"((_ zero_extend {target_bits - right_bits}) {right_smt})"
                
                op = self._get_smt_operator(self.operator)
                return f"({op} {left_smt} {right_smt})"
            
            # 比較演算: 両オペランドのビット幅を揃える
            if self.operator in ["INT_EQUAL", "INT_NOTEQUAL", 
                                 "INT_LESS", "INT_SLESS", 
                                 "INT_LESSEQUAL", "INT_SLESSEQUAL"]:
                if left_bits != right_bits:
                    target_bits = max(left_bits, right_bits)
                    if left_bits < target_bits:
                        left_smt = f"((_ zero_extend {target_bits - left_bits}) {left_smt})"
                    if right_bits < target_bits:
                        right_smt = f"((_ zero_extend {target_bits - right_bits}) {right_smt})"
                
                op = self._get_smt_operator(self.operator)
                return f"({op} {left_smt} {right_smt})"
            
            # その他の二項演算（BOOL_AND, BOOL_OR など）
            op = self._get_smt_operator(self.operator)
            return f"({op} {left_smt} {right_smt})"
        
        elif self.expr_type == ExpressionType.UNARY_OP:
            operand = self.operands[0]
            operand_smt = operand._to_smt_internal()
            operand_bits = operand.get_bit_width()
            
            # INT_ZEXT: ゼロ拡張
            if self.operator == "INT_ZEXT":
                output_bits = (self.size if self.size else 8) * 8
                extend_bits = output_bits - operand_bits
                if extend_bits > 0:
                    return f"((_ zero_extend {extend_bits}) {operand_smt})"
                elif extend_bits == 0:
                    return operand_smt
                else:
                    # 入力より出力が小さい場合は抽出
                    return f"((_ extract {output_bits - 1} 0) {operand_smt})"
            
            # INT_SEXT: 符号拡張
            elif self.operator == "INT_SEXT":
                output_bits = (self.size if self.size else 8) * 8
                extend_bits = output_bits - operand_bits
                if extend_bits > 0:
                    return f"((_ sign_extend {extend_bits}) {operand_smt})"
                elif extend_bits == 0:
                    return operand_smt
                else:
                    return f"((_ extract {output_bits - 1} 0) {operand_smt})"
            
            # INT_NEGATE - ビット反転（1の補数）
            elif self.operator == "INT_NEGATE":
                return f"(bvnot {operand_smt})"
            
            # INT_2COMP - 算術否定（2の補数）
            elif self.operator == "INT_2COMP":
                return f"(bvneg {operand_smt})"
            
            # BOOL_NEGATE
            elif self.operator == "BOOL_NEGATE":
                return f"(not {operand_smt})"
            
            # その他の単項演算
            else:
                op = self._get_smt_operator(self.operator)
                return f"({op} {operand_smt})"
        
        elif self.expr_type == ExpressionType.CALL:
            args = " ".join(op._to_smt_internal() for op in self.operands)
            if args:
                return f"({self.name} {args})"
            else:
                return f"{self.name}"
        
        elif self.expr_type == ExpressionType.MEMORY:
            addr = self.operands[0]._to_smt_internal()
            return f"(select mem {addr})"
        
        elif self.expr_type == ExpressionType.PHI:
            branches = self.value
            if not branches:
                return "undefined"
            
            # 最後のブランチがデフォルト値
            last_val = branches[-1][1]
            if hasattr(last_val, '_to_smt_internal'):
                result = last_val._to_smt_internal()
            else:
                result = str(last_val)
            
            # 逆順にite式を構築
            for i in range(len(branches) - 2, -1, -1):
                cond, val = branches[i]
                if cond is not None and hasattr(cond, '_to_smt_internal'):
                    cond_str = cond._to_smt_internal()
                elif cond is not None and hasattr(cond, 'to_smt'):
                    cond_str = cond.to_smt()
                else:
                    cond_str = "true"
                
                if hasattr(val, '_to_smt_internal'):
                    val_str = val._to_smt_internal()
                else:
                    val_str = str(val)
                
                result = f"(ite {cond_str} {val_str} {result})"
            
            return result
        
        else:
            return "unknown"

    def _get_smt_operator(self, operator: Optional[str] = None) -> str:
        """P-codeオペレータをSMT-LIB演算子に変換"""
        if operator is None:
            return "unknown"

        op_map = {
            # 算術演算
            "INT_ADD": "bvadd",
            "INT_SUB": "bvsub",
            "INT_MULT": "bvmul",
            "INT_DIV": "bvudiv",
            "INT_SDIV": "bvsdiv",
            "INT_REM": "bvurem",
            "INT_SREM": "bvsrem",
            # ビット演算
            "INT_AND": "bvand",
            "INT_OR": "bvor",
            "INT_XOR": "bvxor",
            "INT_LEFT": "bvshl",
            "INT_RIGHT": "bvlshr",
            "INT_SRIGHT": "bvashr",
            # 比較演算
            "INT_EQUAL": "=",
            "INT_NOTEQUAL": "distinct",
            "INT_LESS": "bvult",
            "INT_SLESS": "bvslt",
            "INT_LESSEQUAL": "bvule",
            "INT_SLESSEQUAL": "bvsle",
            # 単項演算（特別処理済みのものは除外）
            "INT_NEGATE": "bvnot",
            "INT_2COMP": "bvneg",
            "BOOL_NEGATE": "not",
            # 論理演算
            "BOOL_AND": "and",
            "BOOL_OR": "or",
            "BOOL_XOR": "xor",
        }
        return op_map.get(operator, operator.lower())
    
    def to_dict(self) -> Dict[str, Any]:
        result: Dict[str, Any] = {"type": self.expr_type.name}
        if self.value is not None:
            result["value"] = self.value
        if self.operator:
            result["operator"] = self.operator
        if self.name:
            result["name"] = self.name
        if self.data_type:
            result["data_type"] = self.data_type
        if self.size:
            result["size"] = self.size
        if self.operands:
            result["operands"] = [op.to_dict() for op in self.operands]
        if self.storage_info:
            result["storage_info"] = self.storage_info.to_dict()
        return result
    
    def get_all_variables(self) -> Set[str]:
        """
        式に含まれる全ての変数名（パラメータ・変数）を取得
        
        Returns:
            変数名のセット
        """
        variables: Set[str] = set()
        self._collect_variables(variables)
        return variables
    
    def _collect_variables(self, variables: Set[str]) -> None:
        """再帰的に変数を収集"""
        if self.expr_type == ExpressionType.PARAMETER:
            if self.name:
                variables.add(self.name)
        
        elif self.expr_type == ExpressionType.VARIABLE:
            if self.name:
                variables.add(self.name)
        
        elif self.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP):
            for operand in self.operands:
                operand._collect_variables(variables)
        
        elif self.expr_type == ExpressionType.CALL:
            for operand in self.operands:
                operand._collect_variables(variables)
        
        elif self.expr_type == ExpressionType.MEMORY:
            for operand in self.operands:
                operand._collect_variables(variables)
        
        elif self.expr_type == ExpressionType.PHI:
            if self.value:
                for cond, val in self.value:
                    if cond is not None and hasattr(cond, '_collect_variables'):
                        cond._collect_variables(variables)
                    if hasattr(val, '_collect_variables'):
                        val._collect_variables(variables)
    
    def get_all_variables_with_storage(self) -> Dict[str, Optional['StorageInfo']]:
        """
        式に含まれる全ての変数名とストレージ情報を取得
        
        Returns:
            変数名 -> StorageInfo のマッピング
        """
        variables: Dict[str, Optional[StorageInfo]] = {}
        self._collect_variables_with_storage(variables)
        return variables
    
    def _collect_variables_with_storage(self, variables: Dict[str, Optional['StorageInfo']]) -> None:
        """再帰的に変数とストレージ情報を収集"""
        if self.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
            if self.name and self.name not in variables:
                variables[self.name] = self.storage_info
        
        elif self.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP):
            for operand in self.operands:
                operand._collect_variables_with_storage(variables)
        
        elif self.expr_type == ExpressionType.CALL:
            for operand in self.operands:
                operand._collect_variables_with_storage(variables)
        
        elif self.expr_type == ExpressionType.MEMORY:
            for operand in self.operands:
                operand._collect_variables_with_storage(variables)
        
        elif self.expr_type == ExpressionType.PHI:
            if self.value:
                for cond, val in self.value:
                    if cond is not None and hasattr(cond, '_collect_variables_with_storage'):
                        cond._collect_variables_with_storage(variables)
                    if hasattr(val, '_collect_variables_with_storage'):
                        val._collect_variables_with_storage(variables)


class Condition:
    """条件式を表現するクラス"""
    
    def __init__(self, expression: Expression, negated: bool = False):
        self.expression = expression
        self.negated = negated
    
    def negate(self) -> 'Condition':
        return Condition(self.expression, not self.negated)
    
    def to_string(self) -> str:
        expr_str = self.expression.to_string()
        if self.negated:
            return f"(not {expr_str})"
        return expr_str
    
    def to_smt(self) -> str:
        expr_smt = self.expression.to_smt()
        if self.negated:
            return f"(not {expr_smt})"
        return expr_smt
    
    def equals(self, other: 'Condition') -> bool:
        """条件が等価かどうかを判定"""
        if not isinstance(other, Condition):
            return False
        if self.negated != other.negated:
            return False
        return self.expression.to_string() == other.expression.to_string()
    
    @classmethod
    def combine_and(cls, conditions: List['Condition']) -> Optional['Condition']:
        """複数の条件をANDで結合（重複除去付き）"""
        if not conditions:
            return None
        
        unique = []
        for cond in conditions:
            is_dup = False
            for existing in unique:
                if cond.equals(existing):
                    is_dup = True
                    break
            if not is_dup:
                unique.append(cond)
        
        if len(unique) == 0:
            return None
        if len(unique) == 1:
            return unique[0]
        
        def to_expr(c: Condition) -> Expression:
            if c.negated:
                return Expression.unary_op("BOOL_NEGATE", c.expression)
            return c.expression
        
        combined = Expression.binary_op("BOOL_AND", to_expr(unique[0]), to_expr(unique[1]))
        for cond in unique[2:]:
            combined = Expression.binary_op("BOOL_AND", combined, to_expr(cond))
        
        return Condition(combined, False)
    
    def get_all_variables(self) -> Set[str]:
        """条件式に含まれる全ての変数名を取得"""
        return self.expression.get_all_variables()
    
    def get_all_variables_with_storage(self) -> Dict[str, Optional[StorageInfo]]:
        """条件式に含まれる全ての変数名とストレージ情報を取得"""
        return self.expression.get_all_variables_with_storage()
    
    def to_dict(self) -> Dict[str, Any]:
        """辞書形式に変換"""
        return {
            "expression": self.expression.to_dict(),
            "negated": self.negated,
        }