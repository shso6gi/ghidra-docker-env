# -*- coding: utf-8 -*-
"""除算最適化ルール

Magic number変換、power-of-two最適化、剰余最適化を含む
"""

from typing import TYPE_CHECKING
from .base import RewriteRule
from ..magic_division import MagicConstants, is_power_of_two, log2_exact

if TYPE_CHECKING:
    from ....model import Expression


class DivByConstantRuleBase(RewriteRule):
    """定数除算リライトの基底クラス"""
    
    def __init__(self, name: str, description: str, signed: bool):
        super().__init__(name, description)
        self.signed = signed
        self.div_ops = frozenset(["INT_SDIV", "SDIV"]) if signed else frozenset(["INT_DIV", "DIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ....model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        divisor = right.value
        
        if divisor == 0:
            return False
        if divisor == 1 or divisor == -1:
            return False
        
        return True
    
class SignedDivBy3Rule(RewriteRule):
    """
    signed除算 x sdiv 3 のmagic number変換
    
    アルゴリズム（clangと同一）:
        mulhi = upper64(sign_extend(x, 128) * sign_extend(m, 128))
        result = mulhi - (mulhi >> 63)
    
    where:
        m = 0x5555555555555556 (magic multiplier for /3)
    
    BV意味論の厳密性:
        - mulhi抽出は SUBPIECE で厳密に実装
        - 符号補正 (mulhi >> 63) は負数の丸め補正
        - clangが生成するコードと完全一致
    """
    
    def __init__(self):
        super().__init__(
            "sdiv_by_3_magic",
            "Convert x sdiv 3 to magic multiplication (clang-compatible)"
        )
        self.div_ops = frozenset(["INT_SDIV", "SDIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ....model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        return right.value == 3
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        x = expr.operands[0]
        n_bits = x.get_bit_width()
        n_bytes = x.size
        
        if n_bits == 64:
            magic_info = MagicConstants.SIGNED_64_DIV_3
        elif n_bits == 32:
            magic_info = MagicConstants.SIGNED_32_DIV_3
        else:
            return expr
        
        m_unsigned = magic_info['multiplier_unsigned']
        m_const = Expression.constant(m_unsigned, size=n_bytes)
        
        # mulhi の計算
        x_ext = Expression.unary_op("INT_SEXT", x)
        x_ext.size = n_bytes * 2
        
        m_ext = Expression.unary_op("INT_SEXT", m_const)
        m_ext.size = n_bytes * 2
        
        prod = Expression.binary_op("INT_MULT", x_ext, m_ext)
        prod.size = n_bytes * 2
        
        offset = Expression.constant(n_bytes, size=n_bytes)
        mulhi = Expression.binary_op("SUBPIECE", prod, offset)
        mulhi.size = n_bytes
        
        # 符号補正
        sign_shift = Expression.constant(n_bits - 1, size=n_bytes)
        sign_correction = Expression.binary_op("INT_SRIGHT", mulhi, sign_shift)
        sign_correction.size = n_bytes
        
        result = Expression.binary_op("INT_SUB", mulhi, sign_correction)
        result.size = n_bytes
        
        return result


class UnsignedDivBy3Rule(RewriteRule):
    """
    unsigned除算 x udiv 3 のmagic number変換
    
    アルゴリズム:
        mulhi = upper64(zero_extend(x, 128) * zero_extend(m, 128))
        result = mulhi >> 1
    
    where:
        m = 0xAAAAAAAAAAAAAAAB, shift = 1
    """
    
    def __init__(self):
        super().__init__(
            "udiv_by_3_magic",
            "Convert x udiv 3 to magic multiplication"
        )
        self.div_ops = frozenset(["INT_DIV", "DIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ....model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        return right.value == 3
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        x = expr.operands[0]
        n_bits = x.get_bit_width()
        n_bytes = x.size
        
        if n_bits == 64:
            m_value = 0xAAAAAAAAAAAAAAAB
            shift = 1
        elif n_bits == 32:
            m_value = 0xAAAAAAAB
            shift = 1
        else:
            return expr
        
        m_const = Expression.constant(m_value, size=n_bytes)
        
        x_ext = Expression.unary_op("INT_ZEXT", x)
        x_ext.size = n_bytes * 2
        
        m_ext = Expression.unary_op("INT_ZEXT", m_const)
        m_ext.size = n_bytes * 2
        
        prod = Expression.binary_op("INT_MULT", x_ext, m_ext)
        prod.size = n_bytes * 2
        
        offset = Expression.constant(n_bytes, size=n_bytes)
        mulhi = Expression.binary_op("SUBPIECE", prod, offset)
        mulhi.size = n_bytes
        
        if shift > 0:
            shift_amount = Expression.constant(shift, size=n_bytes)
            result = Expression.binary_op("INT_RIGHT", mulhi, shift_amount)
            result.size = n_bytes
        else:
            result = mulhi
        
        return result


class DivByPowerOfTwoUnsignedRule(DivByConstantRuleBase):
    """
    unsigned除算 x / 2^k → x >> k
    
    厳密性: logical shiftは常に正しい
    """
    
    def __init__(self):
        super().__init__(
            "div_pow2_unsigned",
            "Convert x / 2^k to x >> k (unsigned)",
            signed=False
        )
        self.signed = False
        self.div_ops = frozenset(["INT_DIV", "DIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        if not super().matches(expr):
            return False
        
        divisor = expr.operands[1].value
        return is_power_of_two(divisor)
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        k = log2_exact(divisor)
        
        shift_amount = Expression.constant(k, size=x.size)
        result = Expression.binary_op("INT_RIGHT", x, shift_amount)
        result.size = x.size
        
        return result


class DivByPowerOfTwoSignedRule(DivByConstantRuleBase):
    """
    signed除算 x sdiv 2^k → (x + bias) >> k
    
    bias = (x >> (n-1)) & (2^k - 1)
    
    これはround-to-zeroを実現する標準的な変換
    """
    
    def __init__(self):
        super().__init__(
            "div_pow2_signed",
            "Convert x sdiv 2^k to (x + bias) >> k (signed)",
            signed=False
        )
        self.signed = True
        self.div_ops = frozenset(["INT_SDIV", "SDIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        if not super().matches(expr):
            return False
        
        divisor = expr.operands[1].value
        return is_power_of_two(abs(divisor))
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        n_bits = x.get_bit_width()
        
        if divisor < 0:
            k = log2_exact(abs(divisor))
            
            sign_shift = Expression.constant(n_bits - 1, size=x.size)
            sign_bit_ext = Expression.binary_op("INT_SRIGHT", x, sign_shift)
            sign_bit_ext.size = x.size
            
            mask = Expression.constant((1 << k) - 1, size=x.size)
            bias = Expression.binary_op("INT_AND", sign_bit_ext, mask)
            bias.size = x.size
            
            x_plus_bias = Expression.binary_op("INT_ADD", x, bias)
            x_plus_bias.size = x.size
            
            shift_amount = Expression.constant(k, size=x.size)
            shifted = Expression.binary_op("INT_SRIGHT", x_plus_bias, shift_amount)
            shifted.size = x.size
            
            result = Expression.unary_op("INT_2COMP", shifted)
            result.size = x.size
            
            return result
        
        else:
            k = log2_exact(divisor)
            
            sign_shift = Expression.constant(n_bits - 1, size=x.size)
            sign_bit_ext = Expression.binary_op("INT_SRIGHT", x, sign_shift)
            sign_bit_ext.size = x.size
            
            mask = Expression.constant((1 << k) - 1, size=x.size)
            bias = Expression.binary_op("INT_AND", sign_bit_ext, mask)
            bias.size = x.size
            
            x_plus_bias = Expression.binary_op("INT_ADD", x, bias)
            x_plus_bias.size = x.size
            
            shift_amount = Expression.constant(k, size=x.size)
            result = Expression.binary_op("INT_SRIGHT", x_plus_bias, shift_amount)
            result.size = x.size
            
            return result


class RemByPowerOfTwoUnsignedRule(RewriteRule):
    """
    unsigned余り x % 2^k → x & (2^k - 1)
    """
    
    def __init__(self):
        super().__init__(
            "rem_pow2_unsigned",
            "Convert x % 2^k to x & (2^k - 1) (unsigned)"
        )
        self.rem_ops = frozenset(["INT_REM", "REM"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ....model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.rem_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        divisor = right.value
        if divisor <= 0:
            return False
        
        return is_power_of_two(divisor)
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        
        mask = Expression.constant(divisor - 1, size=x.size)
        result = Expression.binary_op("INT_AND", x, mask)
        result.size = x.size
        
        return result


class RemByPowerOfTwoSignedRule(RewriteRule):
    """
    signed余り x srem 2^k の変換
    
    srem は x - (x sdiv d) * d で定義される
    x sdiv 2^k は既に他のルールで変換されるので、
    ここでは展開形に戻してから除算を置換
    """
    
    def __init__(self):
        super().__init__(
            "rem_pow2_signed",
            "Convert x srem 2^k using expansion (signed)"
        )
        self.rem_ops = frozenset(["INT_SREM", "SREM"])
    
    def matches(self, expr: 'Expression') -> bool:
        from ....model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.rem_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        divisor = right.value
        if divisor == 0:
            return False
        
        return is_power_of_two(abs(divisor))
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        x = expr.operands[0]
        d = expr.operands[1]
        
        div_expr = Expression.binary_op("INT_SDIV", x, d)
        div_expr.size = x.size
        
        mult_expr = Expression.binary_op("INT_MULT", div_expr, d)
        mult_expr.size = x.size
        
        result = Expression.binary_op("INT_SUB", x, mult_expr)
        result.size = x.size
        
        return result