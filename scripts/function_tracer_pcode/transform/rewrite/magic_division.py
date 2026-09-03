# -*- coding: utf-8 -*-
"""
Magic number計算（除算の最適化）

参考文献:
- Hacker's Delight, Second Edition, Chapter 10
- "Division by Invariant Integers using Multiplication"
  by Torbjörn Granlund and Peter L. Montgomery

BV意味論で厳密に等価な変換のみを提供
"""



def is_power_of_two(n: int) -> bool:
    """nが2の累乗かチェック（正の整数のみ）"""
    return n > 0 and (n & (n - 1)) == 0


def log2_exact(n: int) -> int:
    """2の累乗nに対してkを返す（n = 2^k）"""
    assert is_power_of_two(n)
    return (n - 1).bit_length()


class MagicDivisionCalculator:
    """Magic number計算（BV厳密版）"""
    
class MagicConstants:
    """事前計算されたmagic number定数（/3専用）"""
    
    # 64-bit signed division by 3
    # m = 0x5555555555555556 (2の補数表現)
    # unsigned表現: 6148914691236517206 (ログの値と一致)
    SIGNED_64_DIV_3 = {
        'multiplier': 0x5555555555555556,
        'multiplier_unsigned': 6148914691236517206,
        'shift': 0,
        'needs_sign_correction': True
    }
    
    # 32-bit signed division by 3
    SIGNED_32_DIV_3 = {
        'multiplier': 0x55555556,
        'multiplier_unsigned': 1431655766,
        'shift': 0,
        'needs_sign_correction': True
    }