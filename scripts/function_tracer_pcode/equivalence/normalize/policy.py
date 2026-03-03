# -*- coding: utf-8 -*-
"""正規化ポリシー（MIN除外制約の解析など）"""

from typing import Set, List
import re


def extract_min_excluded_params(
    smt_lines: List[str],
    bit_width: int = 64,
    debug: bool = False
) -> Set[str]:
    """
    SMT制約から MIN除外制約を持つパラメータを抽出
    
    パターン:
        (assert (not (= param_name (_ bv9223372036854775808 64))))
        (assert (distinct param_name (_ bv9223372036854775808 64)))
    
    Args:
        smt_lines: SMT制約行のリスト
        bit_width: ビット幅（デフォルト: 64）
        debug: デバッグ出力
    
    Returns:
        MIN除外制約を持つパラメータ名のセット
    """
    excluded = set()
    
    # MIN値を計算
    if bit_width == 64:
        min_value = 2**63  # INT64_MIN (符号なし表現)
    elif bit_width == 32:
        min_value = 2**31  # INT32_MIN
    else:
        # 他のビット幅は未対応
        return excluded
    
    # パターン: (assert (not (= PARAM (_ bvMIN WIDTH))))
    # または: (assert (distinct PARAM (_ bvMIN WIDTH)))
    pattern1 = re.compile(
        r'\(assert\s+\(not\s+\(=\s+(\w+)\s+\(_\s+bv' + str(min_value) + r'\s+' + str(bit_width) + r'\)\)\)\)'
    )
    pattern2 = re.compile(
        r'\(assert\s+\(distinct\s+(\w+)\s+\(_\s+bv' + str(min_value) + r'\s+' + str(bit_width) + r'\)\)\)'
    )
    
    for line in smt_lines:
        match1 = pattern1.search(line)
        if match1:
            param_name = match1.group(1)
            excluded.add(param_name)
            if debug:
                print(f"[Policy] MIN excluded: {param_name} (pattern: not =)")
            continue
        
        match2 = pattern2.search(line)
        if match2:
            param_name = match2.group(1)
            excluded.add(param_name)
            if debug:
                print(f"[Policy] MIN excluded: {param_name} (pattern: distinct)")
    
    return excluded