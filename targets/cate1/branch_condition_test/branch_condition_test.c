/*
 * branch_condition_test.c - 条件分岐の動作テスト
 * 目的：等価性判定プログラム向けに、比較演算・短絡評価・switch・
 *       ループ内分岐などの条件分岐パターンを網羅的に確認する
 */

#include <stdint.h>

volatile int branch_probe = 0;

// ============================================================
// パターン1: 基本的な比較演算
// ============================================================

int branch_eq(int a, int b) {
    if (a == b) {
        return 11;
    }
    return -11;
}

int branch_ne(int a, int b) {
    if (a != b) {
        return 13;
    }
    return -13;
}

int branch_lt(int a, int b) {
    if (a < b) {
        return a - b;
    }
    return b - a;
}

int branch_le(int a, int b) {
    if (a <= b) {
        return a + 2;
    }
    return b + 3;
}

int branch_gt(int a, int b) {
    if (a > b) {
        return a * 2;
    }
    return b * 2;
}

int branch_ge(int a, int b) {
    if (a >= b) {
        return a - 5;
    }
    return b - 7;
}

// ============================================================
// パターン2: 0判定・真偽値化
// ============================================================

int branch_zero(int value) {
    if (value == 0) {
        return 100;
    }
    return value;
}

int branch_nonzero(int value) {
    if (value) {
        return value + 1;
    }
    return -100;
}

int branch_not(int value) {
    if (!value) {
        return 77;
    }
    return -77;
}

// ============================================================
// パターン3: 範囲チェックと境界値
// ============================================================

int branch_closed_range(int value, int low, int high) {
    if (value >= low && value <= high) {
        return value;
    }
    return -1;
}

int branch_half_open_range(int value, int low, int high) {
    if (value >= low && value < high) {
        return value + 10;
    }
    return -10;
}

int branch_disjoint_range(int value) {
    if (value < -100 || value > 100) {
        return 1;
    }
    return 0;
}

// ============================================================
// パターン4: 符号付き・符号なし比較
// ============================================================

int branch_signed_compare(int a, int b) {
    if (a < 0 && b >= 0) {
        return a + b;
    }
    if (a >= 0 && b < 0) {
        return a - b;
    }
    return a ^ b;
}

unsigned int branch_unsigned_compare(unsigned int a, unsigned int b) {
    if (a < b) {
        return b - a;
    }
    if (a > b) {
        return a - b;
    }
    return 0;
}

int branch_signed_unsigned_mix(int a, unsigned int b) {
    if (a < 0) {
        return -1;
    }
    if ((unsigned int)a < b) {
        return (int)(b - (unsigned int)a);
    }
    return a;
}

// ============================================================
// パターン5: 短絡評価と副作用
// ============================================================

int record_and_return(int marker, int value) {
    branch_probe += marker;
    return value;
}

int branch_short_circuit_and(int a, int b, int c) {
    if (record_and_return(1, a > 0) &&
        record_and_return(10, b > 0) &&
        record_and_return(100, c > 0)) {
        return 1;
    }
    return 0;
}

int branch_short_circuit_or(int a, int b, int c) {
    if (record_and_return(2, a < 0) ||
        record_and_return(20, b < 0) ||
        record_and_return(200, c < 0)) {
        return -1;
    }
    return 1;
}

int branch_nested_boolean(int a, int b, int c, int d) {
    if ((a > b && c > d) || (a == d && b != c)) {
        return a + c;
    }
    return b + d;
}

// ============================================================
// パターン6: if-else if 連鎖
// ============================================================

int branch_sign_bucket(int value) {
    if (value < -100) {
        return -3;
    } else if (value < 0) {
        return -2;
    } else if (value == 0) {
        return 0;
    } else if (value <= 100) {
        return 2;
    }
    return 3;
}

int branch_priority_select(int flags) {
    if (flags & 0x1) {
        return 10;
    } else if (flags & 0x2) {
        return 20;
    } else if (flags & 0x4) {
        return 40;
    }
    return 80;
}

// ============================================================
// パターン7: ネストした分岐
// ============================================================

int branch_nested_if(int a, int b, int c) {
    if (a > 0) {
        if (b > 0) {
            return c > 0 ? 111 : 112;
        }
        return c > 0 ? 121 : 122;
    }
    if (b > 0) {
        return c > 0 ? 211 : 212;
    }
    return c > 0 ? 221 : 222;
}

int branch_guard_clauses(int a, int b, int c) {
    if (a == 0) return -10;
    if (b == 0) return -20;
    if (c == 0) return -30;
    return a + b + c;
}

// ============================================================
// パターン8: 条件演算子
// ============================================================

int branch_ternary_basic(int a, int b) {
    return (a > b) ? a : b;
}

int branch_ternary_nested(int a, int b, int c) {
    return (a > b) ? ((a > c) ? a : c) : ((b > c) ? b : c);
}

int branch_ternary_with_side_effect(int a, int b) {
    int selected = (a & 1) ? record_and_return(3, a) : record_and_return(30, b);
    return selected + 5;
}

// ============================================================
// パターン9: switch分岐
// ============================================================

int branch_switch_dense(int value) {
    switch (value) {
        case 0:
            return 1000;
        case 1:
            return 1001;
        case 2:
            return 1002;
        case 3:
            return 1003;
        default:
            return -1000;
    }
}

int branch_switch_sparse(int value) {
    switch (value) {
        case -7:
            return 7;
        case 10:
            return 10;
        case 100:
            return 100;
        case 1024:
            return 1024;
        default:
            return -7;
    }
}

int branch_switch_fallthrough(int value) {
    switch (value) {
        case 0:
        case 1:
            return 1;
        case 2:
        case 3:
            return 2;
        default:
            return 9;
    }
}

// ============================================================
// パターン10: ループ内分岐
// ============================================================

int branch_for_accumulate(int limit) {
    int sum = 0;
    for (int i = 0; i < limit; i++) {
        if ((i & 1) == 0) {
            sum += i;
        } else {
            sum -= i;
        }
    }
    return sum;
}

int branch_continue_break(int limit, int stop_value) {
    int sum = 0;
    for (int i = 0; i < limit; i++) {
        if (i == stop_value) {
            break;
        }
        if (i % 3 == 0) {
            continue;
        }
        sum += i;
    }
    return sum;
}

int branch_while_state(int start) {
    int value = start;
    int steps = 0;
    while (value > 0) {
        if (value & 1) {
            value -= 3;
        } else {
            value >>= 1;
        }
        steps++;
    }
    return steps;
}

int branch_do_while(int start) {
    int value = start;
    int count = 0;
    do {
        count++;
        value -= (value > 5) ? 4 : 2;
    } while (value > 0);
    return count;
}

// ============================================================
// パターン11: ポインタ・配列を使う条件分岐
// ============================================================

int branch_pointer_check(const int *ptr) {
    if (ptr == 0) {
        return -999;
    }
    if (*ptr > 0) {
        return *ptr;
    }
    return -*ptr;
}

int branch_array_scan(const int *values, int size, int threshold) {
    int hits = 0;
    for (int i = 0; i < size; i++) {
        if (values[i] > threshold) {
            hits++;
        }
    }
    return hits;
}

// ============================================================
// パターン12: ビット条件・マスク判定
// ============================================================

int branch_bitmask(int flags) {
    if ((flags & 0x5) == 0x5) {
        return 5;
    }
    if (flags & 0x8) {
        return 8;
    }
    return 0;
}

int branch_shift_sign(int value) {
    if ((value >> 31) & 1) {
        return -1;
    }
    return 1;
}

// ============================================================
// パターン13: 条件に算術結果を使う
// ============================================================

int branch_difference_check(int a, int b) {
    int diff = a - b;
    if (diff == 0) {
        return 0;
    }
    if (diff < 0) {
        return -diff;
    }
    return diff;
}

int branch_sum_parity(int a, int b, int c) {
    int sum = a + b + c;
    if ((sum % 2) == 0) {
        return sum / 2;
    }
    return sum * 3 + 1;
}

// ============================================================
// パターン14: 複合条件の早期return
// ============================================================

int branch_multi_guard(int a, int b, int c, int d) {
    if (a < 0 || b < 0) return -1;
    if (c == 0 || d == 0) return -2;
    if (a + b > c + d) return 1;
    return 2;
}

// ============================================================
// パターン15: mainからまとめて呼び出し
// ============================================================

int main(void) {
    int values[] = { -5, 0, 7, 12, 101, -200, 33 };
    int x = 42;
    int y = -7;
    int z = 0;
    unsigned int ux = 12U;
    unsigned int uy = 4000000000U;
    int result = 0;

    result += branch_eq(x, 42);
    result += branch_ne(x, y);
    result += branch_lt(y, x);
    result += branch_le(z, x);
    result += branch_gt(x, y);
    result += branch_ge(x, x);

    result += branch_zero(z);
    result += branch_nonzero(x);
    result += branch_not(z);

    result += branch_closed_range(7, 0, 10);
    result += branch_half_open_range(10, 0, 10);
    result += branch_disjoint_range(-200);

    result += branch_signed_compare(y, x);
    result += (int)branch_unsigned_compare(ux, uy);
    result += branch_signed_unsigned_mix(x, uy);

    result += branch_short_circuit_and(1, 2, -3);
    result += branch_short_circuit_or(5, -1, 9);
    result += branch_nested_boolean(3, 1, 8, 2);

    result += branch_sign_bucket(-50);
    result += branch_priority_select(0x4);

    result += branch_nested_if(1, -1, 3);
    result += branch_guard_clauses(1, 2, 3);

    result += branch_ternary_basic(x, y);
    result += branch_ternary_nested(3, 9, 4);
    result += branch_ternary_with_side_effect(5, 8);

    result += branch_switch_dense(2);
    result += branch_switch_sparse(1024);
    result += branch_switch_fallthrough(1);

    result += branch_for_accumulate(10);
    result += branch_continue_break(12, 8);
    result += branch_while_state(19);
    result += branch_do_while(9);

    result += branch_pointer_check(&x);
    result += branch_pointer_check(0);
    result += branch_array_scan(values, 7, 10);

    result += branch_bitmask(0xD);
    result += branch_shift_sign(y);

    result += branch_difference_check(x, y);
    result += branch_sum_parity(3, 4, 5);

    result += branch_multi_guard(1, 2, 3, 4);

    result += branch_probe;
    return result & 0xFF;
}
