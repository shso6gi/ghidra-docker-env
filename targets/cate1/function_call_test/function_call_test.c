/*
 * function_call_test.c - 関数呼び出しの動作テスト
 * 目的：関数等価性判定プログラム向けに、通常呼び出し・条件分岐・
 *       long演算・副作用・再帰・間接呼び出しを含む典型パターンを観察する
 */

#include <stdint.h>

volatile int function_call_probe = 0;

typedef struct {
    int total;
    int count;
} call_stats;

// ============================================================
// パターン1: 基本的な葉関数とラッパー関数
// ============================================================

int fc_add(int a, int b) {
    return a + b;
}

int fc_sub(int a, int b) {
    return a - b;
}

int fc_bias(int value, int bias) {
    return value + bias;
}

int fc_scale(int value, int scale) {
    return value * scale;
}

int fc_wrap_add_then_bias(int a, int b, int bias) {
    return fc_bias(fc_add(a, b), bias);
}

int fc_wrap_scaled_delta(int a, int b) {
    return fc_scale(fc_sub(a, b), 3);
}

// ============================================================
// パターン2: 等価になりやすい呼び出しチェーン
// ============================================================

int fc_equiv_direct(int a, int b) {
    return a + b + 5;
}

int fc_equiv_call_chain(int a, int b) {
    return fc_bias(fc_add(a, b), 5);
}

int fc_equiv_two_stage(int a, int b) {
    int sum = fc_add(a, b);
    return fc_add(sum, 5);
}

int fc_nonequiv_near_miss(int a, int b) {
    return fc_bias(fc_sub(a, b), 5);
}

// ============================================================
// パターン3: 条件分岐で呼び先が変化
// ============================================================

int fc_select_simple(int a, int b, int choose_add) {
    if (choose_add) {
        return fc_add(a, b);
    }
    return fc_sub(a, b);
}

int fc_branch_chain(int a, int b, int c) {
    int mid;

    if (a > b) {
        mid = fc_wrap_add_then_bias(a, b, 1);
    } else if (c < 0) {
        mid = fc_wrap_scaled_delta(b, a);
    } else {
        mid = fc_bias(c, -3);
    }

    if (mid > 20) {
        return fc_scale(mid, 2);
    }
    return fc_sub(mid, 7);
}

int fc_guarded_call(int value, int divisor) {
    if (divisor == 0) {
        return -100;
    }
    if (value < 0) {
        return fc_sub(0, value / divisor);
    }
    return fc_add(value / divisor, divisor);
}

// ============================================================
// パターン4: long型の戻り値・型拡張を伴う呼び出し
// ============================================================

long fc_long_div(long a, long b) {
    if (b == 0) {
        return 0;
    }
    return a / b;
}

long fc_long_mod(long a, long b) {
    if (b == 0) {
        return 0;
    }
    return a % b;
}

long fc_long_divmod_mix(long a, long b) {
    long quotient;
    long remainder;

    if (b == 0) {
        return 0;
    }

    quotient = fc_long_div(a, b);
    remainder = fc_long_mod(a, b);
    return quotient * 100 + remainder;
}

int fc_widen_then_bias(int32_t a, int32_t b, int bias) {
    int64_t widened;

    if (b == 0) {
        return bias;
    }

    widened = (int64_t)a / (int64_t)b;
    return (int)widened + bias;
}

long fc_long_branch_dispatch(long a, long b, int use_mod) {
    if (use_mod) {
        return fc_long_mod(a, b);
    }
    return fc_long_div(a, b);
}

// ============================================================
// パターン5: void関数の副作用を経由した値観測
// ============================================================

void fc_store_sum(call_stats *stats, int a, int b) {
    if (stats == 0) {
        return;
    }
    stats->total = fc_add(a, b);
    stats->count += 1;
}

void fc_accumulate_delta(call_stats *stats, int delta) {
    if (stats == 0) {
        return;
    }
    stats->total = fc_add(stats->total, delta);
    stats->count += 1;
}

int fc_read_after_void(call_stats *stats, int a, int b, int delta) {
    if (stats == 0) {
        return -200;
    }
    fc_store_sum(stats, a, b);
    fc_accumulate_delta(stats, delta);
    return stats->total + stats->count;
}

// ============================================================
// パターン6: 再帰と相互呼び出し
// ============================================================

int fc_recursive_sum(int n) {
    if (n <= 0) {
        return 0;
    }
    return n + fc_recursive_sum(n - 1);
}

int fc_is_odd(int n);

int fc_is_even(int n) {
    if (n == 0) {
        return 1;
    }
    if (n < 0) {
        return fc_is_even(-n);
    }
    return fc_is_odd(n - 1);
}

int fc_is_odd(int n) {
    if (n == 0) {
        return 0;
    }
    if (n < 0) {
        return fc_is_odd(-n);
    }
    return fc_is_even(n - 1);
}

// ============================================================
// パターン7: 関数ポインタ経由の間接呼び出し
// ============================================================

int fc_op_add(int a, int b) {
    return a + b;
}

int fc_op_mul(int a, int b) {
    return a * b;
}

int fc_apply_indirect(int (*op)(int, int), int a, int b) {
    if (op == 0) {
        return -300;
    }
    return op(a, b);
}

int fc_dispatch_indirect(int mode, int a, int b) {
    int (*op)(int, int) = fc_op_add;

    if (mode & 1) {
        op = fc_op_mul;
    }
    return fc_apply_indirect(op, a, b);
}

// ============================================================
// パターン8: 呼び出しとグローバル副作用の観測
// ============================================================

int fc_record(int marker, int value) {
    function_call_probe += marker;
    return value;
}

int fc_recorded_chain(int a, int b, int c) {
    int left = fc_record(1, fc_add(a, b));
    int middle = fc_record(10, fc_scale(c, 2));
    int combined = fc_add(left, middle);

    return fc_record(100, combined);
}

int fc_recorded_branch(int value) {
    if (value > 0) {
        return fc_record(1000, fc_bias(value, 7));
    }
    return fc_record(2000, fc_sub(0, value));
}

// ============================================================
// パターン9: main からまとめて呼び出し
// ============================================================

int main(void) {
    call_stats stats = { 0, 0 };
    int result = 0;
    long long_result = 0;

    result += fc_wrap_add_then_bias(4, 8, 3);
    result += fc_wrap_scaled_delta(20, 5);

    result += fc_equiv_direct(6, 9);
    result += fc_equiv_call_chain(6, 9);
    result += fc_equiv_two_stage(6, 9);
    result += fc_nonequiv_near_miss(6, 9);

    result += fc_select_simple(10, 3, 1);
    result += fc_select_simple(10, 3, 0);
    result += fc_branch_chain(9, 4, 2);
    result += fc_branch_chain(2, 7, -5);
    result += fc_guarded_call(40, 5);
    result += fc_guarded_call(-40, 5);
    result += fc_guarded_call(10, 0);

    long_result += fc_long_divmod_mix(1234, 17);
    long_result += fc_long_branch_dispatch(1234, 17, 0);
    long_result += fc_long_branch_dispatch(1234, 17, 1);
    result += fc_widen_then_bias(200, 7, 9);

    result += fc_read_after_void(&stats, 5, 8, -2);
    result += stats.total;
    result += stats.count;

    result += fc_recursive_sum(6);
    result += fc_is_even(8);
    result += fc_is_odd(9);
    result += fc_is_even(-4);

    result += fc_dispatch_indirect(0, 7, 5);
    result += fc_dispatch_indirect(1, 7, 5);
    result += fc_apply_indirect(0, 7, 5);

    result += fc_recorded_chain(3, 4, 5);
    result += fc_recorded_branch(12);
    result += fc_recorded_branch(-12);

    function_call_probe += stats.total;
    function_call_probe += stats.count;
    function_call_probe += (int)long_result;

    result += function_call_probe;
    return result & 0xFF;
}
