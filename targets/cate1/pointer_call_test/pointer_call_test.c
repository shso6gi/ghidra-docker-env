/*
 * pointer_call_test.c - 関数呼び出しとポインタ操作の複合テスト
 * 目的：関数等価性判定プログラム向けに、呼び出しチェーン・out-parameter・
 *       alias・二重ポインタ・関数ポインタを含む典型パターンを観察する
 */

#include <stdint.h>

volatile int pointer_probe = 0;

typedef struct {
    int value;
    int extra;
    int *link;
} pointer_box;

// ============================================================
// パターン1: 基本的な関数呼び出し
// ============================================================

int ptr_add_bias(int value, int bias) {
    return value + bias;
}

int ptr_scale_then_bias(int value, int scale, int bias) {
    return value * scale + bias;
}

int ptr_call_leaf(int value) {
    return ptr_add_bias(value, 7);
}

int ptr_call_chain(int value) {
    return ptr_scale_then_bias(ptr_call_leaf(value), 2, -3);
}

// ============================================================
// パターン2: 条件分岐を含む呼び出し
// ============================================================

int ptr_select_path(int a, int b, int choose_left) {
    if (choose_left) {
        return ptr_add_bias(a, 10);
    }
    return ptr_scale_then_bias(b, 3, 1);
}

int ptr_nested_dispatch(int a, int b, int c) {
    int mid = ptr_select_path(a, b, a > b);
    if (mid > c) {
        return ptr_add_bias(mid - c, 5);
    }
    return ptr_scale_then_bias(c - mid, 2, -1);
}

// ============================================================
// パターン3: out-parameter / in-out parameter
// ============================================================

void ptr_store_sum_and_diff(int a, int b, int *sum_out, int *diff_out) {
    if (sum_out == 0 || diff_out == 0) {
        return;
    }
    *sum_out = a + b;
    *diff_out = a - b;
}

int ptr_read_after_store(int a, int b) {
    int sum = 0;
    int diff = 0;

    ptr_store_sum_and_diff(a, b, &sum, &diff);
    return sum * 4 + diff;
}

int ptr_update_in_place(int *value, int delta, int negate) {
    if (value == 0) {
        return -100;
    }
    if (negate) {
        *value = -*value + delta;
    } else {
        *value = *value + delta;
    }
    return *value;
}

// ============================================================
// パターン4: alias に敏感なポインタ更新
// ============================================================

int ptr_alias_adjust(int *dst, int *src, int delta) {
    if (dst == 0 || src == 0) {
        return -200;
    }

    *dst = *dst + delta;
    *src = *src - 1;

    if (dst == src) {
        return *dst;
    }
    return *dst + *src;
}

int ptr_copy_or_accumulate(int *dst, const int *src, int copy_flag) {
    if (dst == 0 || src == 0) {
        return -210;
    }
    if (copy_flag) {
        *dst = *src;
    } else {
        *dst += *src;
    }
    return *dst;
}

// ============================================================
// パターン5: ポインタ演算と配列アクセス
// ============================================================

int ptr_sum_window(const int *base, int count) {
    int sum = 0;
    if (base == 0 || count <= 0) {
        return -300;
    }

    for (int i = 0; i < count; i++) {
        sum += *(base + i);
    }
    return sum;
}

int ptr_stride_pick(const int *base, int stride, int index) {
    const int *target;

    if (base == 0 || stride <= 0 || index < 0) {
        return -310;
    }

    target = base + stride * index;
    return *target;
}

// ============================================================
// パターン6: 二重ポインタによる参照先切り替え
// ============================================================

void ptr_choose_target(int **slot, int *left, int *right, int choose_right) {
    if (slot == 0) {
        return;
    }
    if (choose_right) {
        *slot = right;
    } else {
        *slot = left;
    }
}

int ptr_double_indirect_write(int **slot, int value) {
    if (slot == 0 || *slot == 0) {
        return -400;
    }
    **slot = value;
    return **slot + 1;
}

// ============================================================
// パターン7: 構造体フィールドと補助関数
// ============================================================

int ptr_box_follow_link(const pointer_box *box) {
    if (box == 0 || box->link == 0) {
        return -500;
    }
    return *box->link + box->extra;
}

int ptr_box_mutate(pointer_box *box, int delta) {
    if (box == 0) {
        return -510;
    }

    box->value += delta;
    if (box->link != 0) {
        *box->link += box->value;
    }
    return box->value;
}

// ============================================================
// パターン8: 関数ポインタ経由の間接呼び出し
// ============================================================

int ptr_op_add(int a, int b) {
    return a + b;
}

int ptr_op_xor(int a, int b) {
    return a ^ b;
}

int ptr_apply_callback(int (*op)(int, int), int a, int b) {
    if (op == 0) {
        return -600;
    }
    return op(a, b);
}

int ptr_dispatch_callback(int mode, int a, int b) {
    int (*op)(int, int) = ptr_op_add;

    if (mode & 1) {
        op = ptr_op_xor;
    }
    return ptr_apply_callback(op, a, b);
}

// ============================================================
// パターン9: 呼び出し結果とポインタ更新の組み合わせ
// ============================================================

int ptr_call_and_store(int *dst, int a, int b, int use_callback) {
    int value;

    if (dst == 0) {
        return -700;
    }

    if (use_callback) {
        value = ptr_dispatch_callback(1, a, b);
    } else {
        value = ptr_call_chain(a) + b;
    }

    *dst = value;
    return *dst - a;
}

int ptr_branch_on_loaded_value(const int *ptr, int threshold) {
    int loaded;

    if (ptr == 0) {
        return -710;
    }

    loaded = *ptr;
    if (loaded > threshold) {
        return ptr_add_bias(loaded, -threshold);
    }
    return ptr_scale_then_bias(threshold - loaded, 2, 0);
}

// ============================================================
// パターン10: main からまとめて呼び出し
// ============================================================

int main(void) {
    int data[5] = { 4, 9, 15, 16, 23 };
    int left = 10;
    int right = 20;
    int alias = 7;
    int stored = 0;
    int *selected = 0;
    pointer_box box = { 3, 5, &left };
    int result = 0;

    result += ptr_call_leaf(8);
    result += ptr_call_chain(5);

    result += ptr_select_path(7, 4, 1);
    result += ptr_nested_dispatch(3, 9, 20);

    result += ptr_read_after_store(12, 5);
    result += ptr_update_in_place(&stored, 6, 0);
    result += ptr_update_in_place(&stored, 2, 1);

    result += ptr_alias_adjust(&left, &right, 4);
    result += ptr_alias_adjust(&alias, &alias, 3);
    result += ptr_copy_or_accumulate(&stored, &data[2], 0);

    result += ptr_sum_window(data, 4);
    result += ptr_stride_pick(data, 2, 1);

    ptr_choose_target(&selected, &left, &right, 1);
    result += ptr_double_indirect_write(&selected, 33);

    result += ptr_box_follow_link(&box);
    result += ptr_box_mutate(&box, 4);

    result += ptr_dispatch_callback(0, 6, 2);
    result += ptr_dispatch_callback(1, 6, 2);

    result += ptr_call_and_store(&stored, 4, 11, 0);
    result += ptr_call_and_store(&stored, 4, 11, 1);
    result += ptr_branch_on_loaded_value(&stored, 8);

    pointer_probe += data[0];
    pointer_probe += data[1];
    pointer_probe += data[2];
    pointer_probe += data[3];
    pointer_probe += data[4];
    pointer_probe += left;
    pointer_probe += right;
    pointer_probe += alias;
    pointer_probe += stored;
    pointer_probe += box.value;
    pointer_probe += box.extra;

    result += pointer_probe;
    return result & 0xFF;
}
