/*
 * memory_effect_test.c - LOAD/STORE/ポインタ操作の動作テスト
 * 目的：戻り値逆トレースだけでは扱いづらいメモリ依存パターンを、
 *       最小限の関数群で観察できるようにする
 */

#include <stdint.h>

volatile int memory_probe = 0;

static const int lookup_table[] = { 5, 7, 11, 13, 17, 19 };

typedef struct {
    int left;
    int right;
} pair_box;

// ============================================================
// パターン1: rodata / jump-table 風の LOAD
// ============================================================

int mem_rodata_lookup(int index) {
    if ((unsigned int)index >= 6U) {
        return -1;
    }
    return lookup_table[index];
}

int mem_rodata_lookup_bias(int index, int bias) {
    if ((unsigned int)index >= 6U) {
        return bias - 100;
    }
    return lookup_table[index] + bias;
}

// ============================================================
// パターン2: stack 上の STORE -> LOAD
// ============================================================

int mem_stack_store_reload(int a, int b, int select_first) {
    int local[2];
    local[0] = a + 10;
    local[1] = b - 3;
    if (select_first) {
        return local[0];
    }
    return local[1];
}

int mem_stack_conditional_store(int seed, int flag) {
    int slot = seed;
    if (flag > 0) {
        slot = seed + 7;
    } else {
        slot = seed - 9;
    }
    return slot;
}

// ============================================================
// パターン3: 引数ポインタ経由の LOAD
// ============================================================

int mem_pointer_load_basic(const int *ptr) {
    if (ptr == 0) {
        return -300;
    }
    return *ptr;
}

int mem_pointer_index_sum(const int *values, int index) {
    if (values == 0) {
        return -400;
    }
    if (index < 0 || index >= 3) {
        return -401;
    }
    return values[index] + values[index + 1];
}

// ============================================================
// パターン4: 引数ポインタ経由の STORE が return に影響
// ============================================================

int mem_pointer_store_then_read(int *ptr, int value) {
    if (ptr == 0) {
        return -500;
    }
    *ptr = value + 3;
    return *ptr - 1;
}

int mem_pointer_store_select(int *ptr, int value, int flag) {
    if (ptr == 0) {
        return -510;
    }
    if (flag) {
        ptr[0] = value;
    } else {
        ptr[0] = -value;
    }
    return ptr[0];
}

// ============================================================
// パターン5: alias / pointer compare
// ============================================================

int mem_alias_sensitive_add(int *dst, int *src, int delta) {
    if (dst == 0 || src == 0) {
        return -600;
    }
    *dst = *dst + delta;
    if (dst == src) {
        return *src;
    }
    return *dst + *src;
}

int mem_alias_conditional_copy(int *dst, int *src, int choose_src) {
    if (dst == 0 || src == 0) {
        return -610;
    }
    if (choose_src) {
        *dst = *src;
    } else {
        *dst = *dst + 1;
    }
    return *dst;
}

// ============================================================
// パターン6: struct field access (PTRSUB 由来を期待)
// ============================================================

int mem_struct_pick_field(const pair_box *box, int pick_right) {
    if (box == 0) {
        return -700;
    }
    if (pick_right) {
        return box->right;
    }
    return box->left;
}

int mem_struct_update_field(pair_box *box, int delta, int update_right) {
    if (box == 0) {
        return -710;
    }
    if (update_right) {
        box->right += delta;
        return box->right;
    }
    box->left -= delta;
    return box->left;
}

// ============================================================
// パターン7: return を持たない副作用関数
// ============================================================

void mem_void_write_if_needed(int *ptr, int value) {
    if (ptr == 0) {
        return;
    }
    if (value > 0) {
        ptr[0] = value;
    } else {
        ptr[0] = -value;
    }
}

void mem_void_swap_if_greater(int *a, int *b) {
    int tmp;
    if (a == 0 || b == 0) {
        return;
    }
    if (*a > *b) {
        tmp = *a;
        *a = *b;
        *b = tmp;
    }
}

// ============================================================
// パターン8: 副作用の観測
// ============================================================

int mem_observe_after_void(int *ptr, int value) {
    if (ptr == 0) {
        return -800;
    }
    mem_void_write_if_needed(ptr, value);
    return ptr[0];
}

int mem_observe_after_swap(int *a, int *b) {
    if (a == 0 || b == 0) {
        return -810;
    }
    mem_void_swap_if_greater(a, b);
    return a[0] - b[0];
}

// ============================================================
// パターン9: main からまとめて呼び出し
// ============================================================

int main(void) {
    int values[4] = { 3, 8, 21, 34 };
    int dst = 10;
    int src = 4;
    int alias = 6;
    int write_slot = 0;
    pair_box box = { 12, 20 };
    int result = 0;

    result += mem_rodata_lookup(2);
    result += mem_rodata_lookup(9);
    result += mem_rodata_lookup_bias(4, 3);

    result += mem_stack_store_reload(5, 30, 1);
    result += mem_stack_store_reload(5, 30, 0);
    result += mem_stack_conditional_store(11, -1);

    result += mem_pointer_load_basic(&values[0]);
    result += mem_pointer_load_basic(0);
    result += mem_pointer_index_sum(values, 1);

    result += mem_pointer_store_then_read(&write_slot, 9);
    result += mem_pointer_store_select(&write_slot, 7, 0);

    result += mem_alias_sensitive_add(&dst, &src, 5);
    result += mem_alias_sensitive_add(&alias, &alias, 2);
    result += mem_alias_conditional_copy(&dst, &src, 1);

    result += mem_struct_pick_field(&box, 0);
    result += mem_struct_pick_field(&box, 1);
    result += mem_struct_update_field(&box, 3, 1);

    mem_void_write_if_needed(&values[0], -14);
    mem_void_swap_if_greater(&values[1], &values[2]);

    result += mem_observe_after_void(&values[3], -5);
    result += mem_observe_after_swap(&values[1], &values[2]);

    memory_probe += values[0];
    memory_probe += values[1];
    memory_probe += values[2];
    memory_probe += values[3];
    memory_probe += write_slot;
    memory_probe += dst;
    memory_probe += src;
    memory_probe += alias;
    memory_probe += box.left;
    memory_probe += box.right;

    result += memory_probe;
    return result & 0xFF;
}
