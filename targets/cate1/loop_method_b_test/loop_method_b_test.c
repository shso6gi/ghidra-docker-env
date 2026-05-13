/*
 * loop_method_b_test.c - method-B loop-summary validation samples
 *
 * Purpose:
 *   Exercise object-centric loop meaning extraction rather than a zero-start
 *   readonly-sum special case.  The functions below are grouped so that an
 *   equivalence run can check both positive pairs and near-miss negative pairs.
 */

#include <stdint.h>

#if defined(__GNUC__) || defined(__clang__)
#define LMB_NOINLINE __attribute__((noinline))
#else
#define LMB_NOINLINE
#endif

volatile int loop_method_b_probe = 0;

typedef struct {
    int total;
    int count;
} lmb_trace;

static LMB_NOINLINE int lmb_term_bias(int value, int bias) {
    return value + bias;
}

static LMB_NOINLINE void lmb_record_step(lmb_trace *trace, int value) {
    if (trace == 0) {
        return;
    }
    trace->total += value;
    trace->count += 1;
    loop_method_b_probe += value;
}

// ============================================================
// Task A/E/F: one meaning object, seed compensation, pairwise use
// ============================================================

int lmb_sum_prefix_loop(const int *base, int count) {
    int sum = 0;

    if (base == 0 || count <= 0) {
        return -300;
    }

    for (int i = 0; i < count; i++) {
        sum += base[i];
    }
    return sum;
}

int lmb_sum_prefix_peeled3_tail(const int *base, int count) {
    int sum;
    int i;

    if (base == 0 || count <= 0) {
        return -300;
    }
    if (count == 1) {
        return base[0];
    }
    if (count == 2) {
        return base[0] + base[1];
    }
    if (count == 3) {
        return base[0] + base[1] + base[2];
    }

    sum = base[0] + base[1] + base[2];
    i = 3;
    while (i < count) {
        sum += base[i];
        i++;
    }
    return sum;
}

int lmb_sum_prefix_peeled1_tail(const int *base, int count) {
    int sum;
    int i;

    if (base == 0 || count <= 0) {
        return -300;
    }
    if (count == 1) {
        return base[0];
    }

    sum = base[0];
    i = 1;
    while (i < count) {
        sum += base[i];
        i++;
    }
    return sum;
}

int lmb_sum_prefix_wrong_tail(const int *base, int count) {
    int sum;
    int i;

    if (base == 0 || count <= 0) {
        return -300;
    }
    if (count <= 3) {
        return lmb_sum_prefix_loop(base, count);
    }

    sum = base[0] + base[2];
    i = 3;
    while (i < count) {
        sum += base[i];
        i++;
    }
    return sum;
}

// ============================================================
// Task C: non-unit step and equivalent loop-counter formulations
// ============================================================

int lmb_sum_even_index_step2(const int *base, int count) {
    int sum = 0;

    if (base == 0 || count <= 0) {
        return -310;
    }

    for (int i = 0; i < count; i += 2) {
        sum += base[i];
    }
    return sum;
}

int lmb_sum_even_index_scaled_counter(const int *base, int count) {
    int sum = 0;
    int pairs;

    if (base == 0 || count <= 0) {
        return -310;
    }

    pairs = (count + 1) / 2;
    for (int k = 0; k < pairs; k++) {
        sum += base[k * 2];
    }
    return sum;
}

int lmb_sum_even_index_wrong_step(const int *base, int count) {
    int sum = 0;

    if (base == 0 || count <= 0) {
        return -310;
    }

    for (int i = 1; i < count; i += 2) {
        sum += base[i];
    }
    return sum;
}

// ============================================================
// Task C/G: dynamic start, dynamic end, and unknown trip count
// ============================================================

int lmb_sum_slice_for(const int *base, int start, int end) {
    int sum = 0;

    if (base == 0 || start < 0 || end < start) {
        return -320;
    }

    for (int i = start; i < end; i++) {
        sum += base[i];
    }
    return sum;
}

int lmb_sum_slice_pointer_walk(const int *base, int start, int end) {
    const int *cur;
    const int *finish;
    int sum = 0;

    if (base == 0 || start < 0 || end < start) {
        return -320;
    }

    cur = base + start;
    finish = base + end;
    while (cur < finish) {
        sum += *cur;
        cur++;
    }
    return sum;
}

int lmb_sum_until_zero_bounded(const int *base, int max_count) {
    int sum = 0;
    int i = 0;

    if (base == 0 || max_count <= 0) {
        return -330;
    }

    while (i < max_count && base[i] != 0) {
        sum += base[i];
        i++;
    }
    return sum;
}

int lmb_sum_until_zero_for_break(const int *base, int max_count) {
    int sum = 0;

    if (base == 0 || max_count <= 0) {
        return -330;
    }

    for (int i = 0; i < max_count; i++) {
        if (base[i] == 0) {
            break;
        }
        sum += base[i];
    }
    return sum;
}

// ============================================================
// Task D: path-sensitive loop body summaries
// ============================================================

int lmb_sum_abs_branch(const int *base, int count) {
    int sum = 0;

    if (base == 0 || count <= 0) {
        return -340;
    }

    for (int i = 0; i < count; i++) {
        int value = base[i];
        if (value < 0) {
            value = -value;
        }
        sum += value;
    }
    return sum;
}

int lmb_sum_abs_conditional_expr(const int *base, int count) {
    int sum = 0;

    if (base == 0 || count <= 0) {
        return -340;
    }

    for (int i = 0; i < count; i++) {
        int value = base[i];
        sum += (value < 0) ? -value : value;
    }
    return sum;
}

int lmb_sum_even_odd_weighted(const int *base, int count) {
    int sum = 0;

    if (base == 0 || count <= 0) {
        return -350;
    }

    for (int i = 0; i < count; i++) {
        int value = base[i];
        if ((value & 1) == 0) {
            sum += value * 2;
        } else {
            sum += value + 3;
        }
    }
    return sum;
}

int lmb_sum_even_odd_weighted_split(const int *base, int count) {
    int sum = 0;

    if (base == 0 || count <= 0) {
        return -350;
    }

    for (int i = 0; i < count; i++) {
        int value = base[i];
        int even_part = ((value & 1) == 0) ? value * 2 : 0;
        int odd_part = ((value & 1) != 0) ? value + 3 : 0;
        sum += even_part + odd_part;
    }
    return sum;
}

// ============================================================
// Task B: side-effect-aware summaries
// ============================================================

int lmb_store_prefix_running_sum(int *dst, const int *src, int count) {
    int sum = 0;

    if (dst == 0 || src == 0 || count <= 0) {
        return -360;
    }

    for (int i = 0; i < count; i++) {
        sum += src[i];
        dst[i] = sum;
    }
    return sum;
}

int lmb_store_prefix_running_sum_while(int *dst, const int *src, int count) {
    int sum = 0;
    int i = 0;

    if (dst == 0 || src == 0 || count <= 0) {
        return -360;
    }

    while (i < count) {
        sum += src[i];
        dst[i] = sum;
        i++;
    }
    return sum;
}

int lmb_store_prefix_wrong_order(int *dst, const int *src, int count) {
    int sum = 0;

    if (dst == 0 || src == 0 || count <= 0) {
        return -360;
    }

    for (int i = 0; i < count; i++) {
        dst[i] = sum;
        sum += src[i];
    }
    return sum;
}

int lmb_trace_loop_for(lmb_trace *trace, const int *base, int count) {
    int sum = 0;

    if (trace == 0 || base == 0 || count <= 0) {
        return -370;
    }

    for (int i = 0; i < count; i++) {
        int value = base[i];
        lmb_record_step(trace, value);
        sum += value;
    }
    return sum + trace->count;
}

int lmb_trace_loop_while(lmb_trace *trace, const int *base, int count) {
    int sum = 0;
    int i = 0;

    if (trace == 0 || base == 0 || count <= 0) {
        return -370;
    }

    while (i < count) {
        int value = base[i];
        lmb_record_step(trace, value);
        sum += value;
        i++;
    }
    return sum + trace->count;
}

// ============================================================
// Task D/G: nested loops and data-dependent inner limits
// ============================================================

int lmb_triangular_sum_nested(const int *base, int rows) {
    int sum = 0;

    if (base == 0 || rows <= 0) {
        return -380;
    }

    for (int i = 0; i < rows; i++) {
        for (int j = 0; j <= i; j++) {
            sum += base[j];
        }
    }
    return sum;
}

int lmb_triangular_sum_reweighted(const int *base, int rows) {
    int sum = 0;

    if (base == 0 || rows <= 0) {
        return -380;
    }

    for (int j = 0; j < rows; j++) {
        sum += base[j] * (rows - j);
    }
    return sum;
}

int lmb_dynamic_inner_limit(const int *base, const int *limits, int rows, int max_cols) {
    int sum = 0;

    if (base == 0 || limits == 0 || rows <= 0 || max_cols <= 0) {
        return -390;
    }

    for (int r = 0; r < rows; r++) {
        int limit = limits[r];
        if (limit < 0) {
            limit = 0;
        }
        if (limit > max_cols) {
            limit = max_cols;
        }
        for (int c = 0; c < limit; c++) {
            sum += base[r * max_cols + c];
        }
    }
    return sum;
}

// ============================================================
// Main harness: keep every function reachable in optimized builds
// ============================================================

int main(void) {
    int data[12] = { 4, -2, 7, 0, 9, 5, -6, 8, 11, -3, 2, 10 };
    int limits[4] = { 1, 3, 2, 4 };
    int out_a[12] = { 0 };
    int out_b[12] = { 0 };
    lmb_trace trace_a = { 0, 0 };
    lmb_trace trace_b = { 0, 0 };
    int result = 0;

    result += lmb_sum_prefix_loop(data, 6);
    result += lmb_sum_prefix_peeled3_tail(data, 6);
    result += lmb_sum_prefix_peeled1_tail(data, 6);
    result += lmb_sum_prefix_wrong_tail(data, 6);

    result += lmb_sum_even_index_step2(data, 9);
    result += lmb_sum_even_index_scaled_counter(data, 9);
    result += lmb_sum_even_index_wrong_step(data, 9);

    result += lmb_sum_slice_for(data, 2, 8);
    result += lmb_sum_slice_pointer_walk(data, 2, 8);
    result += lmb_sum_until_zero_bounded(data, 10);
    result += lmb_sum_until_zero_for_break(data, 10);

    result += lmb_sum_abs_branch(data, 10);
    result += lmb_sum_abs_conditional_expr(data, 10);
    result += lmb_sum_even_odd_weighted(data, 10);
    result += lmb_sum_even_odd_weighted_split(data, 10);

    result += lmb_store_prefix_running_sum(out_a, data, 8);
    result += lmb_store_prefix_running_sum_while(out_b, data, 8);
    result += lmb_store_prefix_wrong_order(out_a, data, 8);

    result += lmb_trace_loop_for(&trace_a, data, 7);
    result += lmb_trace_loop_while(&trace_b, data, 7);

    result += lmb_triangular_sum_nested(data, 5);
    result += lmb_triangular_sum_reweighted(data, 5);
    result += lmb_dynamic_inner_limit(data, limits, 4, 3);

    result += lmb_term_bias(out_a[0], out_b[1]);
    result += trace_a.total + trace_b.total;
    result += trace_a.count + trace_b.count;
    result += loop_method_b_probe;
    return result & 0xFF;
}
