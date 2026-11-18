/* Synthetic functions for the concrete-execution address and global-state rules (#18). */
int g_table[4] = {10, 20, 30, 40};          /* writable, initialized (.data) */
int g_counter;                               /* writable, zero (.bss) */
static const int c_table[4] = {7, 11, 13, 17};  /* read-only (.rodata) */

/* A pointer return: the value is an image address. */
int *ret_global_ptr(int x) { return &g_table[x & 3]; }

/* The same address returned as an integer. */
long ret_global_addr_as_long(int x) { return (long)&g_table[x & 3]; }

/* The difference of two addresses of one object does not depend on placement. */
long ret_pointer_difference(int x) {
    int local[8];
    int *p = &local[x & 7];
    int *q = &local[0];
    return p - q;
}

/* An address of the stack frame returned as an integer. */
long ret_stack_addr(int x) {
    volatile int local[4];
    local[x & 3] = x;
    return (long)&local[x & 3];
}

/* A branch decided by the bits of an image address. */
int branch_on_address_bits(int x) {
    unsigned long a = (unsigned long)&g_table[x & 3];
    return (a & 0x10) ? 1 : 2;
}

/* Reads writable program data. */
int read_writable_global(int x) { return g_table[x & 3] + x; }

/* Reads zero-initialized writable data. */
int read_bss_counter(int x) { return g_counter + x; }

/* Reads read-only data only. */
int read_const_table(int x) { return c_table[x & 3] + x; }

/* Walks a local array with pointers. */
int walk_local_array(int n) {
    int buf[8];
    int *p, *end = buf + 8;
    int s = 0, i = 0;
    for (p = buf; p != end; ++p) *p = n + i++;
    for (p = buf; p < end; ++p) s += *p;
    return s;
}

/* A null test of a pointer argument-derived value. */
int null_test(int x) {
    int *p = x ? &g_table[0] : 0;
    return p == 0 ? 5 : 6;
}

int main(void) { return 0; }
