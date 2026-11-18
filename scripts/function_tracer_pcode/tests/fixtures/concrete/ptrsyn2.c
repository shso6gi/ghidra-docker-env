/* Same-kind address pairs that are NOT one object (#18 C2a review).  Each function is
   one source; two builds may place the objects differently, so the results may differ
   between builds of this same source.  Concrete evidence must not call that a difference. */
#include <stdint.h>
int g_a = 1, g_b = 2;            /* two distinct writable objects (.data)  */
static const int k_a = 3, k_b = 4; /* two distinct read-only objects       */
int g_arr[8];

/* relational comparison of two different globals, through uintptr_t (implementation-defined) */
int global_order(int x) { return ((uintptr_t)&g_b < (uintptr_t)&g_a) ? x + 1 : x + 2; }
/* distance between two different globals as an integer */
long global_distance(int x) { return (long)((uintptr_t)&g_b - (uintptr_t)&g_a) + x; }
/* the same for read-only objects */
long const_distance(int x) { return (long)((uintptr_t)&k_b - (uintptr_t)&k_a) + x; }
/* one-past-the-end equality of two objects (unspecified in C) */
int one_past_equal(int x) { return (&g_a + 1 == &g_b) ? x + 1 : x + 2; }
/* two different stack objects */
int stack_order(int x) {
    volatile int u = x, v = x + 1;
    return ((uintptr_t)&u < (uintptr_t)&v) ? u : v + 10;
}
long stack_distance(int x) {
    volatile int u = x, v = x + 1;
    return (long)((uintptr_t)&v - (uintptr_t)&u) + u;
}
/* one object: the placement cancels (legitimate; refusing it costs precision only) */
long same_array_distance(int x) { int *p = &g_arr[x & 7]; return (long)(p - &g_arr[0]); }
int main(void) { return 0; }
