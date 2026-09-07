/* Issue #104 Gap 4 shape: callees whose body is not in the binary.
 *
 * In a relocatable object an undefined symbol such as unknown_external is a
 * Ghidra thunk to an EXTERNAL function; decompiling it yields a bare RETURN.
 * Before the fix the effect lane read that empty HighFunction as an
 * effect-free callee, so helper (and through it f) looked effect-free.
 * After the fix every external callee is unsupported for the effect lane
 * (callee_effect_summary_missing -> unsupported_call_effect_semantics):
 * there is no name-based library model, so sqrt (s) and printf (p) fail
 * closed exactly like unknown_external.  A symbol name is not evidence of
 * libm/libc semantics.
 */
#include <math.h>
#include <stdio.h>

extern void unknown_external(int);

static void helper(int x) {
    unknown_external(x);
}

int f(int x) {
    helper(x);
    return 0;
}

double s(double x) {
    return sqrt(x);
}

void p(int x) {
    printf("%d\n", x);
}
