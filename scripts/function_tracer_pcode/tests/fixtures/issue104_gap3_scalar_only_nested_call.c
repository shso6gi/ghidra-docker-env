/* Issue #104 Gap 3 shape: a scalar-only call chain with an unknown side effect.
 *
 *   f(x) --> helper(x) --> (*g_hook)(x)      g_hook is a global function pointer
 *
 * helper takes only a scalar and recovers no store effect of its own, but its
 * summary contains an unresolved indirect call.  Before the fix the caller f
 * treated helper as effect-free because no argument could expose parameter
 * memory; two versions of f whose helper differs in the hidden call were then
 * provable EQUIVALENT.  After the fix the incompleteness propagates to f
 * (unsupported_call_effect_semantics, reason
 * callee_unsupported_call_effects_unresolved) and the pair stays UNKNOWN
 * until the nested call is modelled.  The unit regression is
 * test_memory_model_call_4.py::test_summarize_store_effects_propagates_scalar_only_unsupported_callee.
 */
void (*g_hook)(int);

static void helper(int x) {
    g_hook(x);
}

int f(int x) {
    helper(x);
    return 0;
}
