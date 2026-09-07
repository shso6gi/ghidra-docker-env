/* Issue #104 Gap 3 shape: a scalar-only call chain with an unknown side effect.
 *
 *   f(x) --> helper(x) --> (*g_hook)(x)      g_hook is a global function pointer
 *
 * helper takes only a scalar and recovers no store effect of its own, but its
 * summary contains an unresolved indirect call.  Before the fix the
 * effect-summary layer of the caller f silently dropped this incompleteness
 * because no argument could expose parameter memory, leaving no
 * effect-summary blocker for f.  Absent an independent blocker in another
 * proof lane (pure-call / callsite correspondence), this could permit an
 * unsound EQUIVALENT decision.  After the fix the incompleteness propagates
 * to f (unsupported_call_effect_semantics, reason
 * callee_unsupported_call_effects_unresolved) and the effect summary itself
 * keeps the pair away from EQUIVALENT until the nested call is modelled.
 * The unit regression is
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
