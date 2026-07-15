/* Real-binary regression fixture for guarded affine state transitions. */
int recurrence_guarded_steps(int x) {
    int acc = 0;
    while (x > 0) {
        if ((x & 1) != 0) {
            x = x - 1;
        } else {
            x = x - 2;
        }
        acc = acc + 1;
    }
    return acc;
}
