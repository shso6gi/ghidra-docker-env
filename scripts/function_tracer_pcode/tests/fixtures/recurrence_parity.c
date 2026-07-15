/* Real-binary regression fixture for the bounded small-modulus summary. */
int recurrence_parity_sum(int n) {
    int i = 0;
    int acc = 0;
    while (i < n) {
        acc += (i & 1) + 1;
        i++;
    }
    return acc;
}
