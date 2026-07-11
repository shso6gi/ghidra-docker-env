__attribute__((noinline, used))
int refactor_not_eq(int value) {
    return value + 2;
}

int main(void) {
    return refactor_not_eq(7);
}
