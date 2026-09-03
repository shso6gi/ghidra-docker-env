#include <stdint.h>

__attribute__((noinline))
uint64_t zext_or_repro_tail_index_probe(uint32_t count, uint64_t *out_start) {
    uint64_t count64 = (uint64_t)count;
    uint64_t rounded = count64 & UINT64_C(0xfffffffffffffff0);
    uint64_t start = rounded | (UINT64_C(1) << 40);
    *out_start = start;
    return start;
}

int main(void) {
    return 0;
}
