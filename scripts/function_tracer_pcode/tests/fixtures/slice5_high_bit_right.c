#include <stdint.h>

__attribute__((noinline)) uint64_t slice5_high_bit_projection(uint32_t value) {
    return ((uint64_t)value) | (UINT64_C(1) << 40);
}

int main(void) {
    return (int)slice5_high_bit_projection(1U);
}
