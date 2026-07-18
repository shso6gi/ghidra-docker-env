#include <stdint.h>

__attribute__((noinline)) uint32_t slice5_high_bit_projection(uint32_t value) {
    return value;
}

int main(void) {
    return (int)slice5_high_bit_projection(1U);
}
