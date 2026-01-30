/*
 * bitwise.c - ビット演算のテスト
 * 検証対象：AND, OR, XOR, NOT, シフト演算
 */

// 論理積（AND）
int bitwise_and(int a, int b) {
    return a & b;
}

// 論理和（OR）
int bitwise_or(int a, int b) {
    return a | b;
}

// 排他的論理和（XOR）
int bitwise_xor(int a, int b) {
    return a ^ b;
}

// 論理否定（NOT）
int bitwise_not(int a) {
    return ~a;
}

// 左シフト
int left_shift(int a, int shift) {
    return a << shift;
}

// 右シフト（論理）
unsigned int right_shift_logical(unsigned int a, int shift) {
    return a >> shift;
}

// 右シフト（算術）
int right_shift_arithmetic(int a, int shift) {
    return a >> shift;
}

// 複合ビット演算（元の要件通り）
int xor_shift(int x) {
    return (x ^ 0xFF) << 2;
}

// ビットマスク操作
int extract_bits(int value, int mask, int shift) {
    return (value & mask) >> shift;
}

// ビット反転
int flip_bits(int value, int position) {
    return value ^ (1 << position);
}

// テスト用main関数
int main() {
    int a = 0xABCD;
    int b = 0x1234;
    int result = 0;
    
    result ^= bitwise_and(a, b);
    result ^= bitwise_or(a, b);
    result ^= bitwise_xor(a, b);
    result ^= bitwise_not(a);
    result ^= left_shift(a, 4);
    result ^= right_shift_logical(a, 4);
    result ^= right_shift_arithmetic(-100, 2);
    result ^= xor_shift(0x55);
    result ^= extract_bits(a, 0xFF00, 8);
    result ^= flip_bits(a, 7);
    
    return result;
}