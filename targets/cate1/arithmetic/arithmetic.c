/*
 * arithmetic.c - 基本的な算術演算のテスト
 * 検証対象：整数の加算、減算、乗算、除算
 */

// 加算
int add(int a, int b) {
    return a + b;
}

// 減算
int subtract(int a, int b) {
    return a - b;
}

// 乗算
int multiply(int a, int b) {
    return a * b;
}

// 除算
int divide(int a, int b) {
    if (b == 0) return 0;  // ゼロ除算回避
    return a / b;
}

// 剰余
int modulo(int a, int b) {
    if (b == 0) return 0;
    return a % b;
}

// 複数演算の組み合わせ
int combined_arithmetic(int x, int y, int z) {
    return (x + y) * z - (x / 2);
}

// テスト用main関数
int main() {
    int a = 100, b = 25;
    int result = 0;
    
    result += add(a, b);
    result += subtract(a, b);
    result += multiply(a, b);
    result += divide(a, b);
    result += modulo(a, b);
    result += combined_arithmetic(a, b, 3);
    
    return result;
}