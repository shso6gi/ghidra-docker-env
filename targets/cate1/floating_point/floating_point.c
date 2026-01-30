/*
 * floating_point.c - 浮動小数点演算のテスト
 * 検証対象：float/double演算、FMA命令の扱い
 */

// 浮動小数点加算
double fp_add(double a, double b) {
    return a + b;
}

// 浮動小数点減算
double fp_subtract(double a, double b) {
    return a - b;
}

// 浮動小数点乗算
double fp_multiply(double a, double b) {
    return a * b;
}

// 浮動小数点除算
double fp_divide(double a, double b) {
    if (b == 0.0) return 0.0;
    return a / b;
}

// FMA演算（元の要件通り）
double fma(double a, double b, double c) {
    return a * b + c;  // FMA命令がある環境では1命令
}

// 複合浮動小数点演算
double complex_fp(double x, double y) {
    return (x * 2.0 + 3.0) / (y + 1.0);
}

// 二次方程式の判別式
double discriminant(double a, double b, double c) {
    return b * b - 4.0 * a * c;
}

// 単精度と倍精度の混在
double mixed_precision(float f, double d) {
    return (double)f * 2.0 + d;
}

// 連続した乗算と加算（複数のFMAパターン）
double multi_fma(double x, double y, double z) {
    double temp1 = x * y + z;        // FMA
    double temp2 = temp1 * 2.0 + x;  // FMA
    return temp2;
}

// 平方根近似（ニュートン法の1ステップ）
double sqrt_approx(double x, double guess) {
    return (guess + x / guess) * 0.5;
}

// テスト用main関数
int main() {
    double a = 3.14, b = 2.71, c = 1.41;
    double result = 0.0;
    
    result += fp_add(a, b);
    result += fp_subtract(a, b);
    result += fp_multiply(a, b);
    result += fp_divide(a, b);
    result += fma(a, b, c);
    result += complex_fp(a, b);
    result += discriminant(1.0, -3.0, 2.0);
    result += mixed_precision(2.5f, 3.5);
    result += multi_fma(a, b, c);
    result += sqrt_approx(2.0, 1.5);
    
    return (int)result;
}