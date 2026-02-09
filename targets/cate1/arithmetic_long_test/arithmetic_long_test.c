/*
 * arithmetic_long_test.c - 算術演算の型推論テスト
 * 目的：Ghidraが様々なパターンの除算・剰余演算の型を正しく推論できるか検証
 */

#include <stdint.h>

// ============================================================
// パターン1: 基本的なlong型での除算・剰余
// ============================================================

// 基本的な除算（long版）
long divide_long(long a, long b) {
    if (b == 0) return 0;
    return a / b;
}

// 基本的な剰余（long版）
long modulo_long(long a, long b) {
    if (b == 0) return 0;
    return a % b;
}

// ============================================================
// パターン2: 混合型（異なる引数・戻り値の型）
// ============================================================

// int引数、long戻り値
long divide_int_to_long(int a, int b) {
    if (b == 0) return 0L;
    return (long)a / (long)b;
}

// long引数、int戻り値（切り詰め）
int divide_long_to_int(long a, long b) {
    if (b == 0) return 0;
    return (int)(a / b);
}

// 片方だけlong
long divide_mixed(long a, int b) {
    if (b == 0) return 0;
    return a / b;
}

// 片方だけlong（逆パターン）
long modulo_mixed(int a, long b) {
    if (b == 0) return 0;
    return a % b;
}

// ============================================================
// パターン3: 複数の除算・剰余を組み合わせ
// ============================================================

// 除算と剰余の両方を使用
long divmod_combined(long a, long b) {
    if (b == 0) return 0;
    long quotient = a / b;
    long remainder = a % b;
    return quotient * 1000 + remainder;  // 商と余りを結合
}

// 連鎖的な除算
long chained_divide(long a, long b, long c) {
    if (b == 0 || c == 0) return 0;
    return (a / b) / c;
}

// 連鎖的な剰余
long chained_modulo(long a, long b, long c) {
    if (b == 0 || c == 0) return 0;
    return (a % b) % c;
}

// 複合式での除算・剰余
long complex_arithmetic(long a, long b, long c) {
    if (b == 0 || c == 0) return 0;
    return (a / b) + (a % c) - (b / c);
}

// ============================================================
// パターン4: ポインタ経由での結果返却
// ============================================================

// 商と余りを別々に返す
void divmod_separate(long a, long b, long *quotient, long *remainder) {
    if (b == 0) {
        *quotient = 0;
        *remainder = 0;
        return;
    }
    *quotient = a / b;
    *remainder = a % b;
}

// 商をポインタで返し、余りを戻り値で返す
long divide_with_remainder_ptr(long a, long b, long *remainder) {
    if (b == 0) {
        *remainder = 0;
        return 0;
    }
    *remainder = a % b;
    return a / b;
}

// ============================================================
// パターン5: 条件分岐を含む複雑なロジック
// ============================================================

// 条件付き除算
long conditional_divide(long a, long b, int use_modulo) {
    if (b == 0) return 0;
    if (use_modulo) {
        return a % b;
    } else {
        return a / b;
    }
}

// 符号に応じた処理分岐
long signed_divide_logic(long a, long b) {
    if (b == 0) return 0;
    if (a < 0 && b < 0) {
        return (-a) / (-b);
    } else if (a < 0) {
        return -((-a) / b);
    } else if (b < 0) {
        return -(a / (-b));
    }
    return a / b;
}

// 範囲チェック付き除算
long safe_divide(long a, long b, long min_result, long max_result) {
    if (b == 0) return 0;
    long result = a / b;
    if (result < min_result) return min_result;
    if (result > max_result) return max_result;
    return result;
}

// ============================================================
// パターン6: ループ内での除算・剰余
// ============================================================

// ループ内で累積除算
long loop_divide(long initial, long divisor, int iterations) {
    if (divisor == 0) return 0;
    long result = initial;
    for (int i = 0; i < iterations && result > 0; i++) {
        result = result / divisor;
    }
    return result;
}

// ループ内で剰余を累積
long loop_modulo_sum(long start, long end, long divisor) {
    if (divisor == 0) return 0;
    long sum = 0;
    for (long i = start; i <= end; i++) {
        sum += i % divisor;
    }
    return sum;
}

// GCDアルゴリズム（ユークリッドの互除法）
long gcd(long a, long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        long temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

// LCM（最小公倍数）
long lcm(long a, long b) {
    if (a == 0 || b == 0) return 0;
    long g = gcd(a, b);
    return (a / g) * b;
}

// ============================================================
// パターン7: ビット演算と組み合わせ
// ============================================================

// 2のべき乗での除算（最適化テスト）
long divide_by_power_of_2(long a, int shift) {
    // コンパイラがシフト演算に最適化する可能性あり
    return a / (1L << shift);
}

// 2のべき乗での剰余（マスク最適化テスト）
long modulo_power_of_2(long a, int shift) {
    // コンパイラが a & ((1L << shift) - 1) に最適化する可能性あり
    return a % (1L << shift);
}

// ビット演算と除算の混合
long bitwise_and_divide(long a, long b, long mask) {
    if (b == 0) return 0;
    return (a & mask) / b;
}

// ============================================================
// パターン8: 符号付き・符号なしの違い
// ============================================================

// 符号なし除算
unsigned long unsigned_divide(unsigned long a, unsigned long b) {
    if (b == 0) return 0;
    return a / b;
}

// 符号なし剰余
unsigned long unsigned_modulo(unsigned long a, unsigned long b) {
    if (b == 0) return 0;
    return a % b;
}

// 符号付きと符号なしの混合
long signed_unsigned_mix(long a, unsigned long b) {
    if (b == 0) return 0;
    return a / (long)b;
}

// ============================================================
// パターン9: 固定幅整数型
// ============================================================

// int64_tでの除算
int64_t divide_int64(int64_t a, int64_t b) {
    if (b == 0) return 0;
    return a / b;
}

// uint64_tでの剰余
uint64_t modulo_uint64(uint64_t a, uint64_t b) {
    if (b == 0) return 0;
    return a % b;
}

// int32_tからint64_tへの拡張除算
int64_t widen_divide(int32_t a, int32_t b) {
    if (b == 0) return 0;
    return (int64_t)a / (int64_t)b;
}

// ============================================================
// パターン10: 配列・構造体との組み合わせ
// ============================================================

// 配列要素を使った除算
long array_divide(long arr[], int size, long divisor) {
    if (divisor == 0 || size <= 0) return 0;
    long sum = 0;
    for (int i = 0; i < size; i++) {
        sum += arr[i] / divisor;
    }
    return sum;
}

// 配列インデックスの剰余計算（循環バッファ風）
long circular_access(long arr[], int size, int index) {
    if (size <= 0) return 0;
    int actual_index = index % size;
    if (actual_index < 0) actual_index += size;
    return arr[actual_index];
}

// ============================================================
// パターン11: 複雑な数式
// ============================================================

// 平均計算（除算使用）
long calculate_average(long a, long b, long c) {
    return (a + b + c) / 3;
}

// パーセンテージ計算
long calculate_percentage(long value, long total) {
    if (total == 0) return 0;
    return (value * 100) / total;
}

// 切り上げ除算
long divide_ceiling(long a, long b) {
    if (b == 0) return 0;
    if (a >= 0) {
        return (a + b - 1) / b;
    } else {
        return a / b;
    }
}

// 四捨五入除算
long divide_round(long a, long b) {
    if (b == 0) return 0;
    if ((a >= 0 && b > 0) || (a < 0 && b < 0)) {
        return (a + b / 2) / b;
    } else {
        return (a - b / 2) / b;
    }
}

// ============================================================
// パターン12: 特殊な定数での除算（コンパイラ最適化テスト）
// ============================================================

// 3での除算（乗算+シフトに最適化される可能性）
long divide_by_3(long a) {
    return a / 3;
}

// 7での除算
long divide_by_7(long a) {
    return a / 7;
}

// 10での除算
long divide_by_10(long a) {
    return a / 10;
}

// 10での剰余
long modulo_by_10(long a) {
    return a % 10;
}

// 1000での除算
long divide_by_1000(long a) {
    return a / 1000;
}

// ============================================================
// パターン13: ネストした関数呼び出し
// ============================================================

// 除算結果を別の除算で使用
long nested_divide(long a, long b, long c) {
    if (b == 0 || c == 0) return 0;
    return divide_long(divide_long(a, b), c);
}

// 除算と剰余の組み合わせ結果
long nested_divmod(long a, long b, long c) {
    if (b == 0 || c == 0) return 0;
    long div_result = divide_long(a, b);
    long mod_result = modulo_long(a, c);
    return div_result + mod_result;
}

// ============================================================
// パターン14: インライン計算（複合代入演算子）
// ============================================================

// 複合代入での除算
long compound_divide(long a, long b) {
    if (b == 0) return 0;
    long result = a;
    result /= b;
    result /= 2;
    return result;
}

// 複合代入での剰余
long compound_modulo(long a, long b, long c) {
    if (b == 0 || c == 0) return 0;
    long result = a;
    result %= b;
    result %= c;
    return result;
}

// ============================================================
// パターン15: 三項演算子との組み合わせ
// ============================================================

// 三項演算子での除算選択
long ternary_divide(long a, long b, long c, int selector) {
    if (b == 0 || c == 0) return 0;
    return selector ? (a / b) : (a / c);
}

// 条件付き剰余
long ternary_modulo(long a, long b, int use_abs) {
    if (b == 0) return 0;
    long result = a % b;
    return use_abs ? (result < 0 ? -result : result) : result;
}

// ============================================================
// テスト用main関数
// ============================================================

int main() {
    long a = 1000000L, b = 333L, c = 17L;
    long result = 0;
    
    // パターン1: 基本long型
    result += divide_long(a, b);
    result += modulo_long(a, b);
    
    // パターン2: 混合型
    result += divide_int_to_long(1000, 33);
    result += divide_long_to_int(a, b);
    result += divide_mixed(a, 25);
    result += modulo_mixed(100, b);
    
    // パターン3: 複合演算
    result += divmod_combined(a, b);
    result += chained_divide(a, b, c);
    result += chained_modulo(a, b, c);
    result += complex_arithmetic(a, b, c);
    
    // パターン4: ポインタ
    long quot, rem;
    divmod_separate(a, b, &quot, &rem);
    result += quot + rem;
    result += divide_with_remainder_ptr(a, b, &rem);
    
    // パターン5: 条件分岐
    result += conditional_divide(a, b, 0);
    result += conditional_divide(a, b, 1);
    result += signed_divide_logic(-a, b);
    result += safe_divide(a, b, 0, 10000);
    
    // パターン6: ループ
    result += loop_divide(a, 2, 5);
    result += loop_modulo_sum(1, 100, b);
    result += gcd(a, b);
    result += lcm(12, 18);
    
    // パターン7: ビット演算
    result += divide_by_power_of_2(a, 4);
    result += modulo_power_of_2(a, 4);
    result += bitwise_and_divide(a, b, 0xFFFF);
    
    // パターン8: 符号なし
    result += (long)unsigned_divide(a, b);
    result += (long)unsigned_modulo(a, b);
    
    // パターン9: 固定幅
    result += divide_int64(a, b);
    result += (long)modulo_uint64(a, b);
    result += widen_divide(10000, 33);
    
    // パターン10: 配列
    long arr[] = {100, 200, 300, 400, 500};
    result += array_divide(arr, 5, 10);
    result += circular_access(arr, 5, 7);
    
    // パターン11: 複雑な数式
    result += calculate_average(a, b, c);
    result += calculate_percentage(b, a);
    result += divide_ceiling(a, b);
    result += divide_round(a, b);
    
    // パターン12: 定数除算
    result += divide_by_3(a);
    result += divide_by_7(a);
    result += divide_by_10(a);
    result += modulo_by_10(a);
    result += divide_by_1000(a);
    
    // パターン13: ネスト
    result += nested_divide(a, b, c);
    result += nested_divmod(a, b, c);
    
    // パターン14: 複合代入
    result += compound_divide(a, b);
    result += compound_modulo(a, b, c);
    
    // パターン15: 三項演算子
    result += ternary_divide(a, b, c, 1);
    result += ternary_modulo(a, b, 1);
    
    // 結果をint範囲に収める
    return (int)(result % 256);
}