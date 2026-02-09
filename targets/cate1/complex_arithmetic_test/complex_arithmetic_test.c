/*
 * complex_arithmetic_test.c - 複雑な演算フローのテスト
 * 目的：除算/剰余が中間にある場合のGhidra型推論テスト
 */

#include <stdint.h>

// ============================================================
// パターン1: 前処理 → 除算 → 後処理
// ============================================================

// 加算 → 除算 → 乗算
int calc_add_div_mul(int a, int b, int c) {
    int temp1 = a + b;           // 前処理：加算
    int temp2 = temp1 / c;       // 除算
    int result = temp2 * 5;      // 後処理：乗算
    return result;
}

// 乗算 → 除算 → 減算
int calc_mul_div_sub(int a, int b, int c) {
    int temp1 = a * b;           // 前処理：乗算
    int temp2 = temp1 / c;       // 除算
    int result = temp2 - 100;    // 後処理：減算
    return result;
}

// シフト → 剰余 → OR演算
int calc_shift_mod_or(int a, int b, int mask) {
    int temp1 = a << 2;          // 前処理：左シフト
    int temp2 = temp1 % b;       // 剰余
    int result = temp2 | mask;   // 後処理：OR
    return result;
}

// AND → 除算 → XOR
int calc_and_div_xor(int a, int b, int c) {
    int temp1 = a & 0xFFFF;      // 前処理：AND
    int temp2 = temp1 / b;       // 除算
    int result = temp2 ^ c;      // 後処理：XOR
    return result;
}

// ============================================================
// パターン2: 複数の除算・剰余が混在
// ============================================================

// 加算 → 除算 → 加算 → 剰余 → 乗算
int calc_mixed_divmod(int a, int b, int c) {
    int step1 = a + 100;
    int step2 = step1 / b;
    int step3 = step2 + 50;
    int step4 = step3 % c;
    int result = step4 * 3;
    return result;
}

// 交互に演算：乗 → 除 → 加 → 剰 → 減
int calc_alternating_ops(int a, int b, int c, int d) {
    int v1 = a * 7;
    int v2 = v1 / b;
    int v3 = v2 + c;
    int v4 = v3 % d;
    int v5 = v4 - 10;
    return v5;
}

// 除算と剰余を同時に活用
int calc_divmod_parallel(int a, int b) {
    if (b == 0) return 0;
    int quotient = a / b;
    int remainder = a % b;
    int combined = quotient * 100 + remainder;
    int final = combined + (quotient - remainder);
    return final;
}

// ============================================================
// パターン3: 累積計算
// ============================================================

// 累積加算してから除算、その後さらに加算
int calc_accumulate_div(int a, int b, int c, int d) {
    int sum = a + b + c;
    int divided = sum / d;
    int result = divided + a + b;
    return result;
}

// 累積乗算してから剰余、その後減算
int calc_accumulate_mod(int a, int b, int c) {
    int product = a * b;
    int remainder = product % c;
    int result = remainder - (a + b);
    return result;
}

// 段階的な累積と除算
int calc_staged_accumulate(int a, int b, int c) {
    int acc = 0;
    acc += a * 2;
    acc += b * 3;
    int divided = acc / c;
    acc = divided + a;
    acc -= b / 2;
    return acc;
}

// ============================================================
// パターン4: ビット演算との複合
// ============================================================

// ビット操作 → 除算 → ビット操作
int calc_bit_div_bit(int a, int b) {
    int masked = a & 0x0FFF;
    int shifted = masked << 4;
    int divided = shifted / b;
    int result = divided >> 2;
    result = result | 0x80;
    return result;
}

// 複合ビット演算と剰余
int calc_complex_bit_mod(int a, int b, int c) {
    int temp = (a ^ b) & 0xFFFF;
    int mod_result = temp % c;
    int final = (mod_result << 1) | (mod_result >> 7);
    return final & 0xFF;
}

// 符号拡張と除算
int calc_sign_extend_div(int a, int b) {
    int extended = (a << 16) >> 16;  // 16bit符号拡張
    int processed = extended + 1000;
    int divided = processed / b;
    int result = divided & 0x7FFF;
    return result;
}

// ============================================================
// パターン5: 条件付き演算
// ============================================================

// 条件分岐後に除算
int calc_cond_then_div(int a, int b, int c) {
    int temp;
    if (a > 100) {
        temp = a * 2;
    } else {
        temp = a + 50;
    }
    int divided = temp / b;
    int result = divided + c;
    return result;
}

// 除算後に条件分岐
int calc_div_then_cond(int a, int b) {
    if (b == 0) return 0;
    int divided = a / b;
    int result;
    if (divided > 10) {
        result = divided * 3;
    } else {
        result = divided + 20;
    }
    return result + 5;
}

// 条件に除算結果を使用
int calc_div_in_cond(int a, int b, int c) {
    if (b == 0) return 0;
    int check = a / b;
    if (check > c) {
        return (a % b) + 100;
    } else {
        return (a / c) - 50;
    }
}

// 複数条件と除算の組み合わせ
int calc_multi_cond_div(int a, int b, int c) {
    if (b == 0 || c == 0) return 0;
    
    int result = a;
    if (a > 0) {
        result = result / b;
        if (result > 50) {
            result = result % c;
        }
    } else {
        result = (-a) / b;
        result = -result;
    }
    return result + 1;
}

// ============================================================
// パターン6: ループ内での複合演算
// ============================================================

// ループ前処理 → ループ内除算 → ループ後処理
int calc_loop_with_div(int base, int divisor, int count) {
    if (divisor == 0) return 0;
    
    int prepared = base * 2 + 100;
    int acc = 0;
    
    for (int i = 0; i < count; i++) {
        int temp = (prepared + i) / divisor;
        acc += temp;
    }
    
    int result = acc - count + 10;
    return result;
}

// ループ内で剰余を使った累積
int calc_loop_mod_accumulate(int start, int modulus, int iterations) {
    if (modulus == 0) return 0;
    
    int value = start;
    int sum = 0;
    
    for (int i = 0; i < iterations; i++) {
        value = (value * 3 + 7) % modulus;
        sum += value;
    }
    
    return sum / iterations;
}

// ネストしたループと除算
int calc_nested_loop_div(int a, int b, int c) {
    if (b == 0 || c == 0) return 0;
    
    int total = 0;
    for (int i = 1; i <= a; i++) {
        int row_sum = 0;
        for (int j = 1; j <= i; j++) {
            row_sum += (i * j) / b;
        }
        total += row_sum % c;
    }
    return total;
}

// ============================================================
// パターン7: 数学的計算
// ============================================================

// 平均と偏差の計算
int calc_average_deviation(int a, int b, int c) {
    int sum = a + b + c;
    int avg = sum / 3;
    int dev = ((a - avg) + (b - avg) + (c - avg)) / 3;
    return avg + dev;
}

// パーセント計算と丸め
int calc_percent_rounded(int value, int total, int precision) {
    if (total == 0) return 0;
    int scaled = value * 100 * precision;
    int percent = scaled / total;
    int rounded = (percent + precision / 2) / precision;
    return rounded;
}

// 比率計算
int calc_ratio(int numerator, int denominator, int scale) {
    if (denominator == 0) return 0;
    int pre_scale = numerator * scale;
    int ratio = pre_scale / denominator;
    int adjusted = ratio + (numerator % denominator > denominator / 2 ? 1 : 0);
    return adjusted;
}

// 階乗の近似（除算を含む）
int calc_factorial_approx(int n, int divisor) {
    if (divisor == 0) return 0;
    int result = 1;
    for (int i = 2; i <= n && i <= 12; i++) {
        result *= i;
        if (result > 1000000) {
            result = result / divisor;
        }
    }
    return result % 10000;
}

// ============================================================
// パターン8: 式の中に埋め込まれた除算
// ============================================================

// 複合式内の除算
int calc_embedded_div(int a, int b, int c) {
    if (b == 0 || c == 0) return 0;
    return ((a * 3 + 10) / b - 5) * c + (a % b);
}

// 入れ子の除算式
int calc_nested_div_expr(int a, int b, int c, int d) {
    if (b == 0 || c == 0 || d == 0) return 0;
    return (a / b + c / d) * (a % b - c % d) + 1;
}

// 三項演算子内の除算
int calc_ternary_embedded(int a, int b, int c) {
    if (b == 0 || c == 0) return 0;
    int x = a > 50 ? (a / b) * 2 : (a % c) + 10;
    int y = x > 20 ? x / 3 : x * 2;
    return y + a / (b + 1);
}

// 関数呼び出し風の式（マクロ的な使い方）
int calc_func_like_expr(int a, int b, int c) {
    if (b == 0 || c == 0) return 0;
    
    int min_val = (a < b) ? a : b;
    int max_val = (a > b) ? a : b;
    
    int range = max_val - min_val;
    int mid = min_val + range / 2;
    int normalized = (a - min_val) * 100 / (range == 0 ? 1 : range);
    
    return (mid % c) + normalized;
}

// ============================================================
// パターン9: 配列インデックス計算
// ============================================================

// 配列インデックス計算に除算使用
int calc_array_index_div(int data[], int size, int pos, int stride) {
    if (stride == 0 || size == 0) return 0;
    
    int base_idx = pos / stride;
    int offset = pos % stride;
    
    if (base_idx >= size) base_idx = size - 1;
    if (base_idx < 0) base_idx = 0;
    
    int value = data[base_idx];
    int adjusted = value + offset * 10;
    
    return adjusted / 2 + base_idx;
}

// 2次元配列風のインデックス計算
int calc_2d_index(int data[], int width, int height, int x, int y) {
    if (width == 0) return 0;
    
    int row = y % height;
    int col = x % width;
    int index = row * width + col;
    
    int value = data[index % (width * height)];
    int result = value / 10 + row + col;
    
    return result;
}

// ============================================================
// パターン10: ハッシュ・チェックサム風計算
// ============================================================

// 簡易ハッシュ計算
int calc_simple_hash(int a, int b, int c) {
    int h = 17;
    h = h * 31 + a;
    h = h * 31 + b;
    h = h * 31 + c;
    
    int folded = (h >> 16) ^ (h & 0xFFFF);
    int normalized = folded % 1000;
    
    return normalized + (h / 1000000);
}

// チェックサム計算
int calc_checksum(int data[], int size) {
    if (size == 0) return 0;
    
    int sum = 0;
    for (int i = 0; i < size; i++) {
        sum += data[i];
        sum = (sum << 1) | (sum >> 31);  // rotate
    }
    
    int high = sum / 65536;
    int low = sum % 65536;
    int combined = high + low;
    
    return combined % 256;
}

// ============================================================
// パターン11: 座標・幾何計算
// ============================================================

// 距離の近似計算
int calc_distance_approx(int x1, int y1, int x2, int y2) {
    int dx = x2 - x1;
    int dy = y2 - y1;
    if (dx < 0) dx = -dx;
    if (dy < 0) dy = -dy;
    
    int max_d = (dx > dy) ? dx : dy;
    int min_d = (dx < dy) ? dx : dy;
    
    // 近似: max + min/2 （実際の距離の近似）
    int approx = max_d + min_d / 2;
    int normalized = approx * 100 / (max_d == 0 ? 1 : max_d);
    
    return approx + normalized / 10;
}

// 角度の正規化（度）
int calc_normalize_angle(int angle) {
    int normalized = angle % 360;
    if (normalized < 0) normalized += 360;
    
    int quadrant = normalized / 90;
    int remainder = normalized % 90;
    
    return quadrant * 100 + remainder;
}

// グリッド座標計算
int calc_grid_position(int x, int y, int cell_size, int grid_width) {
    if (cell_size == 0 || grid_width == 0) return 0;
    
    int cell_x = x / cell_size;
    int cell_y = y / cell_size;
    
    int offset_x = x % cell_size;
    int offset_y = y % cell_size;
    
    int cell_index = cell_y * grid_width + cell_x;
    int sub_position = offset_y * cell_size + offset_x;
    
    return cell_index * 1000 + sub_position / 10;
}

// ============================================================
// パターン12: 時間・日付計算
// ============================================================

// 秒から時:分:秒への変換（結合して返す）
int calc_seconds_to_hms(int total_seconds) {
    int hours = total_seconds / 3600;
    int remaining = total_seconds % 3600;
    int minutes = remaining / 60;
    int seconds = remaining % 60;
    
    // HHMMSSの形式で返す（最大99時間）
    hours = hours % 100;
    return hours * 10000 + minutes * 100 + seconds;
}

// 日数から年月日風の計算
int calc_days_to_date(int total_days) {
    int years = total_days / 365;
    int remaining = total_days % 365;
    int months = remaining / 30;
    int days = remaining % 30;
    
    return years * 10000 + months * 100 + days;
}

// 経過時間の計算
int calc_elapsed(int start, int end, int unit) {
    if (unit == 0) return 0;
    
    int diff = end - start;
    if (diff < 0) diff = -diff;
    
    int units = diff / unit;
    int remainder = diff % unit;
    int percent = remainder * 100 / unit;
    
    return units * 1000 + percent;
}

// ============================================================
// パターン13: エンコード・デコード風
// ============================================================

// 値のパッキング
int calc_pack_values(int a, int b, int c) {
    // 各値を制限
    int va = (a % 100 + 100) % 100;  // 0-99
    int vb = (b % 100 + 100) % 100;
    int vc = (c % 100 + 100) % 100;
    
    // パック: AABBCC形式
    int packed = va * 10000 + vb * 100 + vc;
    
    // チェックサム追加
    int checksum = (va + vb + vc) % 10;
    return packed * 10 + checksum;
}

// 値のアンパッキング（特定フィールド抽出）
int calc_unpack_field(int packed, int field_index) {
    // AABBCCDD形式から特定フィールドを抽出
    int divisors[] = {1, 100, 10000, 1000000};
    
    if (field_index < 0 || field_index > 3) return 0;
    
    int shifted = packed / divisors[field_index];
    int extracted = shifted % 100;
    
    // 前後の値との合計
    int prev = (field_index > 0) ? (packed / divisors[field_index-1]) % 100 : 0;
    
    return extracted * 10 + prev / 10;
}

// ============================================================
// パターン14: 複合代入と中間除算
// ============================================================

// 複合代入での段階的計算
int calc_compound_stages(int a, int b, int c) {
    if (b == 0 || c == 0) return 0;
    
    int result = a;
    result += 100;
    result *= 2;
    result /= b;
    result += 50;
    result %= c;
    result -= 25;
    result *= 3;
    
    return result;
}

// 交互の複合代入
int calc_compound_alternating(int a, int b) {
    if (b == 0) return 0;
    
    int x = a;
    int y = b;
    
    x += y;
    x /= 2;
    y *= 3;
    y %= x == 0 ? 1 : x;
    x -= y;
    x /= (y == 0 ? 1 : y);
    
    return x + y;
}

// ============================================================
// パターン15: 再帰的パターン（非再帰で実装）
// ============================================================

// フィボナッチ風計算と除算
int calc_fib_with_div(int n, int divisor) {
    if (divisor == 0) return 0;
    if (n <= 0) return 0;
    if (n == 1) return 1;
    
    int a = 0, b = 1;
    for (int i = 2; i <= n; i++) {
        int temp = (a + b) % divisor;
        a = b;
        b = temp;
    }
    
    int result = b + (a / (b == 0 ? 1 : b));
    return result;
}

// コラッツ風計算
int calc_collatz_steps(int n, int max_steps) {
    if (n <= 0) return 0;
    
    int steps = 0;
    int value = n;
    
    while (value != 1 && steps < max_steps) {
        if (value % 2 == 0) {
            value = value / 2;
        } else {
            value = value * 3 + 1;
            if (value > 1000000) value = value % 1000000;
        }
        steps++;
    }
    
    return steps * 100 + value % 100;
}

// ============================================================
// パターン16: 複数戻り値の模倣（上位・下位ビット）
// ============================================================

// 除算結果と剰余を合成して返す
int calc_divmod_combined_int(int a, int b) {
    if (b == 0) return 0;
    
    int quotient = a / b;
    int remainder = a % b;
    
    // 上位16ビット: 商、下位16ビット: 余り
    quotient = quotient & 0xFFFF;
    remainder = remainder & 0xFFFF;
    
    return (quotient << 16) | remainder;
}

// 複数の計算結果を合成
int calc_multi_result(int a, int b, int c) {
    if (b == 0 || c == 0) return 0;
    
    int div_result = (a / b) & 0xFF;
    int mod_result = (a % c) & 0xFF;
    int add_result = ((a + b + c) / 10) & 0xFF;
    
    return (div_result << 16) | (mod_result << 8) | add_result;
}

// ============================================================
// テスト用main関数
// ============================================================

int main() {
    int a = 12345, b = 67, c = 23, d = 11;
    int result = 0;
    
    // パターン1
    result += calc_add_div_mul(a, b, c);
    result += calc_mul_div_sub(a, b, c);
    result += calc_shift_mod_or(a, b, 0xF0);
    result += calc_and_div_xor(a, b, c);
    
    // パターン2
    result += calc_mixed_divmod(a, b, c);
    result += calc_alternating_ops(a, b, c, d);
    result += calc_divmod_parallel(a, b);
    
    // パターン3
    result += calc_accumulate_div(a, b, c, d);
    result += calc_accumulate_mod(a, b, c);
    result += calc_staged_accumulate(a, b, c);
    
    // パターン4
    result += calc_bit_div_bit(a, b);
    result += calc_complex_bit_mod(a, b, c);
    result += calc_sign_extend_div(a, b);
    
    // パターン5
    result += calc_cond_then_div(a, b, c);
    result += calc_div_then_cond(a, b);
    result += calc_div_in_cond(a, b, c);
    result += calc_multi_cond_div(a, b, c);
    
    // パターン6
    result += calc_loop_with_div(a, b, 10);
    result += calc_loop_mod_accumulate(a, b, 20);
    result += calc_nested_loop_div(10, b, c);
    
    // パターン7
    result += calc_average_deviation(a, b, c);
    result += calc_percent_rounded(a, 1000, 10);
    result += calc_ratio(a, b, 100);
    result += calc_factorial_approx(10, 1000);
    
    // パターン8
    result += calc_embedded_div(a, b, c);
    result += calc_nested_div_expr(a, b, c, d);
    result += calc_ternary_embedded(a, b, c);
    result += calc_func_like_expr(a, b, c);
    
    // パターン9
    int data[] = {100, 200, 300, 400, 500, 600, 700, 800};
    result += calc_array_index_div(data, 8, a, b);
    result += calc_2d_index(data, 4, 2, a, b);
    
    // パターン10
    result += calc_simple_hash(a, b, c);
    result += calc_checksum(data, 8);
    
    // パターン11
    result += calc_distance_approx(0, 0, a, b);
    result += calc_normalize_angle(a);
    result += calc_grid_position(a, b, 50, 100);
    
    // パターン12
    result += calc_seconds_to_hms(a);
    result += calc_days_to_date(a);
    result += calc_elapsed(b, a, c);
    
    // パターン13
    result += calc_pack_values(a, b, c);
    result += calc_unpack_field(a * 100 + b, 1);
    
    // パターン14
    result += calc_compound_stages(a, b, c);
    result += calc_compound_alternating(a, b);
    
    // パターン15
    result += calc_fib_with_div(20, b);
    result += calc_collatz_steps(a % 1000, 100);
    
    // パターン16
    result += calc_divmod_combined_int(a, b);
    result += calc_multi_result(a, b, c);
    
    return result % 256;
}