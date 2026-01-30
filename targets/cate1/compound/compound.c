/*
 * compound.c - 複合演算のテスト
 * 検証対象：LEA命令（x86）vs 複数命令（ARM）の差異
 */

// 単純な複合演算（元の要件通り）
int calc(int x) {
    return x * 3 + 5;
}

// 配列インデックス計算的な演算（LEA命令の典型的用途）
int array_index_calc(int base, int index, int element_size) {
    return base + index * element_size;
}

// スケール付き加算（x86のLEAで1命令になる）
int scaled_add(int x) {
    return x * 4 + 8;  // lea eax, [rdi*4+8] (x86)
}

// 2のべき乗スケール（シフトと加算の組み合わせ）
int power_of_two_scale(int x, int y) {
    return (x << 3) + y;  // x*8 + y
}

// 複数の複合演算
int multi_compound(int a, int b) {
    return (a * 2 + 10) + (b * 5 - 3);
}

// アドレス計算シミュレーション
int address_calc(int base_addr, int offset1, int offset2) {
    return base_addr + offset1 * 4 + offset2;
}

// ネストした複合演算
int nested_compound(int x) {
    int temp = x * 2 + 1;
    return temp * 3 + 7;
}

// 減算を含む複合演算
int compound_with_sub(int x, int y) {
    return x * 4 - y * 2 + 15;
}

// テスト用main関数
int main() {
    int x = 10, y = 20;
    int result = 0;
    
    result += calc(x);
    result += array_index_calc(1000, 5, 4);
    result += scaled_add(x);
    result += power_of_two_scale(x, y);
    result += multi_compound(x, y);
    result += address_calc(0x1000, 10, 5);
    result += nested_compound(x);
    result += compound_with_sub(x, y);
    
    return result;
}