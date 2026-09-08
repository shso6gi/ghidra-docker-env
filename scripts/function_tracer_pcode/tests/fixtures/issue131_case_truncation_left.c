/* Issue #131: MULTIEQUAL のケース数上限（既定 16）で実際に切り捨てが起きる形。
 *
 * 1 つの合流点（return する r）へ 19 通りの (guard, value) ケースが集まる。
 *   - switch の case 0..15 : guard は 1 条件、値は左右で同じ（生存する 16 件）
 *   - default の入れ子分岐 : guard が 2〜4 条件と長く、切り捨て対象になる 3 件
 *
 * 共通 dedup は条件列の短い順に上限件数だけ残すので、切り捨てられるのは default
 * 側の深い分岐だけになる。left/right はその default 側の値だけが異なるので、
 * 「切り捨てられたケースだけで観測結果が異なる」対を作れる。
 *
 * left が Eq 側（右と同じ値）、right が Neq 側（切り捨て対象だけ値が違う）。
 * どちらも未定義動作を含まず、返り値は入力領域全体で定義される。
 *
 * 実際に 17 件以上のケースが生成されるかはコンパイラ・最適化に依存する。
 * 生成された P-code と EXPANSION_BUDGET_DIAGNOSTIC_JSON で確認すること
 * （C の分岐数から 19 ケース生成は保証されない）。
 */

int f(int selector, int a, int b, int c)
{
    int r;

    switch (selector) {
    case 0:  r = 100; break;
    case 1:  r = 101; break;
    case 2:  r = 102; break;
    case 3:  r = 103; break;
    case 4:  r = 104; break;
    case 5:  r = 105; break;
    case 6:  r = 106; break;
    case 7:  r = 107; break;
    case 8:  r = 108; break;
    case 9:  r = 109; break;
    case 10: r = 110; break;
    case 11: r = 111; break;
    case 12: r = 112; break;
    case 13: r = 113; break;
    case 14: r = 114; break;
    case 15: r = 115; break;
    default:
        if (a != 0) {
            if (b != 0) {
                if (c != 0) {
                    r = 200;
                } else {
                    r = 201;
                }
            } else {
                r = 202;
            }
        } else {
            r = 203;
        }
        break;
    }

    return r;
}
