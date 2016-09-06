#include "AssociativeOpsTable.h"

using std::vector;

namespace Halide {
namespace Internal {

namespace {

const Type i32 = Int(32);
const Expr i32_zero = make_const(i32, 0);
const Expr i32_one = make_const(i32, 1);
const Expr i32_tmax = i32.max();
const Expr i32_tmin = i32.min();

const Expr i32_x0 = Variable::make(i32, "x0");
const Expr i32_y0 = Variable::make(i32, "y0");
const Expr i32_x1 = Variable::make(i32, "x1");
const Expr i32_y1 = Variable::make(i32, "y1");

const Expr i32_mul_x0y0 = Mul::make(i32_x0, i32_y0);
const Expr i32_mul_x0x0 = Mul::make(i32_x0, i32_x0);
const Expr i32_mul_y0y0 = Mul::make(i32_y0, i32_y0);
const Expr i32_add_x0y0 = Add::make(i32_x0, i32_y0);
const Expr i32_max_x0y0 = Max::make(i32_x0, i32_y0);
const Expr i32_min_x0y0 = Min::make(i32_x0, i32_y0);
const Expr i32_sub_x0y0 = Sub::make(i32_x0, i32_y0);
const Expr i32_sub_y0x0 = Sub::make(i32_y0, i32_x0);

const Expr i32_mul_x1y1 = Mul::make(i32_x1, i32_y1);
const Expr i32_mul_x1x1 = Mul::make(i32_x1, i32_x1);
const Expr i32_mul_y1y1 = Mul::make(i32_y1, i32_y1);
const Expr i32_add_x1y1 = Add::make(i32_x1, i32_y1);
const Expr i32_max_x1y1 = Max::make(i32_x1, i32_y1);
const Expr i32_min_x1y1 = Min::make(i32_x1, i32_y1);
const Expr i32_sub_x1y1 = Sub::make(i32_x1, i32_y1);
const Expr i32_sub_y1x1 = Sub::make(i32_y1, i32_x1);

const vector<vector<AssociativePair>> &get_single_i32_ops_table_add() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(27);
    if (!init) {
        exprs[0] = {{i32_add_x0y0, i32_zero}};
        exprs[1] = {{Add::make(Max::make(Min::make(i32_mul_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_x0), i32_zero}};
        exprs[2] = {{Add::make(Max::make(Min::make(Min::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[3] = {{Add::make(Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), k0), i32_y0), i32_x0), i32_zero}};
        exprs[4] = {{Add::make(Max::make(Min::make(Min::make(i32_mul_x0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[5] = {{Add::make(Max::make(Min::make(Min::make(i32_mul_x0y0, i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[6] = {{Add::make(Max::make(Min::make(Min::make(i32_sub_y0x0, i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[7] = {{Add::make(Max::make(Min::make(i32_sub_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_x0), i32_zero}};
        exprs[8] = {{Add::make(Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[9] = {{Add::make(Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_y0), i32_y0)), i32_y0), i32_x0), i32_zero}};
        exprs[10] = {{Add::make(Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, k0)), i32_y0), i32_x0), i32_zero}};
        exprs[11] = {{Add::make(Max::make(Sub::make(i32_y0, Max::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[12] = {{Add::make(Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_zero}};
        exprs[13] = {{Add::make(Min::make(Max::make(i32_mul_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_x0), i32_zero}};
        exprs[14] = {{Add::make(Min::make(Max::make(Max::make(i32_mul_x0y0, i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[15] = {{Add::make(Min::make(Max::make(Max::make(i32_mul_x0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[16] = {{Add::make(Min::make(Max::make(Max::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[17] = {{Add::make(Min::make(Max::make(Max::make(i32_sub_y0x0, i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[18] = {{Add::make(Min::make(Max::make(i32_sub_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_x0), i32_zero}};
        exprs[19] = {{Add::make(Min::make(Sub::make(Max::make(Add::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[20] = {{Add::make(Min::make(i32_sub_y0x0, k0), Max::make(Sub::make(i32_y0, k0), i32_x0)), -1}};
        exprs[21] = {{Add::make(Min::make(Sub::make(i32_y0, k0), i32_x0), Max::make(i32_sub_y0x0, k0)), i32_zero}};
        exprs[22] = {{Add::make(Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, k0)), i32_y0), i32_x0), i32_zero}};
        exprs[23] = {{Add::make(Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[24] = {{Add::make(Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_y0), i32_y0)), i32_y0), i32_x0), i32_zero}};
        exprs[25] = {{Add::make(Min::make(Sub::make(i32_y0, Min::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[26] = {{Add::make(Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_zero}};
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_single_i32_ops_table_mul() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(21);
    if (!init) {
        exprs[0] = {{i32_mul_x0y0, i32_one}};
        exprs[1] = {{Mul::make(Max::make(Min::make(i32_mul_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_x0), i32_one}};
        exprs[2] = {{Mul::make(Max::make(Min::make(Min::make(i32_mul_x0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_one}};
        exprs[3] = {{Mul::make(Max::make(Min::make(Min::make(i32_mul_x0y0, i32_x0), k0), i32_x0), i32_y0), i32_one}};
        exprs[4] = {{Mul::make(Max::make(Min::make(Min::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_one}};
        exprs[5] = {{Mul::make(Max::make(Min::make(Min::make(i32_sub_y0x0, i32_x0), k0), i32_x0), i32_y0), i32_one}};
        exprs[6] = {{Mul::make(Max::make(Min::make(i32_sub_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_x0), i32_one}};
        exprs[7] = {{Mul::make(Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_one}};
        exprs[8] = {{Mul::make(Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_one}};
        exprs[9] = {{Mul::make(Max::make(Sub::make(i32_y0, Max::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_one}};
        exprs[10] = {{Mul::make(Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, k0)), i32_y0), i32_x0), i32_one}};
        exprs[11] = {{Mul::make(Min::make(Max::make(i32_mul_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_x0), i32_one}};
        exprs[12] = {{Mul::make(Min::make(Max::make(Max::make(i32_mul_x0y0, i32_x0), k0), i32_x0), i32_y0), i32_one}};
        exprs[13] = {{Mul::make(Min::make(Max::make(Max::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_one}};
        exprs[14] = {{Mul::make(Min::make(Max::make(Max::make(i32_mul_x0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_one}};
        exprs[15] = {{Mul::make(Min::make(Max::make(Max::make(i32_sub_y0x0, i32_x0), k0), i32_x0), i32_y0), i32_one}};
        exprs[16] = {{Mul::make(Min::make(Max::make(i32_sub_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_x0), i32_one}};
        exprs[17] = {{Mul::make(Min::make(Sub::make(Max::make(i32_add_x0y0, k0), i32_y0), i32_x0), i32_y0), i32_one}};
        exprs[18] = {{Mul::make(Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_one}};
        exprs[19] = {{Mul::make(Min::make(Sub::make(i32_y0, Min::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_one}};
        exprs[20] = {{Mul::make(Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_one}};
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_single_i32_ops_table_max() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(292);
    if (!init) {
        exprs[0] = {{i32_max_x0y0, i32_tmin}};
        exprs[1] = {{Max::make(Add::make(i32_min_x0y0, Min::make(i32_y0, k0)), i32_add_x0y0), i32_zero}};
        exprs[2] = {{Max::make(Add::make(Min::make(i32_x0, k0), Min::make(i32_y0, k0)), i32_add_x0y0), i32_zero}};
        exprs[3] = {{Max::make(Add::make(i32_min_x0y0, Min::make(i32_x0, k0)), i32_add_x0y0), i32_zero}};
        exprs[4] = {{Max::make(Add::make(Min::make(Sub::make(i32_y0, Max::make(i32_x0, k0)), i32_x0), k0), i32_y0), i32_zero}};
        exprs[5] = {{Max::make(Add::make(Min::make(Sub::make(i32_y0, Max::make(i32_x0, k0)), i32_x0), i32_x0), i32_y0), i32_tmax}};
        exprs[6] = {{Max::make(Add::make(Min::make(i32_sub_y0x0, i32_x0), i32_min_x0y0), i32_y0), -2}};
        exprs[7] = {{Max::make(Add::make(Min::make(Sub::make(i32_y0, k0), i32_x0), Min::make(i32_x0, k0)), i32_y0), i32_tmax}};
        exprs[8] = {{Max::make(Add::make(Min::make(i32_sub_y0x0, i32_x0), Min::make(i32_x0, k0)), i32_y0), -1}};
        exprs[9] = {{Max::make(Add::make(Min::make(Sub::make(i32_y0, k0), i32_x0), Min::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[10] = {{Max::make(Add::make(Min::make(i32_sub_y0x0, i32_x0), Min::make(i32_y0, i32_x0)), i32_y0), i32_zero}};
        exprs[11] = {{Max::make(Add::make(Min::make(i32_sub_y0x0, k0), i32_min_x0y0), i32_y0), i32_one}};
        exprs[12] = {{Max::make(Add::make(Min::make(i32_sub_y0x0, k0), Min::make(i32_x0, k0)), i32_y0), i32_one}};
        exprs[13] = {{Max::make(Add::make(Min::make(i32_sub_y0x0, k0), Min::make(i32_y0, i32_x0)), i32_y0), i32_zero}};
        exprs[14] = {{Max::make(Add::make(Sub::make(i32_y0, Max::make(Mul::make(i32_y0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[15] = {{Max::make(Add::make(Sub::make(i32_y0, Max::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[16] = {{Max::make(Add::make(Sub::make(Min::make(i32_y0, i32_x0), Max::make(i32_y0, i32_x0)), i32_y0), i32_y0), i32_tmin}};
        exprs[17] = {{Max::make(Add::make(Sub::make(i32_min_x0y0, i32_max_x0y0), i32_x0), i32_y0), i32_zero}};
        exprs[18] = {{Max::make(Add::make(Sub::make(i32_min_x0y0, Max::make(i32_x0, k0)), i32_y0), i32_y0), i32_zero}};
        exprs[19] = {{Max::make(Add::make(Sub::make(Min::make(i32_y0, i32_x0), Max::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[20] = {{Max::make(Max::make(Min::make(Add::make(Mul::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[21] = {{Max::make(Max::make(Min::make(Add::make(i32_mul_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[22] = {{Max::make(Max::make(Min::make(Add::make(i32_mul_x0x0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[23] = {{Max::make(Max::make(Min::make(Add::make(i32_max_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[24] = {{Max::make(Max::make(Min::make(Add::make(i32_max_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[25] = {{Max::make(Max::make(Min::make(Add::make(i32_max_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[26] = {{Max::make(Max::make(Min::make(Add::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[27] = {{Max::make(Max::make(Min::make(Add::make(i32_max_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[28] = {{Max::make(Max::make(Min::make(Add::make(Max::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[29] = {{Max::make(Max::make(Min::make(Add::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[30] = {{Max::make(Max::make(Min::make(Add::make(i32_min_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[31] = {{Max::make(Max::make(Min::make(Add::make(i32_min_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[32] = {{Max::make(Max::make(Min::make(Add::make(Min::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[33] = {{Max::make(Max::make(Min::make(Add::make(i32_min_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[34] = {{Max::make(Max::make(Min::make(Add::make(i32_min_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[35] = {{Max::make(Max::make(Min::make(i32_mul_x0y0, i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[36] = {{Max::make(Max::make(Min::make(i32_mul_x0y0, i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[37] = {{Max::make(Max::make(Min::make(Mul::make(i32_add_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[38] = {{Max::make(Max::make(Min::make(Mul::make(i32_add_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[39] = {{Max::make(Max::make(Min::make(Mul::make(i32_add_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[40] = {{Max::make(Max::make(Min::make(Mul::make(i32_add_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[41] = {{Max::make(Max::make(Min::make(Mul::make(i32_max_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[42] = {{Max::make(Max::make(Min::make(Mul::make(i32_max_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[43] = {{Max::make(Max::make(Min::make(Mul::make(Max::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[44] = {{Max::make(Max::make(Min::make(Mul::make(i32_max_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[45] = {{Max::make(Max::make(Min::make(Mul::make(i32_max_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[46] = {{Max::make(Max::make(Min::make(Mul::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[47] = {{Max::make(Max::make(Min::make(i32_mul_x0y0, Min::make(i32_y0, k0)), i32_x0), i32_y0), i32_tmin}};
        exprs[48] = {{Max::make(Max::make(Min::make(Mul::make(i32_min_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[49] = {{Max::make(Max::make(Min::make(Mul::make(i32_min_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[50] = {{Max::make(Max::make(Min::make(Mul::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[51] = {{Max::make(Max::make(Min::make(Mul::make(i32_min_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[52] = {{Max::make(Max::make(Min::make(Mul::make(i32_min_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[53] = {{Max::make(Max::make(Min::make(Mul::make(Min::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[54] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_y0x0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[55] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[56] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[57] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[58] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[59] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_y0x0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[60] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_y0x0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[61] = {{Max::make(Max::make(Min::make(Mul::make(i32_sub_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[62] = {{Max::make(Max::make(Min::make(Max::make(i32_add_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[63] = {{Max::make(Max::make(Min::make(Max::make(i32_mul_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[64] = {{Max::make(Max::make(Min::make(Max::make(i32_sub_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[65] = {{Max::make(Max::make(Min::make(Max::make(i32_sub_y0x0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[66] = {{Max::make(Max::make(Min::make(Min::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[67] = {{Max::make(Max::make(Min::make(Min::make(i32_sub_y0x0, i32_x0), k0), i32_y0), i32_x0), i32_tmin}};
        exprs[68] = {{Max::make(Max::make(Min::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[69] = {{Max::make(Max::make(Min::make(i32_sub_x0y0, i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[70] = {{Max::make(Max::make(Min::make(Sub::make(Add::make(k0, i32_y0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[71] = {{Max::make(Max::make(Min::make(Sub::make(i32_mul_x0x0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[72] = {{Max::make(Max::make(Min::make(Sub::make(i32_y0, Mul::make(i32_x0, k0)), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[73] = {{Max::make(Max::make(Min::make(Sub::make(i32_mul_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[74] = {{Max::make(Max::make(Min::make(Sub::make(k0, i32_mul_x0y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[75] = {{Max::make(Max::make(Min::make(Sub::make(Mul::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[76] = {{Max::make(Max::make(Min::make(Sub::make(Mul::make(i32_x0, k0), i32_y0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[77] = {{Max::make(Max::make(Min::make(Sub::make(i32_mul_y0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[78] = {{Max::make(Max::make(Min::make(Sub::make(i32_y0, i32_mul_x0x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[79] = {{Max::make(Max::make(Min::make(Sub::make(Max::make(i32_y0, k0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[80] = {{Max::make(Max::make(Min::make(Sub::make(i32_max_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[81] = {{Max::make(Max::make(Min::make(Sub::make(Max::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[82] = {{Max::make(Max::make(Min::make(Sub::make(i32_y0, Max::make(i32_x0, k0)), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[83] = {{Max::make(Max::make(Min::make(Sub::make(k0, i32_max_x0y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[84] = {{Max::make(Max::make(Min::make(Sub::make(Min::make(i32_y0, k0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[85] = {{Max::make(Max::make(Min::make(Sub::make(Min::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[86] = {{Max::make(Max::make(Min::make(Sub::make(i32_min_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[87] = {{Max::make(Max::make(Min::make(Sub::make(i32_y0, Min::make(i32_x0, k0)), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[88] = {{Max::make(Max::make(Min::make(i32_sub_x0y0, Min::make(i32_y0, k0)), i32_x0), i32_y0), i32_tmin}};
        exprs[89] = {{Max::make(Max::make(Min::make(Sub::make(k0, i32_min_x0y0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[90] = {{Max::make(Max::make(Min::make(Sub::make(Sub::make(k0, i32_y0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[91] = {{Max::make(Max::make(Min::make(Sub::make(Sub::make(i32_y0, k0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmin}};
        exprs[92] = {{Max::make(Max::make(Sub::make(i32_y0, Max::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[93] = {{Max::make(Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_tmin}};
        exprs[94] = {{Max::make(Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[95] = {{Max::make(Min::make(i32_x0, k0), i32_y0), i32_tmin}};
        exprs[96] = {{Max::make(Min::make(Add::make(Max::make(i32_sub_x0y0, i32_y0), i32_x0), i32_x0), i32_y0), i32_tmin}};
        exprs[97] = {{Max::make(Min::make(Add::make(Max::make(i32_sub_x0y0, k0), i32_x0), i32_x0), i32_y0), i32_tmin}};
        exprs[98] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, k0), i32_x0), k0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[99] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, k0), i32_x0), i32_y0), i32_add_x0y0), i32_zero}};
        exprs[100] = {{Max::make(Min::make(Add::make(i32_min_x0y0, i32_x0), k0), i32_add_x0y0), i32_zero}};
        exprs[101] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[102] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, k0), i32_x0), k0), i32_add_x0y0), i32_zero}};
        exprs[103] = {{Max::make(Min::make(Add::make(i32_min_x0y0, i32_x0), i32_y0), i32_add_x0y0), i32_zero}};
        exprs[104] = {{Max::make(Min::make(Add::make(i32_min_x0y0, i32_y0), i32_y0), i32_add_x0y0), i32_zero}};
        exprs[105] = {{Max::make(Min::make(Add::make(i32_min_x0y0, i32_x0), i32_x0), i32_add_x0y0), i32_zero}};
        exprs[106] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, k0), i32_x0), i32_y0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[107] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_x0), k0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[108] = {{Max::make(Min::make(Add::make(i32_min_x0y0, i32_x0), i32_sub_y0x0), i32_y0), i32_zero}};
        exprs[109] = {{Max::make(Min::make(Add::make(Min::make(Sub::make(i32_y0, k0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[110] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), k0), Sub::make(i32_y0, k0)), i32_y0), -1}};
        exprs[111] = {{Max::make(Min::make(Add::make(Min::make(i32_sub_y0x0, k0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[112] = {{Max::make(Min::make(Add::make(Min::make(i32_x0, k0), Sub::make(k0, i32_y0)), i32_x0), i32_y0), i32_tmin}};
        exprs[113] = {{Max::make(Min::make(Add::make(i32_min_x0y0, k0), Sub::make(i32_y0, k0)), i32_y0), i32_one}};
        exprs[114] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, k0), i32_x0), i32_sub_y0x0), i32_y0), i32_zero}};
        exprs[115] = {{Max::make(Min::make(Add::make(Min::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[116] = {{Max::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_x0), i32_sub_y0x0), i32_y0), i32_zero}};
        exprs[117] = {{Max::make(Min::make(i32_mul_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[118] = {{Max::make(Min::make(Mul::make(i32_sub_y0x0, i32_y0), Min::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[119] = {{Max::make(Min::make(Max::make(i32_mul_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_x0), i32_tmin}};
        exprs[120] = {{Max::make(Min::make(Max::make(Max::make(i32_mul_x0y0, i32_x0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[121] = {{Max::make(Min::make(Max::make(Max::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[122] = {{Max::make(Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), k0), i32_y0), i32_x0), i32_tmin}};
        exprs[123] = {{Max::make(Min::make(Max::make(Max::make(i32_sub_y0x0, i32_x0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[124] = {{Max::make(Min::make(Max::make(Min::make(Add::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[125] = {{Max::make(Min::make(Max::make(Min::make(Add::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[126] = {{Max::make(Min::make(Max::make(Min::make(Mul::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[127] = {{Max::make(Min::make(Max::make(Min::make(Mul::make(i32_y0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[128] = {{Max::make(Min::make(Max::make(Min::make(Mul::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[129] = {{Max::make(Min::make(Max::make(Min::make(i32_mul_y0y0, i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[130] = {{Max::make(Min::make(Max::make(Min::make(Mul::make(i32_y0, i32_x0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[131] = {{Max::make(Min::make(Max::make(Min::make(i32_mul_y0y0, i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[132] = {{Max::make(Min::make(Max::make(Min::make(Mul::make(i32_y0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[133] = {{Max::make(Min::make(Max::make(Min::make(i32_mul_x0y0, i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[134] = {{Max::make(Min::make(Max::make(Min::make(i32_mul_x0x0, i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[135] = {{Max::make(Min::make(Max::make(Min::make(i32_mul_x0x0, i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[136] = {{Max::make(Min::make(Max::make(Min::make(i32_y0, i32_x0), k0), Max::make(i32_y0, i32_x0)), i32_y0), i32_tmin}};
        exprs[137] = {{Max::make(Min::make(Max::make(Min::make(i32_y0, k0), i32_x0), Max::make(i32_y0, k0)), i32_y0), i32_tmin}};
        exprs[138] = {{Max::make(Min::make(Max::make(i32_min_x0y0, k0), i32_max_x0y0), i32_y0), i32_tmin}};
        exprs[139] = {{Max::make(Min::make(Max::make(Min::make(Sub::make(k0, i32_x0), i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[140] = {{Max::make(Min::make(Max::make(Min::make(Sub::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[141] = {{Max::make(Min::make(Max::make(Min::make(Sub::make(k0, i32_y0), i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[142] = {{Max::make(Min::make(Max::make(Min::make(i32_y0, k0), Sub::make(k0, i32_y0)), i32_x0), i32_y0), i32_tmin}};
        exprs[143] = {{Max::make(Min::make(Max::make(Min::make(Sub::make(k0, i32_y0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[144] = {{Max::make(Min::make(Max::make(Min::make(i32_y0, k0), i32_x0), Sub::make(k0, i32_y0)), i32_y0), i32_tmin}};
        exprs[145] = {{Max::make(Min::make(Max::make(Min::make(i32_sub_x0y0, i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[146] = {{Max::make(Min::make(Max::make(Min::make(Sub::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[147] = {{Max::make(Min::make(Max::make(Min::make(Sub::make(k0, i32_x0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[148] = {{Max::make(Min::make(Max::make(Min::make(i32_sub_x0y0, i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[149] = {{Max::make(Min::make(Max::make(i32_sub_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_x0), i32_tmin}};
        exprs[150] = {{Max::make(Min::make(Max::make(Sub::make(Min::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[151] = {{Max::make(Min::make(Min::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[152] = {{Max::make(Min::make(Min::make(Add::make(Max::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[153] = {{Max::make(Min::make(Min::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[154] = {{Max::make(Min::make(Min::make(Add::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[155] = {{Max::make(Min::make(Min::make(Add::make(i32_max_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[156] = {{Max::make(Min::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[157] = {{Max::make(Min::make(Min::make(Add::make(i32_min_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[158] = {{Max::make(Min::make(Min::make(Add::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[159] = {{Max::make(Min::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[160] = {{Max::make(Min::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[161] = {{Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[162] = {{Max::make(Min::make(Min::make(Mul::make(Add::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[163] = {{Max::make(Min::make(Min::make(Mul::make(Add::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[164] = {{Max::make(Min::make(Min::make(Mul::make(i32_add_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[165] = {{Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), Add::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[166] = {{Max::make(Min::make(Min::make(Mul::make(i32_add_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[167] = {{Max::make(Min::make(Min::make(Mul::make(Add::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[168] = {{Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), i32_mul_x0x0), i32_y0), i32_zero}};
        exprs[169] = {{Max::make(Min::make(Min::make(Mul::make(i32_mul_y0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[170] = {{Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), Mul::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[171] = {{Max::make(Min::make(Min::make(i32_mul_x0y0, i32_x0), i32_y0), i32_mul_x0y0), i32_one}};
        exprs[172] = {{Max::make(Min::make(Min::make(Mul::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[173] = {{Max::make(Min::make(Min::make(Mul::make(Max::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[174] = {{Max::make(Min::make(Min::make(Mul::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[175] = {{Max::make(Min::make(Min::make(Mul::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[176] = {{Max::make(Min::make(Min::make(Mul::make(i32_max_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[177] = {{Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), Min::make(k0, i32_x0)), i32_y0), i32_zero}};
        exprs[178] = {{Max::make(Min::make(Min::make(Mul::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[179] = {{Max::make(Min::make(Min::make(Mul::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[180] = {{Max::make(Min::make(Min::make(Mul::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[181] = {{Max::make(Min::make(Min::make(Mul::make(Min::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[182] = {{Max::make(Min::make(Min::make(Mul::make(i32_min_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[183] = {{Max::make(Min::make(Min::make(Mul::make(i32_sub_y0x0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[184] = {{Max::make(Min::make(Min::make(Mul::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[185] = {{Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), Sub::make(k0, i32_x0)), i32_y0), i32_zero}};
        exprs[186] = {{Max::make(Min::make(Min::make(Mul::make(i32_sub_y0x0, i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[187] = {{Max::make(Min::make(Min::make(Mul::make(i32_sub_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[188] = {{Max::make(Min::make(Min::make(Mul::make(i32_sub_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[189] = {{Max::make(Min::make(Min::make(Mul::make(i32_sub_x0y0, i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[190] = {{Max::make(Min::make(Min::make(Mul::make(Sub::make(k0, i32_y0), k0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[191] = {{Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), Sub::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[192] = {{Max::make(Min::make(Min::make(Max::make(Mul::make(i32_x0, k0), i32_x0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[193] = {{Max::make(Min::make(Min::make(Max::make(i32_mul_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[194] = {{Max::make(Min::make(Min::make(Max::make(Mul::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[195] = {{Max::make(Min::make(Min::make(Max::make(i32_mul_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[196] = {{Max::make(Min::make(Min::make(Max::make(i32_mul_y0y0, k0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[197] = {{Max::make(Min::make(Min::make(Max::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[198] = {{Max::make(Min::make(Min::make(Max::make(Sub::make(k0, i32_x0), i32_x0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[199] = {{Max::make(Min::make(Min::make(Max::make(i32_sub_y0x0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[200] = {{Max::make(Min::make(Min::make(Max::make(i32_y0, k0), Sub::make(k0, i32_y0)), i32_x0), i32_y0), i32_tmin}};
        exprs[201] = {{Max::make(Min::make(Min::make(Min::make(Mul::make(i32_y0, i32_x0), i32_y0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[202] = {{Max::make(Min::make(Min::make(i32_sub_x0y0, i32_y0), k0), i32_y0), i32_zero}};
        exprs[203] = {{Max::make(Min::make(Min::make(Sub::make(i32_mul_x0x0, i32_y0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[204] = {{Max::make(Min::make(Sub::make(k0, i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[205] = {{Max::make(Min::make(Sub::make(Add::make(Max::make(i32_x0, k0), i32_x0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[206] = {{Max::make(Min::make(Sub::make(Add::make(Min::make(i32_y0, k0), i32_y0), i32_x0), i32_x0), i32_y0), i32_tmin}};
        exprs[207] = {{Max::make(Min::make(Sub::make(k0, Add::make(Min::make(i32_y0, i32_x0), i32_y0)), i32_x0), i32_y0), i32_tmin}};
        exprs[208] = {{Max::make(Min::make(Sub::make(i32_y0, i32_mul_x0x0), i32_mul_x0x0), i32_y0), i32_zero}};
        exprs[209] = {{Max::make(Min::make(Sub::make(i32_mul_y0y0, i32_x0), Min::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[210] = {{Max::make(Min::make(Sub::make(i32_x0, i32_mul_y0y0), Min::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[211] = {{Max::make(Min::make(Sub::make(Max::make(Add::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[212] = {{Max::make(Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), k0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[213] = {{Max::make(Min::make(Sub::make(Max::make(i32_add_x0y0, k0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[214] = {{Max::make(Min::make(Sub::make(Max::make(Min::make(i32_y0, i32_x0), k0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[215] = {{Max::make(Min::make(Sub::make(Max::make(i32_y0, k0), i32_min_x0y0), i32_x0), i32_y0), i32_tmin}};
        exprs[216] = {{Max::make(Min::make(Sub::make(Max::make(i32_min_x0y0, k0), i32_y0), i32_x0), i32_y0), i32_tmin}};
        exprs[217] = {{Max::make(Min::make(Sub::make(Max::make(i32_y0, k0), Min::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[218] = {{Max::make(Min::make(Sub::make(Max::make(i32_sub_x0y0, i32_y0), i32_x0), i32_x0), i32_y0), -2147483647}};
        exprs[219] = {{Max::make(Min::make(Sub::make(i32_y0, Max::make(i32_sub_x0y0, k0)), i32_x0), i32_y0), i32_tmin}};
        exprs[220] = {{Max::make(Min::make(Sub::make(k0, Max::make(Sub::make(k0, i32_y0), i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[221] = {{Max::make(Min::make(Sub::make(k0, Max::make(Sub::make(k0, i32_x0), i32_y0)), i32_x0), i32_y0), i32_tmin}};
        exprs[222] = {{Max::make(Min::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_y0)), k0), i32_y0), i32_zero}};
        exprs[223] = {{Max::make(Min::make(Sub::make(k0, Max::make(Sub::make(k0, i32_y0), i32_y0)), i32_x0), i32_y0), i32_zero}};
        exprs[224] = {{Max::make(Min::make(i32_sub_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[225] = {{Max::make(Min::make(Sub::make(k0, Min::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[226] = {{Max::make(Min::make(Sub::make(Min::make(i32_y0, k0), i32_x0), Add::make(i32_y0, i32_x0)), i32_y0), i32_zero}};
        exprs[227] = {{Max::make(Min::make(Sub::make(i32_min_x0y0, k0), Add::make(i32_y0, k0)), i32_y0), i32_one}};
        exprs[228] = {{Max::make(Min::make(Sub::make(Min::make(i32_y0, k0), i32_x0), i32_add_x0y0), i32_y0), i32_zero}};
        exprs[229] = {{Max::make(Min::make(Sub::make(Min::make(i32_y0, i32_x0), k0), Add::make(i32_y0, k0)), i32_y0), -1}};
        exprs[230] = {{Max::make(Min::make(Sub::make(k0, Min::make(Max::make(i32_x0, k0), i32_y0)), i32_x0), i32_y0), i32_tmin}};
        exprs[231] = {{Max::make(Min::make(Sub::make(Min::make(i32_y0, k0), Min::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[232] = {{Max::make(Min::make(Sub::make(Min::make(i32_y0, k0), i32_min_x0y0), i32_x0), i32_y0), i32_tmin}};
        exprs[233] = {{Max::make(Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_y0), i32_y0)), i32_y0), i32_x0), i32_tmin}};
        exprs[234] = {{Max::make(Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_tmin}};
        exprs[235] = {{Max::make(Min::make(Sub::make(i32_y0, Min::make(i32_sub_y0x0, k0)), i32_x0), i32_y0), i32_tmin}};
        exprs[236] = {{Max::make(Min::make(Sub::make(i32_y0, Min::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[237] = {{Max::make(Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_y0), i32_y0)), i32_x0), i32_y0), i32_tmin}};
        exprs[238] = {{Max::make(Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_tmin}};
        exprs[239] = {{Max::make(Min::make(Sub::make(Sub::make(k0, i32_y0), i32_min_x0y0), i32_x0), i32_y0), i32_tmin}};
        exprs[240] = {{Max::make(Sub::make(Add::make(Min::make(Mul::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[241] = {{Max::make(Sub::make(Add::make(Min::make(i32_y0, i32_x0), i32_y0), Max::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[242] = {{Max::make(Sub::make(Add::make(Min::make(i32_y0, k0), i32_y0), Max::make(i32_x0, k0)), i32_y0), i32_one}};
        exprs[243] = {{Max::make(Sub::make(Add::make(Min::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), -1392654478}};
        exprs[244] = {{Max::make(Sub::make(k0, Max::make(Add::make(i32_y0, i32_x0), Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[245] = {{Max::make(Sub::make(Max::make(i32_x0, k0), Max::make(Sub::make(k0, i32_y0), i32_x0)), i32_x0), i32_tmin}};
        exprs[246] = {{Max::make(Sub::make(i32_x0, Max::make(Min::make(i32_y0, k0), i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[247] = {{Max::make(Sub::make(k0, Max::make(Min::make(i32_y0, i32_x0), Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[248] = {{Max::make(Sub::make(k0, Max::make(i32_min_x0y0, Sub::make(k0, i32_y0))), i32_x0), i32_tmin}};
        exprs[249] = {{Max::make(Sub::make(k0, Max::make(Min::make(i32_x0, k0), Sub::make(k0, i32_y0))), i32_y0), i32_tmin}};
        exprs[250] = {{Max::make(Sub::make(k0, Max::make(Min::make(i32_x0, k0), Sub::make(k0, i32_y0))), i32_x0), i32_tmin}};
        exprs[251] = {{Max::make(Sub::make(i32_x0, Max::make(i32_min_x0y0, i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[252] = {{Max::make(Sub::make(i32_x0, Max::make(Min::make(i32_y0, i32_x0), i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[253] = {{Max::make(Sub::make(k0, Max::make(i32_min_x0y0, Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[254] = {{Max::make(Sub::make(i32_x0, Max::make(Min::make(i32_x0, k0), i32_sub_x0y0)), i32_y0), -1053032432}};
        exprs[255] = {{Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_y0), i32_x0)), i32_y0), i32_tmin}};
        exprs[256] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_zero}};
        exprs[257] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, k0)), i32_y0), -1}};
        exprs[258] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, Add::make(i32_y0, k0))), i32_y0), i32_zero}};
        exprs[259] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, Mul::make(i32_y0, i32_x0))), i32_y0), i32_tmin}};
        exprs[260] = {{Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_y0), i32_mul_x0x0)), i32_y0), i32_zero}};
        exprs[261] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_mul_y0y0)), i32_y0), i32_zero}};
        exprs[262] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_mul_x0x0)), i32_y0), -1710971863}};
        exprs[263] = {{Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_max_x0y0), i32_x0)), i32_x0), i32_tmin}};
        exprs[264] = {{Max::make(Sub::make(i32_x0, Max::make(Sub::make(Max::make(i32_x0, k0), i32_y0), i32_y0)), i32_y0), i32_tmax}};
        exprs[265] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, Max::make(i32_y0, k0))), i32_y0), -1}};
        exprs[266] = {{Max::make(Sub::make(k0, Max::make(Sub::make(Max::make(i32_x0, k0), i32_y0), i32_y0)), i32_y0), i32_tmin}};
        exprs[267] = {{Max::make(Sub::make(k0, Max::make(Sub::make(k0, Min::make(i32_y0, i32_x0)), i32_y0)), i32_y0), 2147483646}};
        exprs[268] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, Sub::make(k0, i32_x0))), i32_y0), -1}};
        exprs[269] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_sub_y0x0)), i32_y0), i32_zero}};
        exprs[270] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_y0x0, i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[271] = {{Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, Sub::make(i32_y0, k0))), i32_y0), -1}};
        exprs[272] = {{Max::make(Sub::make(k0, Max::make(i32_sub_y0x0, Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[273] = {{Max::make(Sub::make(Min::make(i32_add_x0y0, k0), Max::make(i32_x0, k0)), i32_y0), -1}};
        exprs[274] = {{Max::make(Sub::make(Min::make(Add::make(i32_y0, k0), i32_x0), Max::make(i32_y0, k0)), i32_y0), i32_tmax}};
        exprs[275] = {{Max::make(Sub::make(Min::make(Add::make(i32_y0, k0), i32_x0), Max::make(i32_x0, k0)), i32_y0), -1}};
        exprs[276] = {{Max::make(Sub::make(Min::make(Add::make(i32_y0, i32_x0), k0), Max::make(i32_y0, i32_x0)), i32_y0), i32_one}};
        exprs[277] = {{Max::make(Sub::make(Min::make(i32_add_x0y0, k0), i32_max_x0y0), i32_y0), -1}};
        exprs[278] = {{Max::make(Sub::make(Min::make(Add::make(i32_y0, i32_x0), k0), Max::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[279] = {{Max::make(Sub::make(Min::make(Add::make(Min::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_one}};
        exprs[280] = {{Max::make(Sub::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_y0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[281] = {{Max::make(Sub::make(Min::make(Add::make(Min::make(i32_y0, i32_x0), i32_y0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[282] = {{Max::make(Sub::make(Min::make(Add::make(Min::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[283] = {{Max::make(Sub::make(Min::make(i32_x0, k0), Max::make(i32_sub_x0y0, k0)), i32_y0), i32_one}};
        exprs[284] = {{Max::make(Sub::make(Min::make(i32_y0, k0), Max::make(Sub::make(k0, i32_y0), i32_x0)), i32_y0), i32_zero}};
        exprs[285] = {{Max::make(Sub::make(Min::make(i32_y0, i32_x0), Max::make(i32_sub_x0y0, k0)), i32_y0), -1}};
        exprs[286] = {{Max::make(Sub::make(Min::make(i32_y0, i32_x0), Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_tmin}};
        exprs[287] = {{Max::make(Sub::make(Min::make(i32_x0, k0), Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_tmin}};
        exprs[288] = {{Max::make(Sub::make(i32_min_x0y0, Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_tmin}};
        exprs[289] = {{Max::make(Sub::make(i32_min_x0y0, Max::make(i32_sub_x0y0, k0)), i32_y0), i32_one}};
        exprs[290] = {{Max::make(Sub::make(Min::make(i32_x0, k0), Max::make(Sub::make(k0, i32_y0), i32_x0)), i32_y0), i32_zero}};
        exprs[291] = {{Max::make(Sub::make(Min::make(i32_x0, k0), Max::make(Sub::make(k0, i32_y0), i32_y0)), i32_y0), i32_tmax}};
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_single_i32_ops_table_min() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(323);
    if (!init) {
        exprs[0] = {{i32_min_x0y0, i32_tmax}};
        exprs[1] = {{Min::make(Add::make(Max::make(i32_x0, k0), Max::make(i32_y0, k0)), i32_add_x0y0), i32_zero}};
        exprs[2] = {{Min::make(Add::make(i32_max_x0y0, Max::make(i32_y0, k0)), i32_add_x0y0), i32_zero}};
        exprs[3] = {{Min::make(Add::make(i32_max_x0y0, Max::make(i32_x0, k0)), i32_add_x0y0), i32_zero}};
        exprs[4] = {{Min::make(Add::make(Max::make(Sub::make(i32_y0, k0), i32_x0), Max::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[5] = {{Min::make(Add::make(Max::make(i32_sub_y0x0, k0), Max::make(i32_x0, k0)), i32_y0), -1}};
        exprs[6] = {{Min::make(Add::make(Max::make(i32_sub_y0x0, k0), i32_max_x0y0), i32_y0), -1}};
        exprs[7] = {{Min::make(Add::make(Max::make(i32_sub_y0x0, i32_x0), i32_max_x0y0), i32_y0), 2}};
        exprs[8] = {{Min::make(Add::make(Max::make(i32_sub_y0x0, i32_x0), Max::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[9] = {{Min::make(Add::make(Max::make(Sub::make(i32_y0, k0), i32_x0), Max::make(i32_x0, k0)), i32_y0), i32_tmin}};
        exprs[10] = {{Min::make(Add::make(Max::make(i32_sub_y0x0, k0), Max::make(i32_y0, i32_x0)), i32_y0), i32_zero}};
        exprs[11] = {{Min::make(Add::make(Max::make(i32_sub_y0x0, i32_x0), Max::make(i32_y0, i32_x0)), i32_y0), i32_zero}};
        exprs[12] = {{Min::make(Add::make(Max::make(Sub::make(i32_y0, Min::make(i32_x0, k0)), i32_x0), k0), i32_y0), i32_zero}};
        exprs[13] = {{Min::make(Add::make(Max::make(Sub::make(i32_y0, Min::make(i32_x0, k0)), i32_x0), i32_x0), i32_y0), i32_tmin}};
        exprs[14] = {{Min::make(Add::make(Sub::make(Max::make(i32_y0, i32_x0), Min::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[15] = {{Min::make(Add::make(Sub::make(i32_max_x0y0, Min::make(i32_x0, k0)), i32_y0), i32_y0), i32_zero}};
        exprs[16] = {{Min::make(Add::make(Sub::make(Max::make(i32_y0, i32_x0), Min::make(i32_y0, i32_x0)), i32_y0), i32_y0), i32_tmax}};
        exprs[17] = {{Min::make(Add::make(Sub::make(i32_max_x0y0, i32_min_x0y0), i32_x0), i32_y0), i32_zero}};
        exprs[18] = {{Min::make(Add::make(Sub::make(i32_y0, Min::make(Mul::make(i32_y0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[19] = {{Min::make(Add::make(Sub::make(i32_y0, Min::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[20] = {{Min::make(Max::make(i32_x0, k0), i32_y0), i32_tmax}};
        exprs[21] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_x0), k0), i32_add_x0y0), i32_zero}};
        exprs[22] = {{Min::make(Max::make(Add::make(i32_max_x0y0, i32_x0), i32_y0), i32_add_x0y0), i32_zero}};
        exprs[23] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_x0), i32_y0), i32_add_x0y0), i32_zero}};
        exprs[24] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[25] = {{Min::make(Max::make(Add::make(i32_max_x0y0, i32_x0), i32_x0), i32_add_x0y0), i32_zero}};
        exprs[26] = {{Min::make(Max::make(Add::make(i32_max_x0y0, i32_y0), i32_y0), i32_add_x0y0), i32_zero}};
        exprs[27] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_x0), i32_y0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[28] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_x0), k0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[29] = {{Min::make(Max::make(Add::make(i32_max_x0y0, i32_x0), k0), i32_add_x0y0), i32_zero}};
        exprs[30] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), k0), Add::make(i32_y0, i32_x0)), i32_zero}};
        exprs[31] = {{Min::make(Max::make(Add::make(i32_max_x0y0, i32_mul_y0y0), k0), i32_y0), i32_zero}};
        exprs[32] = {{Min::make(Max::make(Add::make(i32_max_x0y0, k0), Sub::make(i32_y0, k0)), i32_y0), -1}};
        exprs[33] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_x0), i32_sub_y0x0), i32_y0), i32_zero}};
        exprs[34] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), k0), Sub::make(i32_y0, k0)), i32_y0), 7720}};
        exprs[35] = {{Min::make(Max::make(Add::make(Max::make(i32_sub_y0x0, k0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[36] = {{Min::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), i32_sub_y0x0), i32_y0), i32_zero}};
        exprs[37] = {{Min::make(Max::make(Add::make(Max::make(i32_x0, k0), Sub::make(k0, i32_y0)), i32_x0), i32_y0), i32_tmax}};
        exprs[38] = {{Min::make(Max::make(Add::make(Max::make(Sub::make(i32_y0, k0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[39] = {{Min::make(Max::make(Add::make(Max::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[40] = {{Min::make(Max::make(Add::make(i32_max_x0y0, i32_x0), i32_sub_y0x0), i32_y0), i32_zero}};
        exprs[41] = {{Min::make(Max::make(Add::make(Min::make(i32_sub_x0y0, i32_y0), i32_x0), i32_x0), i32_y0), i32_tmax}};
        exprs[42] = {{Min::make(Max::make(Add::make(Min::make(i32_sub_x0y0, k0), i32_x0), i32_x0), i32_y0), i32_tmax}};
        exprs[43] = {{Min::make(Max::make(i32_mul_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[44] = {{Min::make(Max::make(Mul::make(Max::make(Min::make(i32_x0, k0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[45] = {{Min::make(Max::make(Mul::make(Min::make(i32_y0, k0), i32_y0), Max::make(k0, i32_x0)), i32_y0), i32_tmax}};
        exprs[46] = {{Min::make(Max::make(Mul::make(i32_sub_y0x0, i32_y0), Max::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[47] = {{Min::make(Max::make(Max::make(Add::make(i32_max_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[48] = {{Min::make(Max::make(Max::make(Add::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[49] = {{Min::make(Max::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[50] = {{Min::make(Max::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[51] = {{Min::make(Max::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[52] = {{Min::make(Max::make(Max::make(Add::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[53] = {{Min::make(Max::make(Max::make(Add::make(Min::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[54] = {{Min::make(Max::make(Max::make(Add::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[55] = {{Min::make(Max::make(Max::make(Add::make(i32_min_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[56] = {{Min::make(Max::make(Max::make(Add::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[57] = {{Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[58] = {{Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), Add::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[59] = {{Min::make(Max::make(Max::make(Mul::make(Add::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[60] = {{Min::make(Max::make(Max::make(Mul::make(Add::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[61] = {{Min::make(Max::make(Max::make(Mul::make(i32_add_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[62] = {{Min::make(Max::make(Max::make(Mul::make(i32_add_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[63] = {{Min::make(Max::make(Max::make(Mul::make(Add::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[64] = {{Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), i32_mul_x0x0), i32_y0), i32_zero}};
        exprs[65] = {{Min::make(Max::make(Max::make(Mul::make(i32_mul_y0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[66] = {{Min::make(Max::make(Max::make(i32_mul_x0y0, i32_x0), i32_y0), i32_mul_x0y0), i32_one}};
        exprs[67] = {{Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), Mul::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[68] = {{Min::make(Max::make(Max::make(Mul::make(Max::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[69] = {{Min::make(Max::make(Max::make(Mul::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[70] = {{Min::make(Max::make(Max::make(Mul::make(i32_max_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[71] = {{Min::make(Max::make(Max::make(Mul::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[72] = {{Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), Max::make(k0, i32_x0)), i32_y0), i32_zero}};
        exprs[73] = {{Min::make(Max::make(Max::make(Mul::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[74] = {{Min::make(Max::make(Max::make(Mul::make(Min::make(i32_y0, i32_x0), i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[75] = {{Min::make(Max::make(Max::make(Mul::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[76] = {{Min::make(Max::make(Max::make(Mul::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[77] = {{Min::make(Max::make(Max::make(Mul::make(Min::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[78] = {{Min::make(Max::make(Max::make(Mul::make(i32_min_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[79] = {{Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), Sub::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[80] = {{Min::make(Max::make(Max::make(Mul::make(i32_sub_x0y0, i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[81] = {{Min::make(Max::make(Max::make(Mul::make(i32_sub_y0x0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[82] = {{Min::make(Max::make(Max::make(Mul::make(i32_sub_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[83] = {{Min::make(Max::make(Max::make(Mul::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[84] = {{Min::make(Max::make(Max::make(Mul::make(Sub::make(k0, i32_y0), k0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[85] = {{Min::make(Max::make(Max::make(i32_mul_y0y0, i32_y0), Sub::make(k0, i32_x0)), i32_y0), i32_zero}};
        exprs[86] = {{Min::make(Max::make(Max::make(Mul::make(i32_sub_y0x0, i32_y0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[87] = {{Min::make(Max::make(Max::make(Mul::make(i32_sub_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[88] = {{Min::make(Max::make(Max::make(Max::make(Mul::make(i32_y0, i32_x0), i32_y0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[89] = {{Min::make(Max::make(Max::make(Min::make(Mul::make(i32_x0, k0), i32_x0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[90] = {{Min::make(Max::make(Max::make(Min::make(Mul::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[91] = {{Min::make(Max::make(Max::make(Min::make(i32_mul_x0y0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[92] = {{Min::make(Max::make(Max::make(Min::make(i32_mul_y0y0, k0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[93] = {{Min::make(Max::make(Max::make(Min::make(i32_mul_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[94] = {{Min::make(Max::make(Max::make(Min::make(i32_sub_y0x0, i32_x0), i32_y0), k0), i32_y0), i32_zero}};
        exprs[95] = {{Min::make(Max::make(Max::make(Min::make(i32_y0, k0), Sub::make(k0, i32_y0)), i32_x0), i32_y0), i32_tmax}};
        exprs[96] = {{Min::make(Max::make(Max::make(Min::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[97] = {{Min::make(Max::make(Max::make(Min::make(Sub::make(k0, i32_x0), i32_x0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[98] = {{Min::make(Max::make(Max::make(i32_sub_x0y0, i32_y0), k0), i32_y0), i32_zero}};
        exprs[99] = {{Min::make(Max::make(Max::make(Sub::make(i32_mul_x0x0, i32_y0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[100] = {{Min::make(Max::make(Min::make(i32_mul_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_x0), i32_tmax}};
        exprs[101] = {{Min::make(Max::make(Min::make(Max::make(Add::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[102] = {{Min::make(Max::make(Min::make(Max::make(Add::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[103] = {{Min::make(Max::make(Min::make(Max::make(Mul::make(i32_y0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[104] = {{Min::make(Max::make(Min::make(Max::make(i32_mul_x0x0, i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[105] = {{Min::make(Max::make(Min::make(Max::make(Mul::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[106] = {{Min::make(Max::make(Min::make(Max::make(i32_mul_y0y0, i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[107] = {{Min::make(Max::make(Min::make(Max::make(Mul::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[108] = {{Min::make(Max::make(Min::make(Max::make(i32_mul_x0y0, i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[109] = {{Min::make(Max::make(Min::make(Max::make(i32_mul_x0x0, i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[110] = {{Min::make(Max::make(Min::make(Max::make(Mul::make(i32_y0, i32_x0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[111] = {{Min::make(Max::make(Min::make(i32_max_x0y0, i32_mul_y0y0), k0), i32_y0), i32_zero}};
        exprs[112] = {{Min::make(Max::make(Min::make(i32_max_x0y0, k0), i32_mul_y0y0), i32_y0), i32_zero}};
        exprs[113] = {{Min::make(Max::make(Min::make(Max::make(Mul::make(i32_y0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[114] = {{Min::make(Max::make(Min::make(Max::make(i32_y0, i32_x0), k0), i32_mul_y0y0), i32_y0), i32_zero}};
        exprs[115] = {{Min::make(Max::make(Min::make(Max::make(i32_mul_x0y0, i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[116] = {{Min::make(Max::make(Min::make(Max::make(i32_mul_y0y0, i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[117] = {{Min::make(Max::make(Min::make(i32_max_x0y0, k0), i32_min_x0y0), i32_y0), i32_tmax}};
        exprs[118] = {{Min::make(Max::make(Min::make(Max::make(i32_y0, i32_x0), k0), Min::make(i32_y0, i32_x0)), i32_y0), i32_tmax}};
        exprs[119] = {{Min::make(Max::make(Min::make(Max::make(i32_y0, k0), i32_x0), Min::make(i32_y0, k0)), i32_y0), i32_tmax}};
        exprs[120] = {{Min::make(Max::make(Min::make(Max::make(Sub::make(k0, i32_x0), i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[121] = {{Min::make(Max::make(Min::make(Max::make(Sub::make(k0, i32_y0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[122] = {{Min::make(Max::make(Min::make(Max::make(i32_sub_x0y0, i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[123] = {{Min::make(Max::make(Min::make(Max::make(Sub::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[124] = {{Min::make(Max::make(Min::make(Max::make(i32_sub_x0y0, i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[125] = {{Min::make(Max::make(Min::make(Max::make(i32_y0, k0), i32_x0), Sub::make(k0, i32_y0)), i32_y0), i32_tmax}};
        exprs[126] = {{Min::make(Max::make(Min::make(Max::make(Sub::make(k0, i32_y0), i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[127] = {{Min::make(Max::make(Min::make(Max::make(Sub::make(k0, i32_x0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[128] = {{Min::make(Max::make(Min::make(Max::make(i32_y0, k0), Sub::make(k0, i32_y0)), i32_x0), i32_y0), i32_tmax}};
        exprs[129] = {{Min::make(Max::make(Min::make(Max::make(Sub::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmax}};
        exprs[130] = {{Min::make(Max::make(Min::make(Min::make(i32_mul_y0y0, i32_y0), k0), i32_y0), i32_x0), i32_tmax}};
        exprs[131] = {{Min::make(Max::make(Min::make(Min::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[132] = {{Min::make(Max::make(Min::make(Min::make(i32_mul_x0y0, i32_x0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[133] = {{Min::make(Max::make(Min::make(Min::make(i32_sub_y0x0, i32_x0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[134] = {{Min::make(Max::make(Min::make(Sub::make(Max::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[135] = {{Min::make(Max::make(Min::make(i32_sub_x0y0, Min::make(i32_y0, k0)), i32_y0), i32_x0), i32_tmax}};
        exprs[136] = {{Min::make(Max::make(Sub::make(k0, i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[137] = {{Min::make(Max::make(Sub::make(k0, Add::make(Max::make(i32_y0, i32_x0), i32_y0)), i32_x0), i32_y0), i32_tmax}};
        exprs[138] = {{Min::make(Max::make(Sub::make(Add::make(Max::make(i32_y0, k0), i32_y0), i32_x0), i32_x0), i32_y0), i32_tmax}};
        exprs[139] = {{Min::make(Max::make(Sub::make(Add::make(Min::make(i32_x0, k0), i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[140] = {{Min::make(Max::make(Sub::make(i32_x0, i32_mul_y0y0), Max::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[141] = {{Min::make(Max::make(Sub::make(i32_mul_y0y0, i32_x0), Max::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[142] = {{Min::make(Max::make(Sub::make(k0, Max::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[143] = {{Min::make(Max::make(i32_sub_x0y0, Max::make(i32_y0, k0)), i32_y0), i32_zero}};
        exprs[144] = {{Min::make(Max::make(Sub::make(Max::make(i32_y0, i32_x0), k0), Add::make(i32_y0, k0)), i32_y0), 7720}};
        exprs[145] = {{Min::make(Max::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), k0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[146] = {{Min::make(Max::make(Sub::make(Max::make(i32_add_x0y0, k0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[147] = {{Min::make(Max::make(Sub::make(Max::make(i32_y0, k0), i32_x0), i32_add_x0y0), i32_y0), i32_zero}};
        exprs[148] = {{Min::make(Max::make(Sub::make(Max::make(Add::make(i32_y0, k0), i32_x0), k0), i32_x0), i32_y0), i32_tmin}};
        exprs[149] = {{Min::make(Max::make(Sub::make(i32_max_x0y0, k0), Add::make(i32_y0, k0)), i32_y0), -1}};
        exprs[150] = {{Min::make(Max::make(Sub::make(Max::make(i32_y0, k0), i32_x0), Add::make(i32_y0, i32_x0)), i32_y0), i32_zero}};
        exprs[151] = {{Min::make(Max::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), k0), i32_x0), i32_x0), i32_y0), i32_zero}};
        exprs[152] = {{Min::make(Max::make(Sub::make(Max::make(i32_add_x0y0, k0), i32_x0), k0), i32_y0), i32_zero}};
        exprs[153] = {{Min::make(Max::make(Sub::make(Max::make(i32_add_x0y0, k0), i32_x0), i32_x0), i32_y0), i32_zero}};
        exprs[154] = {{Min::make(Max::make(Sub::make(Max::make(i32_y0, k0), i32_max_x0y0), i32_x0), i32_y0), i32_tmax}};
        exprs[155] = {{Min::make(Max::make(Sub::make(Max::make(i32_y0, k0), Max::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[156] = {{Min::make(Max::make(Sub::make(k0, Max::make(Min::make(i32_x0, k0), i32_y0)), i32_x0), i32_y0), i32_tmax}};
        exprs[157] = {{Min::make(Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_y0), i32_y0)), i32_x0), i32_y0), i32_tmax}};
        exprs[158] = {{Min::make(Max::make(Sub::make(i32_y0, Max::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[159] = {{Min::make(Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[160] = {{Min::make(Max::make(Sub::make(i32_y0, Max::make(i32_sub_y0x0, k0)), i32_x0), i32_y0), i32_tmax}};
        exprs[161] = {{Min::make(Max::make(Sub::make(k0, Max::make(Sub::make(k0, i32_y0), i32_y0)), i32_y0), i32_x0), i32_tmax}};
        exprs[162] = {{Min::make(Max::make(Sub::make(i32_x0, Max::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_tmax}};
        exprs[163] = {{Min::make(Max::make(Sub::make(Min::make(i32_y0, k0), i32_max_x0y0), i32_x0), i32_y0), i32_tmax}};
        exprs[164] = {{Min::make(Max::make(Sub::make(Min::make(i32_y0, k0), Max::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[165] = {{Min::make(Max::make(Sub::make(Min::make(Max::make(i32_y0, i32_x0), k0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[166] = {{Min::make(Max::make(Sub::make(Min::make(i32_max_x0y0, k0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[167] = {{Min::make(Max::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_y0)), k0), i32_y0), i32_zero}};
        exprs[168] = {{Min::make(Max::make(Sub::make(k0, Min::make(Sub::make(k0, i32_y0), i32_y0)), i32_x0), i32_y0), i32_zero}};
        exprs[169] = {{Min::make(Max::make(Sub::make(k0, Min::make(Sub::make(k0, i32_y0), i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[170] = {{Min::make(Max::make(Sub::make(Min::make(i32_sub_x0y0, i32_y0), i32_x0), i32_x0), i32_y0), i32_tmax}};
        exprs[171] = {{Min::make(Max::make(Sub::make(k0, Min::make(Sub::make(k0, i32_x0), i32_y0)), i32_x0), i32_y0), i32_tmax}};
        exprs[172] = {{Min::make(Max::make(Sub::make(i32_y0, Min::make(i32_sub_x0y0, k0)), i32_x0), i32_y0), i32_tmax}};
        exprs[173] = {{Min::make(Max::make(Sub::make(Sub::make(k0, i32_y0), i32_max_x0y0), i32_x0), i32_y0), i32_tmax}};
        exprs[174] = {{Min::make(Min::make(Max::make(Add::make(Mul::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[175] = {{Min::make(Min::make(Max::make(Add::make(i32_mul_x0x0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[176] = {{Min::make(Min::make(Max::make(Add::make(i32_mul_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[177] = {{Min::make(Min::make(Max::make(Add::make(Max::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[178] = {{Min::make(Min::make(Max::make(Add::make(i32_max_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[179] = {{Min::make(Min::make(Max::make(Add::make(i32_max_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[180] = {{Min::make(Min::make(Max::make(Add::make(i32_max_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[181] = {{Min::make(Min::make(Max::make(Add::make(i32_max_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[182] = {{Min::make(Min::make(Max::make(Add::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[183] = {{Min::make(Min::make(Max::make(Add::make(i32_min_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[184] = {{Min::make(Min::make(Max::make(Add::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[185] = {{Min::make(Min::make(Max::make(Add::make(Min::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[186] = {{Min::make(Min::make(Max::make(Add::make(i32_min_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[187] = {{Min::make(Min::make(Max::make(Add::make(i32_min_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[188] = {{Min::make(Min::make(Max::make(Add::make(i32_min_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[189] = {{Min::make(Min::make(Max::make(Mul::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[190] = {{Min::make(Min::make(Max::make(i32_mul_x0y0, i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[191] = {{Min::make(Min::make(Max::make(Mul::make(i32_add_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[192] = {{Min::make(Min::make(Max::make(Mul::make(i32_add_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[193] = {{Min::make(Min::make(Max::make(Mul::make(Add::make(i32_y0, i32_x0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[194] = {{Min::make(Min::make(Max::make(Mul::make(i32_add_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[195] = {{Min::make(Min::make(Max::make(Mul::make(i32_max_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[196] = {{Min::make(Min::make(Max::make(Mul::make(i32_max_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[197] = {{Min::make(Min::make(Max::make(Mul::make(Max::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[198] = {{Min::make(Min::make(Max::make(Mul::make(i32_max_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[199] = {{Min::make(Min::make(Max::make(i32_mul_x0y0, Max::make(i32_y0, k0)), i32_x0), i32_y0), i32_tmax}};
        exprs[200] = {{Min::make(Min::make(Max::make(Mul::make(i32_max_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[201] = {{Min::make(Min::make(Max::make(Mul::make(i32_max_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[202] = {{Min::make(Min::make(Max::make(Mul::make(i32_min_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[203] = {{Min::make(Min::make(Max::make(Mul::make(i32_min_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[204] = {{Min::make(Min::make(Max::make(Mul::make(i32_min_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[205] = {{Min::make(Min::make(Max::make(Mul::make(Min::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[206] = {{Min::make(Min::make(Max::make(Mul::make(i32_min_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[207] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_x0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[208] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_x0y0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[209] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_y0x0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[210] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_y0x0, i32_y0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[211] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_x0y0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[212] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[213] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_x0y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[214] = {{Min::make(Min::make(Max::make(Mul::make(i32_sub_y0x0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[215] = {{Min::make(Min::make(Max::make(Max::make(i32_mul_x0y0, i32_x0), k0), i32_y0), i32_x0), i32_tmax}};
        exprs[216] = {{Min::make(Min::make(Max::make(Max::make(i32_mul_x0x0, i32_x0), k0), i32_x0), i32_y0), i32_tmax}};
        exprs[217] = {{Min::make(Min::make(Max::make(Max::make(i32_sub_y0x0, i32_x0), k0), i32_y0), i32_x0), i32_tmax}};
        exprs[218] = {{Min::make(Min::make(Max::make(Min::make(i32_add_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[219] = {{Min::make(Min::make(Max::make(Min::make(i32_mul_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[220] = {{Min::make(Min::make(Max::make(Min::make(i32_sub_y0x0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[221] = {{Min::make(Min::make(Max::make(Min::make(i32_sub_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[222] = {{Min::make(Min::make(Max::make(i32_sub_x0y0, i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[223] = {{Min::make(Min::make(Max::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[224] = {{Min::make(Min::make(Max::make(Sub::make(Add::make(k0, i32_y0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[225] = {{Min::make(Min::make(Max::make(Sub::make(i32_mul_y0y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[226] = {{Min::make(Min::make(Max::make(Sub::make(i32_mul_x0x0, i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[227] = {{Min::make(Min::make(Max::make(Sub::make(i32_y0, i32_mul_x0x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[228] = {{Min::make(Min::make(Max::make(Sub::make(k0, i32_mul_x0y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[229] = {{Min::make(Min::make(Max::make(Sub::make(i32_mul_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[230] = {{Min::make(Min::make(Max::make(Sub::make(Mul::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[231] = {{Min::make(Min::make(Max::make(Sub::make(i32_y0, Mul::make(i32_x0, k0)), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[232] = {{Min::make(Min::make(Max::make(Sub::make(Mul::make(i32_x0, k0), i32_y0), i32_y0), i32_x0), i32_y0), i32_tmax}};
        exprs[233] = {{Min::make(Min::make(Max::make(i32_sub_x0y0, Max::make(i32_y0, k0)), i32_x0), i32_y0), i32_tmax}};
        exprs[234] = {{Min::make(Min::make(Max::make(Sub::make(Max::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[235] = {{Min::make(Min::make(Max::make(Sub::make(k0, i32_max_x0y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[236] = {{Min::make(Min::make(Max::make(Sub::make(i32_y0, Max::make(i32_x0, k0)), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[237] = {{Min::make(Min::make(Max::make(Sub::make(Max::make(i32_y0, k0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[238] = {{Min::make(Min::make(Max::make(Sub::make(i32_max_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[239] = {{Min::make(Min::make(Max::make(Sub::make(i32_min_x0y0, k0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[240] = {{Min::make(Min::make(Max::make(Sub::make(k0, i32_min_x0y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[241] = {{Min::make(Min::make(Max::make(Sub::make(Min::make(i32_x0, k0), i32_y0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[242] = {{Min::make(Min::make(Max::make(Sub::make(Min::make(i32_y0, k0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[243] = {{Min::make(Min::make(Max::make(Sub::make(i32_y0, Min::make(i32_x0, k0)), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[244] = {{Min::make(Min::make(Max::make(Sub::make(Sub::make(i32_y0, k0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[245] = {{Min::make(Min::make(Max::make(Sub::make(Sub::make(k0, i32_y0), i32_x0), i32_x0), i32_y0), i32_x0), i32_tmax}};
        exprs[246] = {{Min::make(Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_x0), i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[247] = {{Min::make(Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_x0), i32_tmax}};
        exprs[248] = {{Min::make(Min::make(Sub::make(i32_y0, Min::make(i32_sub_y0x0, i32_x0)), i32_x0), i32_y0), i32_tmax}};
        exprs[249] = {{Min::make(Sub::make(Add::make(Max::make(Mul::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[250] = {{Min::make(Sub::make(Add::make(Max::make(i32_y0, i32_x0), i32_y0), Min::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[251] = {{Min::make(Sub::make(Add::make(Max::make(i32_y0, k0), i32_y0), Min::make(i32_x0, k0)), i32_y0), i32_one}};
        exprs[252] = {{Min::make(Sub::make(Add::make(Max::make(i32_sub_y0x0, i32_x0), i32_y0), i32_x0), i32_y0), 1207960576}};
        exprs[253] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[254] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, k0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[255] = {{Min::make(Sub::make(Max::make(i32_add_x0y0, k0), i32_x0), i32_y0), i32_zero}};
        exprs[256] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), Mul::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[257] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), i32_mul_y0y0), i32_x0), i32_y0), i32_zero}};
        exprs[258] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), Mul::make(i32_x0, k0)), i32_x0), i32_y0), i32_zero}};
        exprs[259] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), i32_mul_x0x0), i32_x0), i32_y0), i32_zero}};
        exprs[260] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_x0, k0), i32_y0), k0), i32_x0), i32_y0), -1}};
        exprs[261] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_y0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[262] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[263] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_y0), k0), i32_y0), i32_y0), i32_zero}};
        exprs[264] = {{Min::make(Sub::make(Max::make(Add::make(i32_max_x0y0, k0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[265] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[266] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_x0), k0), i32_x0), i32_y0), i32_zero}};
        exprs[267] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_x0, k0), i32_y0), i32_x0), k0), i32_y0), i32_tmin}};
        exprs[268] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_y0), i32_x0), i32_y0), i32_y0), -1560281088}};
        exprs[269] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_x0), i32_y0), i32_x0), i32_y0), i32_zero}};
        exprs[270] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, k0), i32_y0), i32_x0), i32_y0), i32_y0), i32_tmin}};
        exprs[271] = {{Min::make(Sub::make(Max::make(Add::make(i32_max_x0y0, k0), i32_y0), k0), i32_y0), -1}};
        exprs[272] = {{Min::make(Sub::make(Max::make(Add::make(Max::make(i32_y0, i32_x0), i32_y0), k0), i32_x0), i32_y0), 8855}};
        exprs[273] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), k0), Min::make(i32_x0, k0)), i32_y0), i32_one}};
        exprs[274] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), k0), Min::make(i32_y0, i32_x0)), i32_y0), -1}};
        exprs[275] = {{Min::make(Sub::make(Max::make(i32_add_x0y0, k0), Min::make(i32_x0, k0)), i32_y0), i32_one}};
        exprs[276] = {{Min::make(Sub::make(Max::make(i32_add_x0y0, k0), i32_min_x0y0), i32_y0), i32_zero}};
        exprs[277] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, k0), i32_x0), Min::make(i32_x0, k0)), i32_y0), i32_zero}};
        exprs[278] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, k0), i32_x0), Min::make(i32_y0, k0)), i32_y0), i32_tmin}};
        exprs[279] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), Sub::make(i32_y0, k0)), i32_x0), i32_y0), i32_zero}};
        exprs[280] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), Sub::make(k0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[281] = {{Min::make(Sub::make(Max::make(Add::make(i32_y0, i32_x0), Sub::make(k0, i32_y0)), i32_x0), i32_y0), i32_zero}};
        exprs[282] = {{Min::make(Sub::make(Max::make(Min::make(i32_x0, k0), Add::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[283] = {{Min::make(Sub::make(Max::make(Min::make(i32_y0, k0), Add::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[284] = {{Min::make(Sub::make(Max::make(Min::make(i32_y0, i32_x0), Add::make(i32_y0, i32_x0)), i32_x0), i32_y0), i32_zero}};
        exprs[285] = {{Min::make(Sub::make(Max::make(i32_x0, k0), Min::make(i32_sub_x0y0, k0)), i32_y0), -1}};
        exprs[286] = {{Min::make(Sub::make(i32_max_x0y0, Min::make(i32_sub_x0y0, k0)), i32_y0), -1}};
        exprs[287] = {{Min::make(Sub::make(Max::make(i32_x0, k0), Min::make(Sub::make(k0, i32_y0), i32_x0)), i32_y0), -1}};
        exprs[288] = {{Min::make(Sub::make(Max::make(i32_y0, i32_x0), Min::make(i32_sub_x0y0, k0)), i32_y0), i32_one}};
        exprs[289] = {{Min::make(Sub::make(Max::make(i32_x0, k0), Min::make(Sub::make(k0, i32_y0), i32_y0)), i32_y0), i32_tmin}};
        exprs[290] = {{Min::make(Sub::make(Max::make(i32_y0, i32_x0), Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_tmax}};
        exprs[291] = {{Min::make(Sub::make(Max::make(i32_x0, k0), Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_tmax}};
        exprs[292] = {{Min::make(Sub::make(i32_max_x0y0, Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_tmax}};
        exprs[293] = {{Min::make(Sub::make(Max::make(i32_y0, k0), Min::make(Sub::make(k0, i32_y0), i32_x0)), i32_y0), i32_zero}};
        exprs[294] = {{Min::make(Sub::make(k0, Min::make(Add::make(i32_y0, i32_x0), Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[295] = {{Min::make(Sub::make(k0, Min::make(Max::make(i32_x0, k0), Sub::make(k0, i32_y0))), i32_x0), i32_tmax}};
        exprs[296] = {{Min::make(Sub::make(i32_x0, Min::make(Max::make(i32_y0, i32_x0), i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[297] = {{Min::make(Sub::make(k0, Min::make(Max::make(i32_x0, k0), Sub::make(k0, i32_y0))), i32_y0), i32_tmax}};
        exprs[298] = {{Min::make(Sub::make(k0, Min::make(i32_max_x0y0, Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[299] = {{Min::make(Sub::make(i32_x0, Min::make(Max::make(i32_x0, k0), i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[300] = {{Min::make(Sub::make(k0, Min::make(i32_max_x0y0, Sub::make(k0, i32_y0))), i32_x0), i32_tmax}};
        exprs[301] = {{Min::make(Sub::make(i32_x0, Min::make(i32_max_x0y0, i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[302] = {{Min::make(Sub::make(k0, Min::make(Max::make(i32_y0, i32_x0), Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[303] = {{Min::make(Sub::make(i32_x0, Min::make(Max::make(i32_y0, k0), i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[304] = {{Min::make(Sub::make(Min::make(i32_x0, k0), Min::make(Sub::make(k0, i32_y0), i32_x0)), i32_x0), i32_tmax}};
        exprs[305] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_y0)), i32_y0), i32_zero}};
        exprs[306] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, k0)), i32_y0), -1}};
        exprs[307] = {{Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_y0), i32_x0)), i32_y0), i32_tmax}};
        exprs[308] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, Add::make(i32_y0, k0))), i32_y0), -1}};
        exprs[309] = {{Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_y0), i32_mul_x0x0)), i32_y0), i32_zero}};
        exprs[310] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, Mul::make(i32_y0, i32_x0))), i32_y0), i32_zero}};
        exprs[311] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_mul_x0x0)), i32_y0), i32_zero}};
        exprs[312] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_mul_y0y0)), i32_y0), i32_zero}};
        exprs[313] = {{Min::make(Sub::make(k0, Min::make(Sub::make(k0, Max::make(i32_y0, i32_x0)), i32_y0)), i32_y0), i32_tmin}};
        exprs[314] = {{Min::make(Sub::make(k0, Min::make(Sub::make(k0, i32_min_x0y0), i32_x0)), i32_x0), i32_tmax}};
        exprs[315] = {{Min::make(Sub::make(k0, Min::make(Sub::make(Min::make(i32_x0, k0), i32_y0), i32_y0)), i32_y0), i32_tmax}};
        exprs[316] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, Min::make(i32_y0, k0))), i32_y0), -1}};
        exprs[317] = {{Min::make(Sub::make(i32_x0, Min::make(Sub::make(Min::make(i32_x0, k0), i32_y0), i32_y0)), i32_y0), i32_tmin}};
        exprs[318] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, Sub::make(i32_y0, k0))), i32_y0), i32_zero}};
        exprs[319] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, Sub::make(k0, i32_x0))), i32_y0), -1}};
        exprs[320] = {{Min::make(Sub::make(k0, Min::make(i32_sub_y0x0, Sub::make(k0, i32_y0))), i32_y0), i32_zero}};
        exprs[321] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_y0x0, i32_sub_x0y0)), i32_y0), i32_zero}};
        exprs[322] = {{Min::make(Sub::make(i32_x0, Min::make(i32_sub_x0y0, i32_sub_y0x0)), i32_y0), i32_zero}};
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_single_i32_ops_table_sub() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(4);
    if (!init) {
        exprs[0] = {{Sub::make(Max::make(Add::make(i32_y0, k0), i32_x0), Max::make(i32_sub_x0y0, k0)), i32_zero}};
        exprs[1] = {{Sub::make(Max::make(Add::make(i32_y0, i32_x0), k0), Max::make(Sub::make(k0, i32_y0), i32_x0)), -1}};
        exprs[2] = {{Sub::make(Min::make(Add::make(i32_y0, k0), i32_x0), Min::make(i32_sub_x0y0, k0)), i32_zero}};
        exprs[3] = {{Sub::make(Min::make(Add::make(i32_y0, i32_x0), k0), Min::make(Sub::make(k0, i32_y0), i32_x0)), i32_one}};
        init = true;
    }
    return exprs;
}


const vector<vector<AssociativePair>> &get_double_i32_ops_table_add() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(0);
    if (!init) {
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_double_i32_ops_table_mul() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(0);
    if (!init) {
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_double_i32_ops_table_max() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(0);
    if (!init) {
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_double_i32_ops_table_min() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(0);
    if (!init) {
        init = true;
    }
    return exprs;
}

const vector<vector<AssociativePair>> &get_double_i32_ops_table_sub() {
    static bool init = false;
    static vector<vector<AssociativePair>> exprs(0);
    if (!init) {
        init = true;
    }
    return exprs;
}

} // anonymous namespace

const std::vector<std::vector<AssociativePair>> &get_i32_ops_table(const vector<Expr> &exprs) {

    static std::vector<std::vector<AssociativePair>> empty;
    if (exprs[0].as<Add>()) {
        debug(5) << "Returning add root table\n";
        if (exprs.size() == 1) {
            return get_single_i32_ops_table_add();
        } else {
            return get_double_i32_ops_table_add();
        }
    } else if (exprs[0].as<Sub>()) {
        debug(5) << "Returning sub root table\n";
        if (exprs.size() == 1) {
            return get_single_i32_ops_table_sub();
        } else {
            return get_double_i32_ops_table_sub();
        }
    } else if (exprs[0].as<Mul>()) {
        debug(5) << "Returning mul root table\n";
        if (exprs.size() == 1) {
            return get_single_i32_ops_table_mul();
        } else {
            return get_double_i32_ops_table_mul();
        }
    } else if (exprs[0].as<Min>()) {
        debug(5) << "Returning min root table\n";
        if (exprs.size() == 1) {
            return get_single_i32_ops_table_min();
        } else {
            return get_double_i32_ops_table_min();
        }
    } else if (exprs[0].as<Max>()) {
        debug(5) << "Returning max root table\n";
        if (exprs.size() == 1) {
            return get_single_i32_ops_table_max();
        } else {
            return get_double_i32_ops_table_max();
        }
    }
    debug(5) << "Returning empty table\n";
    return empty;
}

}
}

using namespace Halide;
using namespace Halide::Internal;

int main() {
    Expr x = Variable::make(Int(32), "x");
    Expr y = Variable::make(Int(32), "y");
    Expr expr = Min::make(x, y);
    const auto &table = get_i32_ops_table({expr});
    std::cout << "Op: " << table[0][0].op << " with id: " << table[0][0].identity << "\n";
    return 0;
}

