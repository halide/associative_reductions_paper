#ifndef Z3_OPS_HELPER_H
#define Z3_OPS_HELPER_H

/** \file
 *
 * C++ wrapper methods for z3 bitvector arithmetic ops.
 */

#include "z3++.h"
#include <cstdlib>
#include <cmath>

namespace z3 {

inline z3::expr min(const z3::expr &a, const z3::expr &b) {
    return z3::ite(a <= b, a, b);
}

inline z3::expr umin(const z3::expr &a, const z3::expr &b) {
    return z3::ite(z3::ule(a, b), a, b);
}

inline z3::expr max(const z3::expr &a, const z3::expr &b) {
    return z3::ite(a >= b, a, b);
}

inline z3::expr umax(const z3::expr &a, const z3::expr &b) {
    return z3::ite(z3::uge(a, b), a, b);
}

inline z3::expr clamp(const z3::expr &a, const z3::expr &min_val, const z3::expr &max_val) {
    return max(min(a, max_val), min_val);
}

inline z3::expr uclamp(const z3::expr &a, const z3::expr &min_val, const z3::expr &max_val) {
    return umax(umin(a, max_val), min_val);
}

inline z3::expr bvcast(const z3::expr &a, int old_bit_size, int new_bit_size, bool is_signed) {
    if (new_bit_size == old_bit_size) {
        return a;
    } else if (new_bit_size > old_bit_size) {
        if (is_signed) {
            return z3::sext(a, new_bit_size-old_bit_size);
        } else {
            return z3::zext(a, new_bit_size-old_bit_size);
        }
    } else {
        z3::expr result = a.extract(new_bit_size - 1, 0);
        return result;
    }
}

inline z3::expr mod(const z3::expr &a, const z3::expr &b) {
	return to_expr(a.ctx(), Z3_mk_mod(a.ctx(), a, b));
}

inline z3::expr bvumod(const z3::expr &a, const z3::expr &b) {
    return to_expr(a.ctx(), Z3_mk_bvurem(a.ctx(), a, b));
}

inline z3::expr bvsmod(const z3::expr &a, const z3::expr &b) {
	return to_expr(a.ctx(), Z3_mk_bvsmod(a.ctx(), a, b));
}

/** Check if a is negative signed integer. */
inline bool is_neg(const z3::expr &a) {
    std::string a_str = Z3_ast_to_string(a.ctx(), a);
    int i = a_str[2] - '0';
    return (i >= 8);
}

inline int64_t to_int(const z3::expr &a, int bits, int64_t min_int) {
    std::string a_str = Z3_ast_to_string(a.ctx(), a);
    if (a_str == "#x8000000000000000") {
        int64_t val = min_int;
        return val;
    }
    int64_t val = a.get_numeral_int64();
    if (!is_neg(a)) {
        return val;
    }
    val -= std::pow(2, bits);
    return val;
}

inline uint64_t to_uint(const z3::expr &a) {
    return a.get_numeral_uint64();
}

}

#endif
