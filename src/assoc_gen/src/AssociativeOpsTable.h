#ifndef HALIDE_ASSOCIATIVE_OPS_TABLE_H
#define HALIDE_ASSOCIATIVE_OPS_TABLE_H

/** \file
 * Tables listing associative operators and their identities.
 */

#include "Halide.h"

#include <iostream>
#include <vector>

namespace Halide {
namespace Internal {

struct AssociativePair {
    Expr op;
    Expr identity;

    AssociativePair() {}
    AssociativePair(Expr op) : op(op) {}
    AssociativePair(Expr op, Expr id) : op(op), identity(id) {}
};

const std::vector<std::vector<AssociativePair>> &get_i32_ops_table(const std::vector<Expr> &exprs);

}
}

#endif
