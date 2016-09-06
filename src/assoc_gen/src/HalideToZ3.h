#ifndef HALIDE_TO_Z3_H
#define HALIDE_TO_Z3_H

/** \file
 *
 * Routine for converting Halide Expr into Z3 Expr.
 */

#include "Halide.h"
#include "z3++.h"


/**
 * Convert a Halide Expr into an equivalent Z3 Expr. All integers (signed or
 * unsigned) are represented as bitvectors with appropriate bit size.
 *
 */
z3::expr convert_halide_to_z3(Halide::Expr e, z3::context *ctx, bool use_bv);

void halide_to_z3_test();

#endif
