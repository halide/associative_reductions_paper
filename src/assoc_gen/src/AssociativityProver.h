#ifndef ASSOCIATIVITY_PROVER_H
#define ASSOCIATIVITY_PROVER_H

/** \file
 *
 * Routines for proving associativity of a Halide expr and computing the identity
 * of the associative operator.
 */

#include "Halide.h"
#include "z3++.h"

#include <vector>

struct AssociativeIds {
	enum Associativity {
		LEFT,
		RIGHT,
		UNKNOWN
	};

    Associativity associativity;
    std::vector<Halide::Expr> identities;

    AssociativeIds() : associativity(UNKNOWN) {}
};

enum class IsAssociative {
	NO = 0,
	YES = 1,
	UNKNOWN = 2
};

/**
 * Given Tuple of Halide Exprs and list of variables involves in the exprs,
 * determine if they are associative and compute the identity of each Expr in
 * the Tuple if they are associative (with boolean values that indicates
 * left-associativity if true; otherwise, it's right-associative). For a Tuple
 * of Exprs to be associative, every Expr element of the Tuple has to be
 * associative. The Exprs should only involves two binary variables, x_i and y_i,
 * where i is index to the Tuple. For example, for complex multiplication, the
 * tuple of Exprs is the following:
 \code
 Halide::Tuple tuple = {
 	x0 * y0 - x1 * y1,
	x0 * y1 + x1 * y0
 };
 \endcode
 *
 * The list of variables are the following: xvars -> {x0, x1} and
 * yvars -> {y0, y1}. Note that xvars and yvars have to be of the same size,
 * which size equals to the Tuple size.
 */
// @{
std::pair<IsAssociative, AssociativeIds> prove_associativity(
	const Halide::Tuple &tuple,
	const std::vector<Halide::Expr> &xvars,
	const std::vector<Halide::Expr> &yvars,
	const std::vector<Halide::Expr> &constants);
std::pair<IsAssociative, AssociativeIds> prove_associativity(
	const Halide::Expr &expr,
	const std::vector<Halide::Expr> &xvars,
	const std::vector<Halide::Expr> &yvars,
	const std::vector<Halide::Expr> &constants);
// @}

void associativity_prover_test();

#endif
