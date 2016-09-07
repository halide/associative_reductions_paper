#ifndef UTILITES_H
#define UTILITES_H

/** \file
 *
 * Utility functions used across the files.
 */

#include "Halide.h"
#include "z3++.h"
#include "CommonClass.h"
#include "Error.h"

#include <vector>
#include <algorithm>
#include <iostream>
#include <boost/icl/interval_set.hpp>

void morton2(uint32_t z, uint32_t &x, uint32_t &y);

bool uses_vars(Halide::Expr e, const std::vector<std::string> &vars);

std::ostream &operator<<(std::ostream &stream, const Halide::Tuple &tuple);

bool should_skip_expression(int index,
						    Halide::Expr expr,
                            bool e_fail,
                            const std::vector<bool> e_uses_x,
                            const std::vector<bool> e_uses_y,
							const std::vector<std::string> &kXNames,
                    		const std::vector<std::string> &kYNames,
                    		const std::vector<std::string> &kConstantNames);

// Return true if the expr is boring
bool is_expr_boring(Halide::Expr e, Halide::Expr &simplified,
                    const std::vector<std::string> &kXNames,
                    const std::vector<std::string> &kYNames,
                    const std::vector<std::string> &kConstantNames);

// Return true if it's decomposable
bool is_decomposable(const std::vector<std::vector<bool>> &eqs_uses_x,
                     const std::vector<std::vector<bool>> &eqs_uses_y);

// Return true if eqs are associative and have identities
bool z3_check_associativity(std::vector<Halide::Expr> &eqs, std::vector<Halide::Expr> &kXVars,
                            std::vector<Halide::Expr> &kYVars, std::vector<Halide::Expr> &kConstants,
                            std::vector<uint64_t> leaves, std::vector<uint64_t> is);

void is_decomposable_test();

#endif
