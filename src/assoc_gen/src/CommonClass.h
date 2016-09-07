#ifndef COMMON_CLASS_H
#define COMMON_CLASS_H

/** \file
 *
 * Common class/declaration used across the files.
 */

#include "Halide.h"
#include "z3++.h"

#include <vector>
#include <boost/icl/interval_set.hpp>

typedef boost::icl::interval_set<unsigned int> IntervalSet;
typedef IntervalSet::interval_type IntervalVal;

typedef int Value;

inline Value random_value() {
    return (((rand() << 16) ^ (rand() << 8) ^ rand()) & 0x0ffffff) - 0x07fffff;
}

typedef enum {
    Int = 0
} Type;

struct DecisionSource {
    uint64_t val;

    DecisionSource() : val(0) {}

    // Choose between n alternatives
    int get(int n) {
        assert(n > 0);
        int result = val % n;
        val /= n;
        return result;
    }

    // Give away half the bits to a new decision source.
    DecisionSource fork() {
        DecisionSource a, b;
        for (int i = 0; i < 32; i++) {
            b.val |= ((val >> (2*i)) & 1) << i;
            a.val |= ((val >> (2*i + 1)) & 1) << i;
        }
        val = a.val;
        return b;
    }
};

struct Point {
    uint64_t leaves;
    uint64_t i;
};

enum Node : long;

class Expr {
public:
	std::vector<Node> nodes;
    int size;
    bool fail;
    std::vector<bool> uses_x;
    std::vector<bool> uses_y;

    Expr() : Expr(1) {}
    Expr(int tuple_size) : nodes(64), size(0), fail(false), uses_x(tuple_size, false), uses_y(tuple_size, false) {}

    bool operator==(const Expr &rhs) const { return rhs.nodes == nodes; }
    bool operator<(const Expr &rhs) const { return rhs.nodes < nodes; }
};

template<class T>
class AssociativeTuple {
public:
    std::vector<T> exprs;

    AssociativeTuple(const T &e0, const T &e1) {
        exprs.push_back(e0);
        exprs.push_back(e1);
    }

    AssociativeTuple(const T &e0, const T &e1, const T &e2) {
        exprs.push_back(e0);
        exprs.push_back(e1);
        exprs.push_back(e2);
    }

    AssociativeTuple(const T &e0, const T &e1, const T &e2, const T &e3) {
        exprs.push_back(e0);
        exprs.push_back(e1);
        exprs.push_back(e2);
        exprs.push_back(e3);
    }

    AssociativeTuple(const std::vector<T> &eqs) : exprs(eqs) {}

    bool operator==(const AssociativeTuple &rhs) const {
        if (exprs.size() != rhs.exprs.size()) {
            return false;
        }
        for (size_t i = 0; i < exprs.size(); ++i) {
            if (exprs[i] == rhs.exprs[i]) {
                continue;
            }
            return false;
        }
        return true;
    }

    bool operator<(const AssociativeTuple &rhs) const {
        if (exprs.size() != rhs.exprs.size()) {
            return exprs.size() < rhs.exprs.size();
        }
        for (size_t i = 0; i < exprs.size(); ++i) {
            if (exprs[i] < rhs.exprs[i]) {
                return true;
            }
            return false;
        }
        return true;
    }
};

class TupleExpr;

#endif
