#include "Halide.h"
#include "Error.h"
#include "Utilities.h"

#include <algorithm>
#include <iostream>
#include <cstdlib>
#include <cassert>
#include <cmath>
#include <vector>
#include <map>
#include <set>
#include <stdint.h>

using std::pair;
using std::set;
using std::string;
using std::vector;
using Halide::Internal::Variable;

class TupleExpr;
typedef AssociativeTuple<TupleExpr> AssocTuple;

const size_t TUPLE_SIZE = 2;
const uint64_t START_LEAVES = 2;
const uint64_t MAX_LEAVES = 7;
const uint64_t LEAVES_TILE = 3;
const uint64_t ITER_TILE = 85000;

Halide::Type kType = Halide::Int(32);
vector<string> kXNames = {"x0", "x1"};
vector<string> kYNames = {"y0", "y1"};
vector<string> kConstantNames = {"k0"};
vector<Halide::Expr> kXVars = {
    Variable::make(kType, "x0"),
    Variable::make(kType, "x1")
};
vector<Halide::Expr> kYVars = {
    Variable::make(kType, "y0"),
    Variable::make(kType, "y1")
};
vector<Halide::Expr> kConstants = {
    Variable::make(kType, "k0"),
};

enum Node : long {
    X0 = 0,
    Y0,
    X1,
    Y1,
    K0,
    Add,
    Sub,
    Mul,
    Min,
    Max,
    LT,
    LastNode
};

class TupleExpr : public Expr {
public:
    bool is_cond;

    TupleExpr(bool is_cond) : Expr(2), is_cond(is_cond) {}
    TupleExpr() : Expr(2), is_cond(false) {}

    Value evaluate_term(const vector<Value> &xvalues, const vector<Value> &yvalues, Value k, int &cursor) const {
        Value v1, v2;
        switch(nodes[cursor++]) {
        case X0:
            return xvalues[0];
        case X1:
            return xvalues[1];
        case Y0:
            return yvalues[0];
        case Y1:
            return yvalues[1];
        case K0:
            return k;
        case Add:
            v1 = evaluate_term(xvalues, yvalues, k, cursor);
            v2 = evaluate_term(xvalues, yvalues, k, cursor);
            return v1 + v2;
        case Sub:
            v1 = evaluate_term(xvalues, yvalues, k, cursor);
            v2 = evaluate_term(xvalues, yvalues, k, cursor);
            return v1 - v2;
        case Mul:
            v1 = evaluate_term(xvalues, yvalues, k, cursor);
            v2 = evaluate_term(xvalues, yvalues, k, cursor);
            return v1 * v2;
        case Min:
            v1 = evaluate_term(xvalues, yvalues, k, cursor);
            v2 = evaluate_term(xvalues, yvalues, k, cursor);
            return std::min(v1, v2);
        case Max:
            v1 = evaluate_term(xvalues, yvalues, k, cursor);
            v2 = evaluate_term(xvalues, yvalues, k, cursor);
            return std::max(v1, v2);
        case LT:
            v1 = evaluate_term(xvalues, yvalues, k, cursor);
            v2 = evaluate_term(xvalues, yvalues, k, cursor);
            return v1 < v2;
        default:
            return 0;
        }
    }

    Value evaluate(const vector<Value> &xvalues, const vector<Value> &yvalues, Value k) const {
        int cursor = 0;
        return evaluate_term(xvalues, yvalues, k, cursor);
    }

    void create(DecisionSource &dec, int leaves) {
        assert(size < 64);
        assert(leaves > 0);
        if (leaves == 1) {
            if (size > 1 && nodes[size-1] == X0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == LT ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                int d = dec.get(4);
                if (d == 0) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 1) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 2) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    nodes[size++] = K0;
                }

            } else if (size > 1 && nodes[size-1] == X1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == LT ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                int d = dec.get(4);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 2) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    nodes[size++] = K0;
                }

            } else if (size > 1 && nodes[size-1] == Y0 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == Mul ||
                        nodes[size-2] == LT ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                int d = dec.get(4);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == Y1 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == Mul ||
                        nodes[size-2] == LT ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                int d = dec.get(4);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == K0) {
                int d = dec.get(4);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                }
            } else {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 3) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    nodes[size++] = K0;
                }
            }
        } else {
            // TODO make a list of reasonable options
            int d;
            if (!is_cond) {
                d = dec.get(LastNode - 1 - Add) + Add;
            } else {
                d = dec.get(LastNode - Add) + Add;
            }
            nodes[size++] = Node(d);
            switch(d) {
            case Add:
            case Mul:
            case Min:
            case Max:
            case LT:
                {
                    int leaves_on_right = dec.get(leaves/2) + 1;
                    int leaves_on_left = leaves - leaves_on_right;
                    create(dec, leaves_on_left);
                    create(dec, leaves_on_right);
                }
                break;
            case Sub:
                {
                    int leaves_on_right = dec.get(leaves - 1) + 1;
                    int leaves_on_left = leaves - leaves_on_right;
                    create(dec, leaves_on_left);
                    create(dec, leaves_on_right);
                }
                break;
            default:
                std::cerr << "Unreachable\n";
            }
        }
    }

    void print_term(int &cursor) const {
        switch(nodes[cursor++]) {
        case X0:
            std::cout << "X0";
            break;
        case X1:
            std::cout << "X1";
            break;
        case Y0:
            std::cout << "Y0";
            break;
        case Y1:
            std::cout << "Y1";
            break;
        case K0:
            std::cout << "K0";
            break;
        case Add:
            std::cout << "(";
            print_term(cursor);
            std::cout << " + ";
            print_term(cursor);
            std::cout << ")";
            break;
        case Sub:
            std::cout << "(";
            print_term(cursor);
            std::cout << " - ";
            print_term(cursor);
            std::cout << ")";
            break;
        case Mul:
            print_term(cursor);
            std::cout << "*";
            print_term(cursor);
            break;
        case Min:
            std::cout << "min(";
            print_term(cursor);
            std::cout << ", ";
            print_term(cursor);
            std::cout << ")";
            break;
        case Max:
            std::cout << "max(";
            print_term(cursor);
            std::cout << ", ";
            print_term(cursor);
            std::cout << ")";
            break;
        case LT:
            std::cout << "(";
            print_term(cursor);
            std::cout << " < ";
            print_term(cursor);
            std::cout << ")";
            break;
        default:
            assert(false);
            break;
        }
    }

    void print() const {
        int cursor = 0;
        print_term(cursor);
        std::cout << "\n";
    }

    Halide::Expr get_expr_term(int &cursor) {
        Halide::Expr result;

        switch(nodes[cursor++]) {
        case X0:
            result = kXVars[0];
            break;
        case X1:
            result = kXVars[1];
            break;
        case Y0:
            result = kYVars[0];
            break;
        case Y1:
            result = kYVars[1];
            break;
        case K0:
            result = kConstants[0];
            break;
        case Add:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                if (!lhs.defined()) {
                    return Halide::Expr();
                }
                Halide::Expr rhs = get_expr_term(cursor);
                if (!rhs.defined()) {
                    return Halide::Expr();
                }
                result = (lhs + rhs);
            }
            break;
        case Sub:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                if (!lhs.defined()) {
                    return Halide::Expr();
                }
                Halide::Expr rhs = get_expr_term(cursor);
                if (!rhs.defined()) {
                    return Halide::Expr();
                }
                result = (lhs - rhs);
            }
            break;
        case Mul:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                if (!lhs.defined()) {
                    return Halide::Expr();
                }
                Halide::Expr rhs = get_expr_term(cursor);
                if (!rhs.defined()) {
                    return Halide::Expr();
                }
                result = (lhs * rhs);
            }
            break;
        case Min:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                if (!lhs.defined()) {
                    return Halide::Expr();
                }
                Halide::Expr rhs = get_expr_term(cursor);
                if (!rhs.defined()) {
                    return Halide::Expr();
                }
                result = Halide::min(lhs, rhs);
            }
            break;
        case Max:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                if (!lhs.defined()) {
                    return Halide::Expr();
                }
                Halide::Expr rhs = get_expr_term(cursor);
                if (!rhs.defined()) {
                    return Halide::Expr();
                }
                result = Halide::max(lhs, rhs);
            }
            break;
        case LT:
            {
                if (fail) {
                    return Halide::Expr();
                }
                Halide::Expr lhs = get_expr_term(cursor);
                if (fail || !lhs.defined()) {
                    return Halide::Expr();
                }
                Halide::Expr rhs = get_expr_term(cursor);
                if (fail || !rhs.defined()) {
                    return Halide::Expr();
                }
                fail = true;
                result = Halide::Internal::LT::make(lhs, rhs);
            }
            break;
        default:
            assert(false);
            break;
        }
        return result;
    }

    Halide::Expr get_expr() {
        int cursor = 0;
        fail = false;
        return get_expr_term(cursor);
    }
};

bool generate_expr(int index, uint64_t leaves, uint64_t i, set<TupleExpr> &seen, TupleExpr &e) {
    string shift = "";
    for (int a = 0; a < index; ++a) {
        shift += "\t";
    }

    e = TupleExpr();
    DecisionSource dec;
    dec.val = i;
    e.create(dec, leaves);

    if (dec.val == 0) {
        if (seen.find(e) != seen.end()) {
            return true;
        }
        seen.insert(e);
        return false;
    } else {
        return true;
    }
}

bool fast_check_associativity(vector<TupleExpr> &cond_eqs, vector<TupleExpr> &true_eqs,
                              vector<TupleExpr> &false_eqs, const set<AssocTuple> &associative_sets) {
    if (associative_sets.find(AssocTuple(cond_eqs)) != associative_sets.end()) {
        return false;
    }
    size_t size = cond_eqs.size();
    bool associative = true;
    bool uses_y = false, uses_x = false;
    for (int trial = 0; trial < 250; trial++) {
        vector<Value> xvalues(size), yvalues(size), zvalues(size);
        for (size_t i = 0; i < size; ++i) {
            xvalues[i] = random_value();
            yvalues[i] = random_value();
            zvalues[i] = random_value();
        }
        Value k = random_value();

        // Check it depends on x and y in some meaningful way
        vector<Value> v_xy(size), v_yz(size), v_xz(size);

        for (size_t i = 0; i < size; ++i) {
            v_xy[i] = cond_eqs[i].evaluate(xvalues, yvalues, k) ? true_eqs[i].evaluate(xvalues, yvalues, k) : false_eqs[i].evaluate(xvalues, yvalues, k);
            v_yz[i] = cond_eqs[i].evaluate(yvalues, zvalues, k) ? true_eqs[i].evaluate(yvalues, zvalues, k) : false_eqs[i].evaluate(yvalues, zvalues, k);
            v_xz[i] = cond_eqs[i].evaluate(xvalues, zvalues, k) ? true_eqs[i].evaluate(xvalues, zvalues, k) : false_eqs[i].evaluate(xvalues, zvalues, k);

            if (v_xy[i] != v_xz[i]) {
                uses_y = true;
            }
            if (v_xz[i] != v_yz[i]) {
                uses_x = true;
            }
        }

        // Check if it's associative
        vector<Value> v_x_yz(size), v_xy_z(size);
        for (size_t i = 0; i < size; ++i) {
            v_x_yz[i] = cond_eqs[i].evaluate(xvalues, v_yz, k) ? true_eqs[i].evaluate(xvalues, v_yz, k) : false_eqs[i].evaluate(xvalues, v_yz, k);
            v_xy_z[i] = cond_eqs[i].evaluate(v_xy, zvalues, k) ? true_eqs[i].evaluate(v_xy, zvalues, k) : false_eqs[i].evaluate(v_xy, zvalues, k);
            if (v_x_yz[i] != v_xy_z[i]) {
                associative = false;
                break;
            }
        }
    }

    bool skip = !(associative && uses_x && uses_y);
    if (skip) {
        vector<Halide::Expr> temp(size);
        for (size_t i = 0; i < size; ++i) {
            temp[i] = Halide::select(cond_eqs[i].get_expr(), true_eqs[i].get_expr(), false_eqs[i].get_expr());
        }
        DEBUG_PRINT3 << "...Skip " << Halide::Tuple(temp) << "\t; associative? " << associative
                     << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
    }
    return skip;
}

Point morton_to_coordinate(uint32_t morton) {
    int multiplier = morton/8;
    morton = morton % 8;

    uint32_t leaves_tile, i_tile;
    morton2(morton, leaves_tile, i_tile);

    i_tile += multiplier*4;
    uint64_t leaves = leaves_tile * LEAVES_TILE + START_LEAVES;
    uint64_t i = i_tile * ITER_TILE;

    return {leaves, i};
}

int main(int argc, char **argv) {
    vector<set<TupleExpr>> seen(2);
    uint32_t MORTON_MIN = 0;
    uint32_t MORTON_MAX = 2;

    if (argc > 1) {
        MORTON_MIN = atoi(argv[1]);
    }
    if (argc > 2) {
        MORTON_MAX = atoi(argv[2]);
    }
    std::cout << "Morton min: " << MORTON_MIN << ", Morton max: " << MORTON_MAX << "\n\n";

    vector<IntervalSet> invalid(9);
    vector<set<TupleExpr>> seen0(9);

    vector<set<AssocTuple>> associative_sets(9);

    uint64_t valid = 0;
    for (uint32_t morton = MORTON_MIN; morton <= MORTON_MAX; ++morton) {
        Point point = morton_to_coordinate(morton);
        uint64_t leaves_start = std::max(point.leaves, START_LEAVES);
        uint64_t leaves_end =  std::min(point.leaves + LEAVES_TILE - 1, MAX_LEAVES);
        //uint64_t leaves_start = 4, leaves_end = 4;
        uint64_t i_start = point.i;
        uint64_t i_end = point.i + ITER_TILE - 1;

        std::cout << "Morton: " << morton << ", leaves: [" << leaves_start
                  << ", " << leaves_end << "], i: [" << i_start << ", "
                  << i_end << "]" << "\n";

        for (uint64_t leaves0 = leaves_start; leaves0 <= leaves_end; ++leaves0) {
            IntervalSet i0_range;
            i0_range.insert(IntervalVal::closed(i_start, i_end));
            i0_range -= invalid[leaves0];
            for (auto it0 = i0_range.begin(); it0 != i0_range.end(); it0++){
                for (uint64_t i0 = it0->lower(); i0 <= it0->upper(); ++i0) {
                    if (boost::icl::contains(invalid[leaves0], i0)) {
                        DEBUG_PRINT2 << "...Skip leaves0: " << leaves0 << ", i0: " << i0 << "\n";
                        continue;
                    }

                    TupleExpr e0;
                    bool skip_e0 = generate_expr(0, leaves0, i0, seen0[leaves0], e0);
                    skip_e0 = skip_e0 || should_skip_expression(0, e0.get_expr(), e0.fail, e0.uses_x, e0.uses_y, kXNames, kYNames, kConstantNames);
                    if (skip_e0) {
                        invalid[leaves0].insert(i0);
                        continue;
                    }

                    //Halide::Expr expr = (kXVars[0] * kYVars[0]) - (kXVars[1] * kYVars[1]);
                    /*Halide::Expr expr = (kXVars[0] * kYVars[1]) + (kXVars[1] * kYVars[0]);
                    if (equal(e0.get_expr(), expr)) {
                        std::cout << "***FOUND EXPR after i0: " << i0 << "; expr: " << e0.get_expr() << "\n";
                        return 0;
                    }*/

                    //std::cout << "Leaves0: " << leaves0 << ", i0: " << i0 << ", expr: " << e0.get_expr() << ", valid: " << valid << "\n";

                    for (uint64_t leaves1 = leaves_start; leaves1 <= leaves_end; ++leaves1) {
                        IntervalSet i1_range;
                        i1_range.insert(IntervalVal::closed(i_start, i_end));
                        i1_range -= invalid[leaves1];
                        for (auto it1 = i1_range.begin(); it1 != i1_range.end(); it1++){
                            for (uint64_t i1 = it1->lower(); i1 <= it1->upper(); ++i1) {
                                if (boost::icl::contains(invalid[leaves1], i1)) {
                                    DEBUG_PRINT2 << "......Skip leaves1: " << leaves1 << ", i1: " << i1 << "\n";
                                    continue;
                                }

                                TupleExpr e1;
                                bool skip_e1 = generate_expr(1, leaves1, i1, seen[1], e1);
                                if (Halide::Internal::equal(e0.get_expr(), e1.get_expr())) {
                                    continue;
                                }
                                skip_e1 = skip_e1 || should_skip_expression(1, e1.get_expr(), e1.fail, e1.uses_x, e1.uses_y, kXNames, kYNames, kConstantNames);
                                if (skip_e1) {
                                    invalid[leaves1].insert(i1);
                                    continue;
                                }
                                //std::cout << "Leaves1: " << leaves1 << ", i1: " << i1 << ", expr: " << e1.get_expr() << "\n";

                                // Check asssociativity
                                /*vector<TupleExpr> eqs = {e0, e1};
                                if (!fast_check_associativity(eqs, associative_sets[leaves0])) {
                                    vector<Halide::Expr> halide_exprs = {e0.get_expr(), e1.get_expr()};
                                    vector<vector<bool>> eqs_uses_x = {e0.uses_x, e1.uses_x};
                                    if (is_decomposable(eqs_uses_x)) {
                                        std::cout << "......Skip decomposable exprs: " << Halide::Tuple(halide_exprs) << "\n";
                                        continue;
                                    }
                                    if (z3_check_associativity(halide_exprs, kXVars, kYVars, kConstants, {leaves0, leaves1}, {i0, i1})) {
                                        associative_sets[leaves0].insert(AssocTuple(e0, e1));
                                        valid++;
                                    }
                                }*/
                            }
                        }
                    }
                    seen[1] = set<TupleExpr>();
                }
            }
        }
        std::cout << "Valid: " << valid << "\n";
        std::cout << "**************************************************************************\n\n";
    }
    return 0;
}
