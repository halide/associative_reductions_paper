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

const uint64_t START_LEAVES = 2;
const uint64_t MAX_LEAVES = 7;
const uint64_t LEAVES_TILE = 3;
const uint64_t ITER_TILE = 60000;

Halide::Type kType = Halide::Int(32);
vector<string> kXNames = {"x0", "x1", "x2"};
vector<string> kYNames = {"y0", "y1", "y2"};
vector<string> kConstantNames = {"k0"};
vector<Halide::Expr> kXVars = {
    Variable::make(kType, "x0"),
    Variable::make(kType, "x1"),
    Variable::make(kType, "x2"),
};
vector<Halide::Expr> kYVars = {
    Variable::make(kType, "y0"),
    Variable::make(kType, "y1"),
    Variable::make(kType, "y2"),
};
vector<Halide::Expr> kConstants = {
    Variable::make(kType, "k0"),
};

enum Node : long {
    X0 = 0,
    Y0,
    X1,
    Y1,
    X2,
    Y2,
    K0,
    Add,
    Mul,
    LastNode,
    Min,
    Max,
    Sub,
};

class TupleExpr : public Expr {
public:
    TupleExpr() : Expr(3) {}

    Value evaluate_term(const vector<Value> &xvalues, const vector<Value> &yvalues, Value k, int &cursor) const {
        Value v1, v2;
        switch(nodes[cursor++]) {
        case X0:
            return xvalues[0];
        case X1:
            return xvalues[1];
        case X2:
            return xvalues[2];
        case Y0:
            return yvalues[0];
        case Y1:
            return yvalues[1];
        case Y2:
            return yvalues[2];
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
            /*if (size > 1 && nodes[size-1] == X0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(x, x)
                int d = dec.get(3);
                if (d == 0) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 1) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == X1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(x, x)
                int d = dec.get(3);
                if (d == 0) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 1) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == X2 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(x, x)
                int d = dec.get(3);
                if (d == 0) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 1) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == Y0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(y, y)
                int d = dec.get(3);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                }
            } else if (size > 1 && nodes[size-1] == Y1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(y, y)
                int d = dec.get(3);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                }
            } else if (size > 1 && nodes[size-1] == Y2 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Mul ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(y, y)
                int d = dec.get(3);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                }
            } else {
                int d = dec.get(6);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 4) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            }*/

            /*if (size > 1 && nodes[size-1] == X0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(x, x)
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 1) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 2) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 3) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == X1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 2) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 3) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == X2 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
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
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == Y0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == Y1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == Y2 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                }
            } else {
                int d = dec.get(6);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 4) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            }*/


            // With constants
            if (size > 1 && nodes[size-1] == X0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                // avoid min(x, x)
                int d = dec.get(6);
                if (d == 0) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 1) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 2) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 3) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else if (d == 4) {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == X1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(6);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 2) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 3) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else if (d == 4) {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == X2 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(6);
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
                } else if (d == 4) {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == Y0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == Y1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                }
            } else if (size > 1 && nodes[size-1] == Y2 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Sub ||
                 nodes[size-2] == Add)) {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                }
            } else if (size > 1 && nodes[size-1] == K0) {
                int d = dec.get(3);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                }
            } else {
                int d = dec.get(7);
                if (d == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x[1] = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_x[2] = true;
                    nodes[size++] = X2;
                } else if (d == 3) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else if (d == 4) {
                    uses_y[1] = true;
                    nodes[size++] = Y1;
                } else if (d == 5) {
                    uses_y[2] = true;
                    nodes[size++] = Y2;
                } else {
                    nodes[size++] = K0;
                }
            }
        } else {
            // TODO make a list of reasonable options
            int d = dec.get(LastNode - Add) + Add;
            nodes[size++] = Node(d);
            switch(d) {
            case Add:
            case Mul:
            case Min:
            case Max:
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
        case X2:
            std::cout << "X2";
            break;
        case Y0:
            std::cout << "Y0";
            break;
        case Y1:
            std::cout << "Y1";
            break;
        case Y2:
            std::cout << "Y2";
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
        case X2:
            result = kXVars[2];
            break;
        case Y0:
            result = kYVars[0];
            break;
        case Y1:
            result = kYVars[1];
            break;
        case Y2:
            result = kYVars[2];
            break;
        case K0:
            result = kConstants[0];
            break;
        case Add:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                Halide::Expr rhs = get_expr_term(cursor);
                result = (lhs + rhs);
            }
            break;
        case Sub:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                Halide::Expr rhs = get_expr_term(cursor);
                result = (lhs - rhs);
            }
            break;
        case Mul:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                Halide::Expr rhs = get_expr_term(cursor);
                result = (lhs * rhs);
            }
            break;
        case Min:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                Halide::Expr rhs = get_expr_term(cursor);
                result = Halide::min(lhs, rhs);
            }
            break;
        case Max:
            {
                Halide::Expr lhs = get_expr_term(cursor);
                Halide::Expr rhs = get_expr_term(cursor);
                result = Halide::max(lhs, rhs);
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

bool fast_check_associativity(vector<TupleExpr> &eqs, const set<AssocTuple> &associative_set) {
    size_t size = eqs.size();

    if (associative_set.find(AssocTuple(eqs)) != associative_set.end()) {
        // We've already proved it's associative, no need to redo things
        vector<Halide::Expr> temp(size);
        for (size_t i = 0; i < size; ++i) {
            temp[i] = eqs[i].get_expr();
        }
        DEBUG_PRINT2 << "......Skip proven non-associative exprs: " << Halide::Tuple(temp) << "\n";
        return false;
    }

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
            v_xy[i] = eqs[i].evaluate(xvalues, yvalues, k);
            v_yz[i] = eqs[i].evaluate(yvalues, zvalues, k);
            v_xz[i] = eqs[i].evaluate(xvalues, zvalues, k);

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
            v_x_yz[i] = eqs[i].evaluate(xvalues, v_yz, k);
            v_xy_z[i] = eqs[i].evaluate(v_xy, zvalues, k);
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
            temp[i] = eqs[i].get_expr();
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

template <typename T>
std::ostream &operator<<(std::ostream &out, const vector<T> &v) {
    out << '[';
    for (size_t i = 0; i < v.size(); ++i) {
        out << v[i];
        if (i < v.size() - 1) {
            out << ", ";
        }
    }
    out << "]";
    return out;
}

int main(int argc, char **argv) {
    vector<set<TupleExpr>> seen(3);
    uint32_t MORTON_MIN = 0;
    uint32_t MORTON_MAX = 0;

    if (argc > 1) {
        MORTON_MIN = atoi(argv[1]);
    }
    if (argc > 2) {
        MORTON_MAX = atoi(argv[2]);
    }
    std::cout << "Running three-element tuple generator of type: " << kType << "\n";
    std::cout << "Morton min: " << MORTON_MIN << ", Morton max: " << MORTON_MAX << "\n\n";

    vector<IntervalSet> invalid(9);
    vector<set<TupleExpr>> seen0(9);

    vector<set<AssocTuple>> associative_sets(9);

    for (uint32_t morton = MORTON_MIN; morton <= MORTON_MAX; ++morton) {
        Point point = morton_to_coordinate(morton);
        //uint64_t leaves_start = std::max(point.leaves, START_LEAVES);
        //uint64_t leaves_end =  std::min(point.leaves + LEAVES_TILE - 1, MAX_LEAVES);
        uint64_t leaves_start = 3, leaves_end = 3;
        uint64_t i_start = point.i;
        uint64_t i_end = point.i + ITER_TILE - 1;

        std::cout << "Morton: " << morton << ", leaves: [" << leaves_start
                  << ", " << leaves_end << "], i: [" << i_start << ", "
                  << i_end << "]" << "\n";

        int valid = 0, decomposable = 0;
        for (uint64_t leaves0 = leaves_start; leaves0 <= leaves_end; ++leaves0) {
            IntervalSet i0_range;
            i0_range.insert(IntervalVal::closed(i_start, i_end));
            i0_range -= invalid[leaves0];

            Halide::Expr expr0, expr1, expr2;
            for (auto it0 = i0_range.begin(); it0 != i0_range.end(); it0++) {
                for (uint64_t i0 = it0->lower(); i0 <= it0->upper(); ++i0) {
                    if (boost::icl::contains(invalid[leaves0], i0)) {
                        DEBUG_PRINT2 << "...Skip leaves0: " << leaves0 << ", i0: " << i0 << "\n";
                        continue;
                    }

                    TupleExpr e0;
                    bool skip_e0 = generate_expr(0, leaves0, i0, seen0[leaves0], e0);
                    expr0 = e0.get_expr();
                    skip_e0 = skip_e0 || should_skip_expression(0, expr0, e0.fail, e0.uses_x, e0.uses_y, kXNames, kYNames, kConstantNames);
                    if (skip_e0) {
                        invalid[leaves0].insert(i0);
                        continue;
                    }

                    //std::cout << "Leaves0: " << leaves0 << ", i0: " << i0 << ", expr: " << expr0 << ", valid: " << valid << "\n";

                    for (uint64_t leaves1 = leaves_start; leaves1 <= leaves_end; ++leaves1) {
                        IntervalSet i1_range;
                        i1_range.insert(IntervalVal::closed(i_start, i_end));
                        //i1_range.insert(IntervalVal::closed(37382, 37382));
                        i1_range -= invalid[leaves1];
                        for (auto it1 = i1_range.begin(); it1 != i1_range.end(); it1++) {
                            for (uint64_t i1 = it1->lower(); i1 <= it1->upper(); ++i1) {
                                if (boost::icl::contains(invalid[leaves1], i1)) {
                                    DEBUG_PRINT2 << "......Previously invalid skip leaves1: " << leaves1 << ", i1: " << i1 << "\n";
                                    continue;
                                }
                                TupleExpr e1;
                                bool skip_e1 = generate_expr(1, leaves1, i1, seen[1], e1);
                                expr1 = e1.get_expr();
                                if (Halide::Internal::equal(expr0, expr1)) {
                                    DEBUG_PRINT2 << "......Skip leaves1 equal: " << leaves1 << ", i1: " << i1 << "\n";
                                    continue;
                                }
                                skip_e1 = skip_e1 || should_skip_expression(1, expr1, e1.fail, e1.uses_x, e1.uses_y, kXNames, kYNames, kConstantNames);
                                if (skip_e1) {
                                    DEBUG_PRINT2 << "......Skip leaves1: " << leaves1 << ", i1: " << i1 << "\n";
                                    invalid[leaves1].insert(i1);
                                    continue;
                                }
                                //std::cout << "Leaves1: " << leaves1 << ", i1: " << i1 << ", expr: " << expr1 << "\n";

                                for (uint64_t leaves2 = leaves_start; leaves2 <= leaves_end; ++leaves2) {
                                    IntervalSet i2_range;
                                    i2_range.insert(IntervalVal::closed(i_start, i_end));
                                    //i2_range.insert(IntervalVal::closed(53014, 53014));
                                    i2_range -= invalid[leaves2];
                                    for (auto it2 = i2_range.begin(); it2 != i2_range.end(); it2++) {
                                        for (uint64_t i2 = it2->lower(); i2 <= it2->upper(); ++i2) {
                                            if (boost::icl::contains(invalid[leaves2], i2)) {
                                                DEBUG_PRINT2 << "......Skip leaves2: " << leaves2 << ", i2: " << i2 << "\n";
                                                continue;
                                            }
                                            TupleExpr e2;
                                            bool skip_e2 = generate_expr(2, leaves2, i2, seen[2], e2);
                                            expr2 = e2.get_expr();
                                            if (Halide::Internal::equal(expr0, expr2) ||
                                                Halide::Internal::equal(expr1, expr2)) {
                                                DEBUG_PRINT2 << "......Skip leaves2 equal: " << leaves2 << ", i2: " << i2 << "\n";
                                                continue;
                                            }
                                            skip_e2 = skip_e2 || should_skip_expression(2, expr2, e2.fail, e2.uses_x, e2.uses_y, kXNames, kYNames, kConstantNames);
                                            if (skip_e2) {
                                                invalid[leaves2].insert(i2);
                                                continue;
                                            }
                                            //std::cout << "Leaves2: " << leaves2 << ", i2: " << i2 << ", expr: " << expr2 << "\n";

                                            vector<Halide::Expr> halide_exprs = {expr0, expr1, expr2};

                                            /*Halide::Expr expr0 = (kXVars[0] + kYVars[0]);
                                            Halide::Expr expr1 = (kXVars[1] + kYVars[0]);
                                            Halide::Expr expr2 = (kXVars[2] * kYVars[2]);
                                            if (equal(expr0, halide_exprs[0]) && equal(expr1, halide_exprs[1]) && equal(expr2, halide_exprs[2])) {
                                                std::cout << "***FOUND EXPR after i0: " << i0 << "; expr: " << Halide::Tuple(halide_exprs) << "\n";
                                                std::cout << "e0.uses_x: " << e0.uses_x << "\n";
                                                std::cout << "e1.uses_x: " << e1.uses_x << "\n";
                                                std::cout << "e2.uses_x: " << e2.uses_x << "\n";
                                                std::cout << "e0.uses_y: " << e0.uses_y << "\n";
                                                std::cout << "e1.uses_y: " << e1.uses_y << "\n";
                                                std::cout << "e2.uses_y: " << e2.uses_y << "\n";
                                                vector<vector<bool>> eqs_uses_x = {e0.uses_x, e1.uses_x, e2.uses_x};
                                                vector<vector<bool>> eqs_uses_y = {e0.uses_y, e1.uses_y, e2.uses_y};
                                                std::cout << "decomposable? " << is_decomposable(eqs_uses_x, eqs_uses_y) << "\n";
                                                return 0;
                                            }*/

                                            // Check asssociativity
                                            vector<TupleExpr> eqs = {e0, e1, e2};
                                            if (!fast_check_associativity(eqs, associative_sets[leaves0])) {
                                                std::cout << "Leaves0: " << leaves0 << ", i0: " << i0 << ", leaves1: " << leaves1
                                                          << ", i1: " << i1 << ", leaves2: " << leaves2 << ", i2: " << i2 << ", expr:"
                                                          << Halide::Tuple(halide_exprs) << "\n";

                                                vector<vector<bool>> eqs_uses_x = {e0.uses_x, e1.uses_x, e2.uses_x};
                                                vector<vector<bool>> eqs_uses_y = {e0.uses_y, e1.uses_y, e2.uses_y};
                                                /*if (is_decomposable(eqs_uses_x, eqs_uses_y)) {
                                                    DEBUG_PRINT2 << "......Skip decomposable exprs: " << Halide::Tuple(halide_exprs) << "\n";
                                                    continue;
                                                }*/
                                                if (z3_check_associativity(halide_exprs, kXVars, kYVars, kConstants,
                                                                           {leaves0, leaves1, leaves2},
                                                                           {i0, i1, i2})) {
                                                    associative_sets[leaves0].insert(AssocTuple(e0, e1, e2));
                                                    valid++;
                                                    if (is_decomposable(eqs_uses_x, eqs_uses_y)) {
                                                        std::cout << "......Skip decomposable exprs: " << Halide::Tuple(halide_exprs) << "\n";
                                                        decomposable++;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                seen[2] = set<TupleExpr>();
                            }
                        }
                    }
                    seen[1] = set<TupleExpr>();
                }
            }
        }
        std::cout << "Valid: " << valid << ", decomposable: " << decomposable << "\n";
        std::cout << "**************************************************************************\n\n";
    }
    return 0;
}
