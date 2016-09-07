#include "Halide.h"
#include "Error.h"
#include "Utilities.h"

#include <iostream>
#include <cstdlib>
#include <cassert>
#include <cmath>
#include <vector>
#include <map>
#include <stdint.h>

using std::pair;
using std::string;
using std::vector;
using Halide::Internal::Variable;
using Halide::Internal::unique_name;

Halide::Type kType = Halide::UInt(32);
vector<string> kXNames = {"x0"};
vector<string> kYNames = {"y0"};
vector<string> kConstantNames = {"k0"};
vector<Halide::Expr> kXVars = {Variable::make(kType, "x0")};
vector<Halide::Expr> kYVars = {Variable::make(kType, "y0")};
vector<Halide::Expr> kConstants = {Variable::make(kType, "k0")};

enum Node : long {
    X0 = 0,
    Y0,
    K0,
    Add,
    Sub,
    Mul,
    Min,
    Max,
    LastNode,
};

class SingleExpr : public Expr {
public:
    SingleExpr() : Expr(1) {}

    Value evaluate_term(const vector<Value> &xvalues, const vector<Value> &yvalues, Value k, int &cursor) const {
        Value v1, v2;
        switch(nodes[cursor++]) {
        case X0:
            return xvalues[0];
        case Y0:
            return yvalues[0];
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
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                if (dec.get(2)) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == Y0 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                uses_x[0] = true;
                nodes[size++] = X0;
            } else if (size > 1 && nodes[size-1] == K0) {
                uses_x[0] = true;
                nodes[size++] = X0;
            } else {
                int code = dec.get(3);
                if (code == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (code == 1) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }
            }*/

            if (size > 1 && nodes[size-1] == X0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                if (dec.get(2)) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == Y0 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                if (dec.get(2)) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == K0) {
                if (dec.get(2)) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                }
            } else {
                int code = dec.get(3);
                if (code == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else if (code == 1) {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }
            }

            // No constants
            /*if (size > 1 && nodes[size-1] == X0 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                uses_y[0] = true;
                nodes[size++] = Y0;
            } else if (size > 1 && nodes[size-1] == Y0 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                uses_x[0] = true;
                nodes[size++] = X0;
            } else if (size > 1 && nodes[size-1] == K0) {
                uses_x[0] = true;
                nodes[size++] = X0;
            } else {
                int code = dec.get(2);
                if (code == 0) {
                    uses_x[0] = true;
                    nodes[size++] = X0;
                } else {
                    uses_y[0] = true;
                    nodes[size++] = Y0;
                }
            }*/
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
        case Y0:
            std::cout << "Y0";
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

    Halide::Expr get_expr_term(int &cursor) const {
        Halide::Expr result;

        switch(nodes[cursor++]) {
        case X0:
            result = kXVars[0];
            break;
        case Y0:
            result = kYVars[0];
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

    Halide::Expr get_expr() const {
        int cursor = 0;
        return get_expr_term(cursor);
    }
};

int main(int argc, char **argv) {
    vector<SingleExpr> leave_start_expr;
    leave_start_expr.reserve(32);

    uint64_t MIN_LEAVES = 8;
    uint64_t MAX_LEAVES = 8;
    if (argc > 1) {
        MIN_LEAVES = atoi(argv[1]);
    }
    if (argc > 2) {
        MAX_LEAVES = atoi(argv[2]);
    }
    std::cout << "Running single element generator of type: " << kType << "\n";
    std::cout << "Min leaves: " << MIN_LEAVES << ", max leaves: " << MAX_LEAVES << "\n\n";

    uint64_t fails = 0, valid = 0;
    uint64_t leaves = MIN_LEAVES;
    std::cout << "\n******************************************************************\n";
    std::cout << "Leaves: " << leaves << "\n";
    for (uint64_t i = 0;; i++) {
        SingleExpr e;
        DecisionSource dec;
        dec.val = i;
        e.create(dec, leaves);

        //std::cout << "Leaves: " << leaves << ", i: " << i << ", expr: " << e.get_expr() << ", valid: " << valid << "\n";

        //Halide::Expr expected = Halide::max(Halide::min(kXVars[0], kConstants[0]), kYVars[0]);
        /*Halide::Expr expected = Halide::min(kXVars[0], kConstants[0]);
        if (equal(e.get_expr(), expected)) {
            std::cout << "***FOUND EXPR after i: " << i << "; expr: " << expected << "\n";
            return 0;
        }*/

        bool repeat = false;
        if (leave_start_expr.size() < leaves) {
            leave_start_expr.push_back(e);
        } else {
            SingleExpr prev = leave_start_expr[leaves - 1];
            repeat = (prev == e);
        }
        if (repeat) {
            std::cout << "Total: " << i << ", fails: " << fails << ", repeat at: " << e.get_expr() << "\n";
            std::cout << "Valid: " << valid << "\n";
            std::cout << "**************************************************************************\n";
            leaves++;
            i = 0;
            fails = 0;
            std::cout << "\n******************************************************************\n";
            std::cout << "Leaves: " << leaves << "\n";
            std::cout.flush();
            dec.val = i;
            e = SingleExpr();
            e.create(dec, leaves);
            assert(leave_start_expr.size() < leaves);
            leave_start_expr.push_back(e);
        }

        if (leaves > MAX_LEAVES) {
            return 0;
        }

        bool skip = should_skip_expression(0, e.get_expr(), e.fail, e.uses_x, e.uses_y, kXNames, kYNames, kConstantNames);
        if (skip) {
            continue;
        }

        bool associative = true;
        bool uses_x = false, uses_y = false;
        for (int trial = 0; trial < 250; trial++) {
            Value x = random_value(), y = random_value(), z = random_value(), k = random_value();
            // Check it depends on x and y in some meaningful way
            Value v_xy = e.evaluate({x}, {y}, k);
            Value v_yz = e.evaluate({y}, {z}, k);
            Value v_xz = e.evaluate({x}, {z}, k);
            if (v_xy != v_xz) {
                uses_y = true;
            }
            if (v_xz != v_yz) {
                uses_x = true;
            }

            // Check it's associative
            Value v_x_yz = e.evaluate({x}, {v_yz}, k);
            Value v_xy_z = e.evaluate({v_xy}, {z}, k);
            if (v_x_yz != v_xy_z) {
                associative = false;
                break;
            }
        }

        if (associative && uses_x && uses_y) {
            vector<Halide::Expr> halide_exprs = {e.get_expr()};
            if (z3_check_associativity(halide_exprs, kXVars, kYVars, kConstants, {leaves}, {i})) {
                valid++;
            }
        } else {
            fails++;
            DEBUG_PRINT2 << "...Skip " << i << ": " << e.get_expr() << "\t; uses_x: " << uses_x
                         << "; uses_y: " << uses_y << "; associative: " << associative << "\n";
        }
    }
    return 0;
}