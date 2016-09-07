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

Halide::Type kType = Halide::Int(32);
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
    LT,
    LastNode,
    GT,
    EQ,
    NE,
};

class SingleExpr : public Expr {
public:
    bool is_cond;

    SingleExpr(bool is_cond) : Expr(1), is_cond(is_cond) {}
    SingleExpr() : Expr(1), is_cond(false) {}

    Value evaluate_term(Value x, Value y, Value k, int &cursor) {
        Value v1, v2;
        switch(nodes[cursor++]) {
        case X0:
            return x;
        case Y0:
            return y;
        case K0:
            return k;
        case Add:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return v1 + v2;
        case Sub:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return v1 - v2;
        case Mul:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return v1 * v2;
        case Min:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return std::min(v1, v2);
        case Max:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return std::max(v1, v2);
        case LT:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return v1 < v2;
        case EQ:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return v1 == v2;
        case NE:
            v1 = evaluate_term(x, y, k, cursor);
            v2 = evaluate_term(x, y, k, cursor);
            return v1 != v2;
        default:
            return 0;
        }
    }

    Value evaluate(Value x, Value y, Value k) {
        int cursor = 0;
        return evaluate_term(x, y, k, cursor);
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
                 nodes[size-2] == GT ||
                 nodes[size-2] == EQ ||
                 nodes[size-2] == NE ||
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
                        nodes[size-2] == Mul ||
                        nodes[size-2] == LT ||
                        nodes[size-2] == GT ||
                        nodes[size-2] == EQ ||
                        nodes[size-2] == NE ||
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
        } else {
            // TODO make a list of reasonable options
            int d;
            if (!is_cond) {
                d = dec.get(LastNode - 1 - Add) + Add;
            } else {
                d = LT;
                is_cond = false;
            }
            nodes[size++] = Node(d);
            switch(d) {
            case Add:
            case Mul:
            case Min:
            case Max:
            case LT:
            case GT:
            case EQ:
            case NE:
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
                assert(false);
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
        case LT:
            std::cout << "(";
            print_term(cursor);
            std::cout << " < ";
            print_term(cursor);
            std::cout << ")";
            break;
        case GT:
            std::cout << "(";
            print_term(cursor);
            std::cout << " > ";
            print_term(cursor);
            std::cout << ")";
            break;
        case EQ:
            std::cout << "(";
            print_term(cursor);
            std::cout << " == ";
            print_term(cursor);
            std::cout << ")";
            break;
        case NE:
            std::cout << "(";
            print_term(cursor);
            std::cout << " != ";
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
        case Y0:
            result = kYVars[0];
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
        case GT:
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
                result = Halide::Internal::GT::make(lhs, rhs);
            }
            break;
        case EQ:
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
                result = Halide::Internal::EQ::make(lhs, rhs);
            }
            break;
        case NE:
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
                result = Halide::Internal::NE::make(lhs, rhs);
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

int main(int argc, char **argv) {
    vector<SingleExpr> leave_start_expr_cond;
    leave_start_expr_cond.reserve(32);

    const uint64_t MAX_LEAVES_COND = 6;
    const uint64_t MAX_LEAVES = 6;
    const uint64_t START_LEAVES_COND = 1;
    const uint64_t START_LEAVES = 1;

    uint64_t fails = 0, valid = 0;
    uint64_t leaves_cond = START_LEAVES_COND, leaves_true = START_LEAVES, leaves_false = START_LEAVES;
    std::cout << "\n******************************************************************\n";
    std::cout << "Leaves: " << leaves_cond << ", valid: " << valid << "\n";

    SingleExpr e_cond(true), e_true, e_false;
    for (uint64_t i = 0;; i++) {
        e_cond = SingleExpr(true);
        DecisionSource dec_cond;
        dec_cond.val = i;
        e_cond.create(dec_cond, leaves_cond);

        bool repeat = false;
        if (leave_start_expr_cond.size() < leaves_cond) {
            leave_start_expr_cond.push_back(e_cond);
        } else {
            SingleExpr prev = leave_start_expr_cond[leaves_cond - 1];
            repeat = (prev == e_cond);
        }
        if (repeat) {
            std::cout << "Total: " << i << ", fails: " << fails << ", repeat at: " << e_cond.get_expr() << "\n";
            std::cout << "Valid: " << valid << "\n";
            std::cout << "**************************************************************************\n";
            leaves_cond++;
            i = 0;
            fails = 0;
            std::cout << "\n******************************************************************\n";
            std::cout << "Leaves: " << leaves_cond << "\n";
            dec_cond.val = i;
            e_cond = SingleExpr(true);
            e_cond.create(dec_cond, leaves_cond);
            assert(leave_start_expr_cond.size() < leaves_cond);
            leave_start_expr_cond.push_back(e_cond);
        }
        if (leaves_cond > MAX_LEAVES_COND) {
            return 0;
        }

        if (!e_cond.get_expr().defined() || !e_cond.get_expr().type().is_bool()) {
            continue;
        }

        //e_cond.print();
        //std::cout << "e_cond: " << e_cond.get_expr() << "\n";
        vector<SingleExpr> leave_start_expr_true;
        leave_start_expr_true.reserve(32);
        for (uint64_t j = 0;; j++) {
            e_true = SingleExpr();
            DecisionSource dec_true;
            dec_true.val = j;
            e_true.create(dec_true, leaves_true);

            bool repeat = false;
            if (leave_start_expr_true.size() < leaves_true) {
                leave_start_expr_true.push_back(e_true);
            } else {
                SingleExpr prev = leave_start_expr_true[leaves_true - 1];
                repeat = (prev == e_true);
            }
            if (repeat) {
                DEBUG_PRINT2 << "\tTotal: " << j << ", fails: " << fails << ", repeat at: " << e_true.get_expr() << "\n";
                leaves_true++;
                j = 0;
                fails = 0;
                DEBUG_PRINT2 << "\n\t******************************************************************\n";
                DEBUG_PRINT2 << "\tLeaves: " << leaves_true << "\n";
                dec_true.val = j;
                e_true = SingleExpr();
                e_true.create(dec_true, leaves_true);
                assert(leave_start_expr_true.size() < leaves_true);
                leave_start_expr_true.push_back(e_true);
            }
            if (leaves_true > MAX_LEAVES) {
                leaves_true = START_LEAVES;
                break;
            }

            //std::cout << "\te_true: " << e_true.get_expr() << "\n";
            vector<SingleExpr> leave_start_expr_false;
            leave_start_expr_false.reserve(32);
            for (uint64_t k = 0;; k++) {
                e_false = SingleExpr();
                DecisionSource dec_false;
                dec_false.val = k;
                e_false.create(dec_false, leaves_false);

                bool repeat = false;
                if (leave_start_expr_false.size() < leaves_false) {
                    leave_start_expr_false.push_back(e_false);
                } else {
                    SingleExpr prev = leave_start_expr_false[leaves_false - 1];
                    repeat = (prev == e_false);
                }
                if (repeat) {
                    DEBUG_PRINT2 << "\t\tTotal: " << k << ", fails: " << fails << ", repeat at: " << e_false.get_expr() << "\n";
                    leaves_false++;
                    k = 0;
                    fails = 0;
                    DEBUG_PRINT2 << "\n\t\t******************************************************************\n";
                    DEBUG_PRINT2 << "\t\tLeaves: " << leaves_false << "\n";
                    std::cout.flush();
                    dec_false.val = k;
                    e_false = SingleExpr();
                    e_false.create(dec_false, leaves_false);
                    assert(leave_start_expr_false.size() < leaves_false);
                    leave_start_expr_false.push_back(e_false);
                }
                if (leaves_false > MAX_LEAVES) {
                    leaves_false = START_LEAVES;
                    break;
                }
                //std::cout << "\t\te_false: " << e_false.get_expr() << "\n";
                Halide::Expr expr_cond = e_cond.get_expr();
                Halide::Expr expr_true = e_true.get_expr();
                Halide::Expr expr_false = e_false.get_expr();

                bool uses_x = e_cond.uses_x[0] || e_true.uses_x[0] || e_false.uses_x[0];
                bool uses_y = e_cond.uses_y[0] || e_true.uses_y[0] || e_false.uses_y[0];

                Halide::Expr expr = Halide::select(expr_cond, expr_true, expr_false);

                if (!uses_x || !uses_y) {
                    DEBUG_PRINT2 << "...Skip " << i << ": " << expr << "\t; uses_x: "
                                 << uses_x << "; uses_y: " << uses_y << "\n";
                    fails++;
                    continue;
                }

                bool associative = true;
                uses_y = uses_vars(expr, kYNames);
                uses_x = uses_vars(expr, kXNames);

                Halide::Expr simplified;
                bool boring = is_expr_boring(expr, simplified, kXNames, kYNames, kConstantNames);
                if (boring || !uses_y || !uses_x) {
                    DEBUG_PRINT2 << "...Skip " << i << ": " << expr << " -> " << simplified << "\t; boring? "
                                 << boring << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
                    fails++;
                    continue;
                }

                //std::cout  << "Checking associativity of: " << expr << "\n";
                for (int trial = 0; trial < 250; trial++) {
                    Value x = random_value(), y = random_value(), z = random_value(), k = random_value();
                    // Check it depends on x and y in some meaningful way
                    Value v_xy = e_cond.evaluate(x, y, k) ? e_true.evaluate(x, y, k) : e_false.evaluate(x, y, k);
                    Value v_yz = e_cond.evaluate(y, z, k) ? e_true.evaluate(y, z, k) : e_false.evaluate(y, z, k);
                    Value v_xz = e_cond.evaluate(x, z, k) ? e_true.evaluate(x, z, k) : e_false.evaluate(x, z, k);
                    if (v_xy != v_xz) {
                        uses_y = true;
                    }
                    if (v_xz != v_yz) {
                        uses_x = true;
                    }

                    // Check it's associative
                    Value v_x_yz = e_cond.evaluate(x, v_yz, k) ? e_true.evaluate(x, v_yz, k) : e_false.evaluate(x, v_yz, k);
                    Value v_xy_z = e_cond.evaluate(v_xy, z, k) ? e_true.evaluate(v_xy, z, k) : e_false.evaluate(v_xy, z, k);
                    if (v_x_yz != v_xy_z) {
                        associative = false;
                        break;
                    }
                }

                if (associative && uses_x && uses_y) {
                    vector<Halide::Expr> halide_exprs = {expr};
                    if (z3_check_associativity(halide_exprs, kXVars, kYVars, kConstants, {leaves_cond}, {i})) {
                        valid++;
                    }
                } else {
                    fails++;
                    DEBUG_PRINT2 << "...Skip " << i << ": " << expr << "\t; uses_x: " << uses_x
                                 << "; uses_y: " << uses_y << "; associative: " << associative << "\n";
                }
            }
        }
    }
    return 0;
}