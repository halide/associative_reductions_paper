
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "z3++.h"
#include "Halide.h"
#include "Z3OpsHelper.h"
#include "HalideToZ3.h"
#include "AssociativityProver.h"
#include "Error.h"

#include <algorithm>
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

const size_t TUPLE_SIZE = 2;

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

namespace {

// Return true if the Expr uses any of the Variables in 'vars'
class UseVars : public Halide::Internal::IRVisitor {
    using Halide::Internal::IRVisitor::visit;

    vector<string> vars;

    void visit(const Variable *op) {
        if (std::find(vars.begin(), vars.end(), op->name) != vars.end()) {
            result = true;
        }
    }

public:
    bool result;
    UseVars(const vector<string> &v) : vars(v), result(false) {}
};

bool uses_vars(Halide::Expr e, const vector<string> &vars) {
    e = simplify(e);
    UseVars uv(vars);
    e.accept(&uv);
    return uv.result;
}

bool is_expr_boring(Halide::Expr e, Halide::Expr &simplified) {
    Halide::Expr before = e;
    simplified = e;
    simplified = simplify(simplified);
    if (!Halide::Internal::equal(before, simplified)) {
        return true;
    }

    vector<string> vars(kXNames);
    vars.insert(vars.end(), kYNames.begin(), kYNames.end());
    vars.insert(vars.end(), kConstantNames.begin(), kConstantNames.end());
    for (int i = vars.size() - 1; i >= 0; --i) {
        const string &v = vars[i];
        // Call simplify after solve_expression since sometimes it will reorder
        // the variables which allows cancellation by the simplifier.
        Halide::Expr temp = solve_expression(simplified, v).result;
        // Call solve_expression again to canonicalize the expr
        temp = solve_expression(temp, v).result;
        if (temp.defined()) {
            simplified = temp;

        }
    }
    simplified = simplify(simplified);
    if (!Halide::Internal::equal(before, simplified)) {
        return true;
    }
    return false;
}

std::ostream &operator<<(std::ostream &stream, const Halide::Tuple &tuple) {
    stream << "{ ";
    for (size_t i = 0; i < tuple.size(); ++i) {
        stream << tuple[i];
        if (i != tuple.size() - 1) {
            stream << ", ";
        }
    }
    stream << " }";
    return stream;
}

};

} // anonymous namespace

typedef int Value;

typedef enum {
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
    LastNode,
} Node;

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
};

struct Expr {
    // The expression in prefix order
    bool is_cond;
    vector<Node> nodes;
    int size;
    bool fail;
    bool uses_x;
    bool uses_y;

    Expr(bool is_cond) : is_cond(is_cond), nodes(64), size(0), fail(false), uses_x(false), uses_y(false) {}
    Expr() : is_cond(false), nodes(64), size(0), fail(false), uses_x(false), uses_y(false) {}

    bool operator==(const Expr& rhs) const {
        return rhs.nodes == nodes;
    }

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
                 nodes[size-2] == LT ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                int d = dec.get(4);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X1;
                } else if (d == 1) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else if (d == 2) {
                    uses_y = true;
                    nodes[size++] = Y1;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == X1 &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == LT ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                int d = dec.get(4);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else if (d == 2) {
                    uses_y = true;
                    nodes[size++] = Y1;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == Y0 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == LT ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                int d = dec.get(4);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y = true;
                    nodes[size++] = Y1;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == Y1 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == LT ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                int d = dec.get(4);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == K0) {
                // avoid min(k0, k0)
                int d = dec.get(4);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y = true;
                    nodes[size++] = Y1;
                }
            } else {
                int d = dec.get(5);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x = true;
                    nodes[size++] = X1;
                } else if (d == 2) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else if (d == 3) {
                    uses_y = true;
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

Value random_value() {
    return (((rand() << 16) ^ (rand() << 8) ^ rand()) & 0x0ffffff) - 0x07fffff;
}

bool should_skip_expression(int index, Halide::Expr expr, uint64_t &fails) {
    string shift = "";
    for (int i = 0; i < index; ++i) {
        shift += "\t";
    }

    bool uses_y = uses_vars(expr, kYNames);
    bool uses_x = uses_vars(expr, kXNames);

    Halide::Expr simplified;
    bool boring = is_expr_boring(expr, simplified);
    if (boring || !uses_y || !uses_x) {
        fails++;
        DEBUG_PRINT2 << shift << "...Skip (" << index << ") " << expr << " -> " << simplified << "\t; boring? "
                     << boring << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
        return true;
    }
    return false;
}

bool fast_check_associativity(Expr &e0, Expr &e_cond, Expr &e_true, Expr &e_false, int select_idx) {
    size_t size = 2;
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

        {
            v_xy[1 - select_idx] = e0.evaluate(xvalues, yvalues, k);
            v_yz[1 - select_idx] = e0.evaluate(yvalues, zvalues, k);
            v_xz[1 - select_idx] = e0.evaluate(xvalues, zvalues, k);

            if (v_xy[1 - select_idx] != v_xz[1 - select_idx]) {
                uses_y = true;
            }
            if (v_xz[1 - select_idx] != v_yz[1 - select_idx]) {
                uses_x = true;
            }
        }
        {
            v_xy[select_idx] = e_cond.evaluate(xvalues, yvalues, k) ? e_true.evaluate(xvalues, yvalues, k) : e_false.evaluate(xvalues, yvalues, k);
            v_yz[select_idx] = e_cond.evaluate(yvalues, zvalues, k) ? e_true.evaluate(yvalues, zvalues, k) : e_false.evaluate(yvalues, zvalues, k);
            v_xz[select_idx] = e_cond.evaluate(xvalues, zvalues, k) ? e_true.evaluate(xvalues, zvalues, k) : e_false.evaluate(xvalues, zvalues, k);

            if (v_xy[select_idx] != v_xz[select_idx]) {
                uses_y = true;
            }
            if (v_xz[select_idx] != v_yz[select_idx]) {
                uses_x = true;
            }
        }

        // Check if it's associative
        vector<Value> v_x_yz(size), v_xy_z(size);
        {
            v_x_yz[1 - select_idx] = e0.evaluate(xvalues, v_yz, k);
            v_xy_z[1 - select_idx] = e0.evaluate(v_xy, zvalues, k);
            if (v_x_yz[1 - select_idx] != v_xy_z[1 - select_idx]) {
                associative = false;
                break;
            }
        }
        {
            v_x_yz[select_idx] = e_cond.evaluate(xvalues, v_yz, k) ? e_true.evaluate(xvalues, v_yz, k) : e_false.evaluate(xvalues, v_yz, k);
            v_xy_z[select_idx] = e_cond.evaluate(v_xy, zvalues, k) ? e_true.evaluate(v_xy, zvalues, k) : e_false.evaluate(v_xy, zvalues, k);
            if (v_x_yz[select_idx] != v_xy_z[select_idx]) {
                associative = false;
                break;
            }
        }
    }

    bool skip = !(associative && uses_x && uses_y);
    if (skip) {
        vector<Halide::Expr> temp = {e0.get_expr(), select(e_cond.get_expr(), e_true.get_expr(), e_false.get_expr())};
        DEBUG_PRINT2 << "...Skip " << Halide::Tuple(temp) << "\t; associative? " << associative
                     << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
    }
    return skip;
}

bool z3_check_associativity(vector<Halide::Expr> &temp, uint64_t &valid) {
    Halide::Tuple tuple_eqs(temp);
    pair<IsAssociative, AssociativeIds> result = prove_associativity(tuple_eqs, kXVars, kYVars, kConstants);
    if (result.first == IsAssociative::YES) {
        if (result.second.associativity == AssociativeIds::LEFT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "Left-associativity";
            valid++;
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "Right-associativity";
            valid++;
        } else {
            //std::cout << tuple_eqs << " -> ";
            //std::cout << "Unknown-associativity\n";
            return false;
        }
        std::cout << " with identity: " << Halide::Tuple(result.second.identities) << "\n";
    } else if (result.first == IsAssociative::UNKNOWN) {
        if (result.second.associativity == AssociativeIds::LEFT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "UNKNOWN associative with left-identity: ";
            valid++;
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "UNKNOWN associative with right-identity: ";
            valid++;
        } else {
            //std::cout << tuple_eqs << " -> ";
            //std::cout << "UNKNOWN associative\n";
            return false;
        }
        std::cout << Halide::Tuple(result.second.identities) << "\n";
    } else {
        //std::cout << tuple_eqs << " -> " << "NOT associative\n";
        return false;
    }
    return true;
}

int main(int argc, char **argv) {
    const uint64_t MAX_LEAVES_COND = 4;
    const uint64_t MAX_LEAVES = 3;
    const uint64_t MAX_LEAVES_0 = 4;
    const uint64_t START_LEAVES_COND = 1;
    const uint64_t START_LEAVES = 1;
    const uint64_t START_LEAVES_0 = 1;

    uint64_t fails = 0, valid = 0;
    uint64_t leaves = START_LEAVES_0, leaves_cond = START_LEAVES_COND, leaves_true = START_LEAVES, leaves_false = START_LEAVES;
    std::cout << "\n******************************************************************\n";
    std::cout << "Leaves: " << leaves_cond << ", valid: " << valid << "\n";

    vector<Expr> leave_start_expr;
    leave_start_expr.reserve(32);
    for (uint64_t t = 0;; t++) {
        Expr e0;
        DecisionSource dec;
        dec.val = t;
        e0.create(dec, leaves);

        bool repeat = false;
        if (leave_start_expr.size() < leaves) {
            leave_start_expr.push_back(e0);
        } else {
            Expr prev = leave_start_expr[leaves - 1];
            repeat = (prev == e0);
        }
        if (repeat) {
            std::cout << "Total: " << t << ", fails: " << fails << ", repeat at: " << e0.get_expr() << "\n";
            leaves++;
            t = 0;
            fails = 0;
            std::cout << "\n******************************************************************\n";
            std::cout << "Leaves: " << leaves << ", valid: " << valid << "\n";
            std::cout.flush();
            dec.val = t;
            e0 = Expr();
            e0.create(dec, leaves);
            assert(leave_start_expr.size() < leaves);
            leave_start_expr.push_back(e0);
        }
        if (leaves > MAX_LEAVES_0) {
            return 0;
        }

        //e0.print();

        Halide::Expr e0_expr = e0.get_expr();
        bool skip_e0 = should_skip_expression(0, e0_expr, fails);
        if (skip_e0) {
            continue;
        }
        //std::cout << "Element 0: " << e0_expr << "\n";

        // GENERATE SELECT
        vector<Expr> leave_start_expr_cond;
        leave_start_expr_cond.reserve(32);
        Expr e_cond(true), e_true, e_false;
        for (uint64_t i = 0;; i++) {
            e_cond = Expr(true);
            DecisionSource dec_cond;
            dec_cond.val = i;
            e_cond.create(dec_cond, leaves_cond);

            bool repeat = false;
            if (leave_start_expr_cond.size() < leaves_cond) {
                leave_start_expr_cond.push_back(e_cond);
            } else {
                Expr prev = leave_start_expr_cond[leaves_cond - 1];
                repeat = (prev == e_cond);
            }
            if (repeat) {
                //std::cout << "\tTotal: " << i << ", fails: " << fails << ", repeat at: " << e_cond.get_expr() << "\n";
                leaves_cond++;
                i = 0;
                fails = 0;
                //std::cout << "\n\t******************************************************************\n";
                //std::cout << "\tLeaves: " << leaves_cond << "\n";
                dec_cond.val = i;
                e_cond = Expr(true);
                e_cond.create(dec_cond, leaves_cond);
                assert(leave_start_expr_cond.size() < leaves_cond);
                leave_start_expr_cond.push_back(e_cond);
            }
            if (leaves_cond > MAX_LEAVES_COND) {
                leaves_cond = START_LEAVES_COND;
                break;
            }

            //e_cond.print();
            //std::cout << "e_cond: " << e_cond.get_expr() << "\n";
            if (!e_cond.get_expr().defined() || !e_cond.get_expr().type().is_bool()) {
                continue;
            }

            //std::cout << "e_cond: " << e_cond.get_expr() << "\n";
            vector<Expr> leave_start_expr_true;
            leave_start_expr_true.reserve(32);
            for (uint64_t j = 0;; j++) {
                e_true = Expr();
                DecisionSource dec_true;
                dec_true.val = j;
                e_true.create(dec_true, leaves_true);

                bool repeat = false;
                if (leave_start_expr_true.size() < leaves_true) {
                    leave_start_expr_true.push_back(e_true);
                } else {
                    Expr prev = leave_start_expr_true[leaves_true - 1];
                    repeat = (prev == e_true);
                }
                if (repeat) {
                    DEBUG_PRINT2 << "\t\tTotal: " << j << ", fails: " << fails << ", repeat at: " << e_true.get_expr() << "\n";
                    leaves_true++;
                    j = 0;
                    fails = 0;
                    DEBUG_PRINT2 << "\n\t\t******************************************************************\n";
                    DEBUG_PRINT2 << "\t\tLeaves: " << leaves_true << "\n";
                    dec_true.val = j;
                    e_true = Expr();
                    e_true.create(dec_true, leaves_true);
                    assert(leave_start_expr_true.size() < leaves_true);
                    leave_start_expr_true.push_back(e_true);
                }
                if (leaves_true > MAX_LEAVES) {
                    leaves_true = START_LEAVES;
                    break;
                }

                //std::cout << "\te_true: " << e_true.get_expr() << "\n";
                vector<Expr> leave_start_expr_false;
                leave_start_expr_false.reserve(32);
                for (uint64_t k = 0;; k++) {
                    e_false = Expr();
                    DecisionSource dec_false;
                    dec_false.val = k;
                    e_false.create(dec_false, leaves_false);

                    bool repeat = false;
                    if (leave_start_expr_false.size() < leaves_false) {
                        leave_start_expr_false.push_back(e_false);
                    } else {
                        Expr prev = leave_start_expr_false[leaves_false - 1];
                        repeat = (prev == e_false);
                    }
                    if (repeat) {
                        DEBUG_PRINT2 << "\t\t\tTotal: " << k << ", fails: " << fails << ", repeat at: " << e_false.get_expr() << "\n";
                        leaves_false++;
                        k = 0;
                        fails = 0;
                        DEBUG_PRINT2 << "\n\t\t\t******************************************************************\n";
                        DEBUG_PRINT2 << "\t\t\tLeaves: " << leaves_false << "\n";
                        std::cout.flush();
                        dec_false.val = k;
                        e_false = Expr();
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
                    Halide::Expr expr = Halide::select(expr_cond, expr_true, expr_false);

                    bool skip_e1 = should_skip_expression(1, expr, fails);
                    if (skip_e1) {
                        continue;
                    }

                    //std::cout << "\tElement 1: " << expr << "\n";
                    vector<Halide::Expr> eqs = {expr, e0_expr}; // Flip
                    //std::cout << "Expression: " << Halide::Tuple(eqs) << "\n";
                    if (!fast_check_associativity(e0, e_cond, e_true, e_false, 0)) {
                        z3_check_associativity(eqs, valid);
                    }
                }
            }
        }
    }
    return 0;
}