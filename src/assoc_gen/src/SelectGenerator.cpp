
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "z3++.h"
#include "Halide.h"
#include "Z3OpsHelper.h"
#include "HalideToZ3.h"
#include "AssociativityProver.h"
#include "Error.h"

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

Halide::Type kType = Halide::Int(32);
vector<string> kXNames = {"x0"};
vector<string> kYNames = {"y0"};
vector<string> kConstantNames = {"k0"};
vector<Halide::Expr> kXVars = {Variable::make(kType, "x0")};
vector<Halide::Expr> kYVars = {Variable::make(kType, "y0")};
vector<Halide::Expr> kConstants = {Variable::make(kType, "k0")};

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

bool is_boring(Halide::Expr e, Halide::Expr &simplified) {
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
        Halide::Expr temp = simplify(solve_expression(simplified, v).result);
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

void print_tuple(const Halide::Tuple &tuple) {
    std::cout << "{ ";
    for (size_t i = 0; i < tuple.size(); ++i) {
        std::cout << tuple[i];
        if (i != tuple.size() - 1) {
            std::cout << ", ";
        }
    }
    std::cout << " }";
}

// Replace all signed/unsigned integers with symbolic variables.
class ReplaceConstants : public Halide::Internal::IRMutator {
    // Count the number of integer constants we have replaced so far.
    unsigned count = 0;

    using Halide::Internal::IRMutator::visit;

    Halide::Expr get_expr(const Halide::Type &t) {
        string name = unique_name("k" + std::to_string(count));
        Halide::Expr var = Variable::make(t, name);
        if (kConstants.size() <= count) {
            kConstantNames.push_back(name);
            kConstants.push_back(var);
        }
        count++;
        return var;
    }

    void visit(const Halide::Internal::IntImm *op) {
        expr = get_expr(op->type);
    }

    void visit(const Halide::Internal::UIntImm *op) {
        expr = get_expr(op->type);
    }
};

} // anonymous namespace

typedef int Value;

typedef enum {
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
    //LastNode,
} Node;

typedef enum {
    Int = 0
} Type;

struct DecisionSource {
    uint64_t val;

    DecisionSource() : val(0){}

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
                 nodes[size-2] == LT ||
                 nodes[size-2] == GT ||
                 nodes[size-2] == EQ ||
                 nodes[size-2] == NE ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                if (dec.get(2)) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }

            } else if (size > 1 && nodes[size-1] == Y0 &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == LT ||
                        nodes[size-2] == GT ||
                        nodes[size-2] == EQ ||
                        nodes[size-2] == NE ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                if (dec.get(2)) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else {
                    nodes[size++] = K0;
                }
            } else if (size > 1 && nodes[size-1] == K0) {
                if (dec.get(2)) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else {
                    uses_y = true;
                    nodes[size++] = Y0;
                }
            } else {
                int code = dec.get(3);
                if (code == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (code == 1) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else {
                    nodes[size++] = K0;
                }
            }

            /*int code = dec.get(3);
            if (code == 0) {
                uses_x = true;
                nodes[size++] = X0;
            } else if (code == 1) {
                uses_y = true;
                nodes[size++] = Y0;
            } else {
                nodes[size++] = K0;
            }*/
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
                    //std::cout << leaves << " -> " << leaves_on_left << ", " << leaves_on_right << "\n";
                    create(dec, leaves_on_left);
                    create(dec, leaves_on_right);
                }
                break;
            case Sub:
                {
                    int leaves_on_right = dec.get(leaves - 1) + 1;
                    int leaves_on_left = leaves - leaves_on_right;
                    //std::cout << leaves << " -> " << leaves_on_left << ", " << leaves_on_right << "\n";
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

    pair<IsAssociative, AssociativeIds> is_associative() {
        Halide::Expr eq = get_expr();
        return prove_associativity(eq, kXVars, kYVars, kConstants);
    }
};

Value random_value() {
    return (((rand() << 16) ^ (rand() << 8) ^ rand()) & 0x0ffffff) - 0x07fffff;
}

int main(int argc, char **argv) {
    vector<Expr> leave_start_expr_cond;
    leave_start_expr_cond.reserve(32);

    const int MAX_LEAVES_COND = 4;
    const int MAX_LEAVES = 4;
    const int START_LEAVES_COND = 1;
    const int START_LEAVES = 1;

    uint64_t fails = 0, valid = 0;
    int leaves_cond = START_LEAVES_COND, leaves_true = START_LEAVES, leaves_false = START_LEAVES;
    std::cout << "\n******************************************************************\n";
    std::cout << "Leaves: " << leaves_cond << ", valid: " << valid << "\n";

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
            std::cout << "Total: " << i << ", fails: " << fails << ", repeat at: " << e_cond.get_expr() << "\n";
            leaves_cond++;
            i = 0;
            fails = 0;
            std::cout << "\n******************************************************************\n";
            std::cout << "Leaves: " << leaves_cond << ", valid: " << valid << "\n";
            dec_cond.val = i;
            e_cond = Expr(true);
            e_cond.create(dec_cond, leaves_cond);
            assert(leave_start_expr_cond.size() < leaves_cond);
            leave_start_expr_cond.push_back(e_cond);
        }
        if (leaves_cond > MAX_LEAVES_COND) {
            return 0;
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
                DEBUG_PRINT2 << "\tTotal: " << j << ", fails: " << fails << ", repeat at: " << e_true.get_expr() << "\n";
                leaves_true++;
                j = 0;
                fails = 0;
                DEBUG_PRINT2 << "\n\t******************************************************************\n";
                DEBUG_PRINT2 << "\tLeaves: " << leaves_true << "\n";
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
                    DEBUG_PRINT2 << "\t\tTotal: " << k << ", fails: " << fails << ", repeat at: " << e_false.get_expr() << "\n";
                    leaves_false++;
                    k = 0;
                    fails = 0;
                    DEBUG_PRINT2 << "\n\t\t******************************************************************\n";
                    DEBUG_PRINT2 << "\t\tLeaves: " << leaves_false << "\n";
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

                bool uses_x = e_cond.uses_x || e_true.uses_x || e_false.uses_x;
                bool uses_y = e_cond.uses_y || e_true.uses_y || e_false.uses_y;

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
                bool boring = is_boring(expr, simplified);
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

                if (associative && uses_x && uses_y && !boring) {
                    pair<IsAssociative, AssociativeIds> result = prove_associativity(expr, kXVars, kYVars, kConstants);
                    if (result.first == IsAssociative::YES) {
                        if (result.second.associativity == AssociativeIds::LEFT) {
                            std::cout << "i: " << i << ", j: " << j << ", k: " << k << ", " << expr << " -> ";
                            std::cout << "Left-associativity";
                            valid++;
                        } else if (result.second.associativity == AssociativeIds::RIGHT) {
                            std::cout << "i: " << i << ", j: " << j << ", k: " << k << ", " << expr << " -> ";
                            std::cout << "Right-associativity";
                            valid++;
                        } else {
                            fails++;
                            //std::cout << "Unknown-associativity\n";
                            continue;
                        }
                        std::cout << " with identity: ";
                        print_tuple(Halide::Tuple(result.second.identities));
                        std::cout << "\n";
                    } else if (result.first == IsAssociative::UNKNOWN) {
                        if (result.second.associativity == AssociativeIds::LEFT) {
                            std::cout << "i: " << i << ", j: " << j << ", k: " << k << ", " << expr << " -> ";
                            std::cout << "UNKNOWN associative with left-identity: ";
                            valid++;
                        } else if (result.second.associativity == AssociativeIds::RIGHT) {
                            std::cout << "i: " << i << ", j: " << j << ", k: " << k << ", " << expr << " -> ";
                            std::cout << "UNKNOWN associative with right-identity: ";
                            valid++;
                        } else {
                            fails++;
                            //std::cout << "UNKNOWN associative\n";
                            continue;
                        }
                        print_tuple(Halide::Tuple(result.second.identities));
                        std::cout << "\n";
                    } else {
                        fails++;
                        //std::cout << "NOT associative\n";
                    }
                } else {
                    fails++;
                    DEBUG_PRINT2 << "...Skip " << i << ": " << expr << "\t; boring? " << boring << "; uses_x: "
                                 << uses_x << "; uses_y: " << uses_y << "; associative: " << associative << "\n";
                }
            }
        }
    }
    return 0;
}