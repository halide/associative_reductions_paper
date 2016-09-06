
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
vector<string> kConstantNames;
vector<Halide::Expr> kXVars = {
    Variable::make(kType, "x0"),
    Variable::make(kType, "x1")
};
vector<Halide::Expr> kYVars = {
    Variable::make(kType, "y0"),
    Variable::make(kType, "y1")
};
vector<Halide::Expr> kConstants;

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
    X1,
    Y1,
    Add,
    Sub,
    Mul,
    //Min,
    //Max,
    LastNode
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

struct Expr {
    // The expression in prefix order
    Node nodes[64];
    int size;
    bool fail;
    bool uses_x;
    bool uses_y;

    Expr() : size(0), fail(false), uses_x(false), uses_y(false) {}

    Value evaluate_term(const vector<Value> &xvalues, const vector<Value> &yvalues, int &cursor) const {
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
        case Add:
            v1 = evaluate_term(xvalues, yvalues, cursor);
            v2 = evaluate_term(xvalues, yvalues, cursor);
            return v1 + v2;
        case Sub:
            v1 = evaluate_term(xvalues, yvalues, cursor);
            v2 = evaluate_term(xvalues, yvalues, cursor);
            return v1 - v2;
        case Mul:
            v1 = evaluate_term(xvalues, yvalues, cursor);
            v2 = evaluate_term(xvalues, yvalues, cursor);
            return v1 * v2;
        /*case Min:
            v1 = evaluate_term(xvalues, yvalues, cursor);
            v2 = evaluate_term(xvalues, yvalues, cursor);
            return std::min(v1, v2);
        case Max:
            v1 = evaluate_term(xvalues, yvalues, cursor);
            v2 = evaluate_term(xvalues, yvalues, cursor);
            return std::max(v1, v2);*/
        default:
            return 0;
        }
    }

    Value evaluate(const vector<Value> &xvalues, const vector<Value> &yvalues) const {
        int cursor = 0;
        return evaluate_term(xvalues, yvalues, cursor);
    }

    void create(DecisionSource &dec, int leaves) {
        assert(size < 64);
        assert(leaves > 0);
        if (leaves == 1) {
            /*if (size > 1 && nodes[size-1] == X0 &&
                (//nodes[size-2] == Min ||
                 //nodes[size-2] == Max ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                //uses_y = true;
                //nodes[size++] = Y0;

                int d = dec.get(3);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X1;
                } else if (d == 1) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y = true;
                    nodes[size++] = Y1;
                }

            } else if (size > 1 && nodes[size-1] == X1 &&
                (//nodes[size-2] == Min ||
                 //nodes[size-2] == Max ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)

                int d = dec.get(3);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_y = true;
                    nodes[size++] = Y0;
                } else {
                    uses_y = true;
                    nodes[size++] = Y1;
                }

            } else if (size > 1 && nodes[size-1] == Y0 &&
                       (//nodes[size-2] == Min ||
                        //nodes[size-2] == Max ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                //uses_x = true;
                //nodes[size++] = X0;

                int d = dec.get(3);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x = true;
                    nodes[size++] = X1;
                } else {
                    uses_y = true;
                    nodes[size++] = Y1;
                }
            } else if (size > 1 && nodes[size-1] == Y1 &&
                       (//nodes[size-2] == Min ||
                        //nodes[size-2] == Max ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                //uses_x = true;
                //nodes[size++] = X0;

                int d = dec.get(3);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else {
                    uses_y = true;
                    nodes[size++] = Y0;
                }
            } else {
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
            }*/

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
            // TODO make a list of reasonable options
            int d = dec.get(LastNode - Add) + Add;
            nodes[size++] = Node(d);
            switch(d) {
            case Add:
            case Mul:
            //case Min:
            //case Max:
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
        /*case Min:
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
            break;*/
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
        case X1:
            result = kXVars[1];
            break;
        case Y0:
            result = kYVars[0];
            break;
        case Y1:
            result = kYVars[1];
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
        /*case Min:
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
            break;*/
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

Value random_value() {
    return (((rand() << 16) ^ (rand() << 8) ^ rand()) & 0x0ffffff) - 0x07fffff;
}

Expr generate_expr(int index, uint64_t &i, uint64_t &leaves, uint64_t &fails) {
    string shift = "";
    for (int i = 0; i < index; ++i) {
        shift += "\t";
    }

    Expr e;
    DecisionSource dec;
    dec.val = i;
    e.create(dec, leaves);

    while (dec.val) {
        std::cout << shift << "Total (" << index << "): " << i << ", fails: " << fails << ", val: " << dec.val << "\n";
        leaves++;
        i = 0;
        fails = 0;
        if (index == 0) {
            std::cout << shift << "\n******************************************************************\n";
            std::cout << shift << "Leaves (" << index << "): " << leaves << "\n";
        }
        std::cout.flush();
        dec.val = i;
        e = Expr();
        e.create(dec, leaves);
    }
    i++;
    return e;
}

bool should_skip_expression(int index, Expr e, uint64_t &fails) {
    string shift = "";
    for (int i = 0; i < index; ++i) {
        shift += "\t";
    }

    Halide::Expr expr = e.get_expr();

    if (e.fail || !e.uses_x || !e.uses_y) {
        fails++;
        DEBUG_PRINT2 << shift << "...Skip (" << index << ") " << expr << "\t; fail? " << e.fail << "; uses_x: "
                     << e.uses_x << "; uses_y: " << e.uses_y << "\n";
        return true;
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

bool fast_check_associativity(const vector<Expr> &eqs) {
    size_t size = eqs.size();
    bool associative = true;
    bool uses_y = false, uses_x = false;
    for (int trial = 0; trial < 250; trial++) {
        vector<Value> xvalues(size), yvalues(size), zvalues(size);
        for (size_t i = 0; i < size; ++i) {
            xvalues[i] = random_value();
            yvalues[i] = random_value();
            zvalues[i] = random_value();
        }

        // Check it depends on x and y in some meaningful way
        vector<Value> v_xy(size), v_yz(size), v_xz(size);

        for (size_t i = 0; i < size; ++i) {
            v_xy[i] = eqs[i].evaluate(xvalues, yvalues);
            v_yz[i] = eqs[i].evaluate(yvalues, zvalues);
            v_xz[i] = eqs[i].evaluate(xvalues, zvalues);

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
            v_x_yz[i] = eqs[i].evaluate(xvalues, v_yz);
            v_xy_z[i] = eqs[i].evaluate(v_xy, zvalues);
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
        DEBUG_PRINT2 << "...Skip " << Halide::Tuple(temp) << "\t; associative? " << associative
                     << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
    }
    return skip;
}

bool z3_check_associativity(const vector<Expr> &eqs) {
    vector<Halide::Expr> temp(eqs.size());
    for (size_t i = 0; i < eqs.size(); ++i) {
        temp[i] = eqs[i].get_expr();
    }

    Halide::Tuple tuple_eqs(temp);
    pair<IsAssociative, AssociativeIds> result = prove_associativity(tuple_eqs, kXVars, kYVars, kConstants);
    if (result.first == IsAssociative::YES) {
        std::cout << tuple_eqs << " -> ";
        if (result.second.associativity == AssociativeIds::LEFT) {
            std::cout << "Left-associativity";
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            std::cout << "Right-associativity";
        } else {
            std::cout << "Unknown-associativity\n";
            return false;
        }
        std::cout << " with identity: " << Halide::Tuple(result.second.identities) << "\n";
    } else if (result.first == IsAssociative::UNKNOWN) {
        std::cout << tuple_eqs << " -> ";
        if (result.second.associativity == AssociativeIds::LEFT) {
            std::cout << "UNKNOWN associative with left-identity: ";
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            std::cout << "UNKNOWN associative with right-identity: ";
        } else {
            std::cout << "UNKNOWN associative\n";
            return false;
        }
        std::cout << Halide::Tuple(result.second.identities) << "\n";
    } else {
        std::cout << tuple_eqs << " -> " << "NOT associative\n";
        return false;
    }
    return true;
}

int main(int argc, char **argv) {
    const int MAX_LEVEL = 4;
    const int START_LEVEL = 4;
    uint64_t fails [TUPLE_SIZE];
    uint64_t indices[TUPLE_SIZE];
    uint64_t leaves[TUPLE_SIZE];
    for (size_t idx = 0; idx < TUPLE_SIZE; ++idx) {
        fails[idx] = 0;
        indices[idx] = 0;
        leaves[idx] = START_LEVEL;
    }

    while (true) {
        Expr e0 = generate_expr(0, indices[0], leaves[0], fails[0]);
        bool skip_e0 = should_skip_expression(0, e0, fails[0]);
        if (skip_e0) {
            continue;
        }

        std::cout << "****Element 0: " << e0.get_expr() << "\n";
        Halide::Expr expr = (kXVars[0] * kYVars[0]) - (kXVars[1] * kYVars[1]);
        if (equal(e0.get_expr(), expr)) {
            std::cout << "FOUND EXPR after " << indices[0] << "; failed: " << fails[0] << "\n";
            return 0;
        }
        /*fails[1] = 0;
        indices[1] = 0;
        leaves[1] = START_LEVEL;
        while (true) {
            Expr e1 = generate_expr(1, indices[1], leaves[1], fails[1]);
            if (Halide::Internal::equal(e0.get_expr(), e1.get_expr())) {
                fails[1] += 1;
                continue;
            }
            bool skip_e1 = should_skip_expression(1, e1, fails[1]);
            if (skip_e1) {
                continue;
            }
            vector<Expr> eqs = {e0, e1};
            if (!fast_check_associativity(eqs)) {
                z3_check_associativity(eqs);
            }

            if (leaves[1] > MAX_LEVEL) {
                break;
            }
        }*/
        if (leaves[0] > MAX_LEVEL) {
            break;
        }
    }
    //bitvector_associativity();
    //bitvector_identity();
    return 0;
}


