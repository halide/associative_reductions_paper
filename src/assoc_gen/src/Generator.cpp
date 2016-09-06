
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
    K0, // constant
    Add,
    Sub,
    Mul,
    Min,
    Max,
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
    vector<Node> nodes;
    int size;
    bool fail;
    bool uses_x;
    bool uses_y;

    Expr() : nodes(64), size(0), fail(false), uses_x(false), uses_y(false) {}

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
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                if (dec.get(2)) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else {
                    nodes[size++] = K0;
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

    pair<IsAssociative, AssociativeIds> is_associative() const {
        Halide::Expr eq = get_expr();
        return prove_associativity(eq, kXVars, kYVars, kConstants);
    }
};

Value random_value() {
    return (((rand() << 16) ^ (rand() << 8) ^ rand()) & 0x0ffffff) - 0x07fffff;
}

int main(int argc, char **argv) {
    int min_leaves = 2;
    uint64_t fails = 0;
    const int MAX_LEAVES = 7;
    vector<set<Expr>> seen(9);

    for (uint64_t sum = 0; ; sum++) {
        for (int leaves = min_leaves; (leaves <= MAX_LEAVES) && (leaves <= (int)sum); leaves++) {
            int i = sum - leaves;
            assert(i >= 0);

            Expr e;
            DecisionSource dec;
            dec.val = i;
            e.create(dec, leaves);

            Halide::Expr expr = e.get_expr();
            //std::cout << "Generating sum: " << sum << "; i: " << i << "; leaves: " << leaves << "; expr: " << expr << "; val: " << dec.val << "\n";

            if (dec.val != 0) {
                //std::cout << "***Skipping duplicate " << "; i: " << i << "; leaves: " << leaves << "; expr: " << e.get_expr() << "\n";
                continue;
            } else {
                if (seen[leaves].find(e) != seen[leaves].end()) {
                    std::cout << "***Skipping duplicate " << "; i: " << i << "; leaves: " << leaves << "; expr: " << e.get_expr() << "\n";
                    continue;
                }
                seen[leaves].insert(e);
            }

            bool skip_e0 = generate_expr(0, leaves0, i0, seen0[leaves0], e0);

            if (e.fail || !e.uses_x || !e.uses_y) {
                DEBUG_PRINT2 << "...Skip " << i << ": " << expr << "\t; fail? " << e.fail << "; uses_x: "
                             << e.uses_x << "; uses_y: " << e.uses_y << "\n";
                fails++;
                continue;
            }
            bool associative = true;
            bool uses_y = uses_vars(expr, kYNames);
            bool uses_x = uses_vars(expr, kXNames);
            Halide::Expr simplified;
            bool boring = is_boring(expr, simplified);
            if (boring || !uses_y || !uses_x) {
                DEBUG_PRINT2 << "...Skip " << i << ": " << expr << " -> " << simplified << "\t; boring? "
                             << boring << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
                fails++;
                continue;
            }
            for (int trial = 0; trial < 250; trial++) {
                Value x = random_value(), y = random_value(), z = random_value(), k = random_value();
                // Check it depends on x and y in some meaningful way
                Value v_xy = e.evaluate(x, y, k);
                Value v_yz = e.evaluate(y, z, k);
                Value v_xz = e.evaluate(x, z, k);
                if (v_xy != v_xz) {
                    uses_y = true;
                }
                if (v_xz != v_yz) {
                    uses_x = true;
                }

                // Check it's associative
                Value v_x_yz = e.evaluate(x, v_yz, k);
                Value v_xy_z = e.evaluate(v_xy, z, k);
                if (v_x_yz != v_xy_z) {
                    associative = false;
                    break;
                }
            }

            if (associative && uses_x && uses_y && !boring) {
                pair<IsAssociative, AssociativeIds> result = e.is_associative();
                if (result.first == IsAssociative::YES) {
                    if (result.second.associativity == AssociativeIds::LEFT) {
                        std::cout << "Leaves: " << leaves << ", i: " << i << ", " << expr << " -> ";
                        std::cout << "Left-associativity";
                    } else if (result.second.associativity == AssociativeIds::RIGHT) {
                        std::cout << "Leaves: " << leaves << ", i: " << i << ", " << expr << " -> ";
                        std::cout << "Right-associativity";
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
                        std::cout << "Leaves: " << leaves << ", i: " << i << ", " << expr << " -> ";
                        std::cout << "UNKNOWN associative with left-identity: ";
                    } else if (result.second.associativity == AssociativeIds::RIGHT) {
                        std::cout << "Leaves: " << leaves << ", i: " << i << ", " << expr << " -> ";
                        std::cout << "UNKNOWN associative with right-identity: ";
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
    //bitvector_associativity();
    //bitvector_identity();
    return 0;
}