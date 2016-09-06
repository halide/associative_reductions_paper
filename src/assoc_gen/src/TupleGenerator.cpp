
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
#include <set>
#include <stdint.h>

#include <boost/icl/interval_set.hpp>

using std::pair;
using std::set;
using std::string;
using std::vector;
using Halide::Internal::Variable;
using Halide::Internal::unique_name;

const size_t TUPLE_SIZE = 2;
const uint64_t START_LEAVES = 2;
const uint64_t MAX_LEAVES = 7;
const uint64_t LEAVES_TILE = 3;
const uint64_t ITER_TILE = 160000;

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

typedef boost::icl::interval_set<unsigned int> IntervalSet;
typedef IntervalSet::interval_type IntervalVal;

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
    K0,
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

    bool operator==(const Expr &rhs) const {
        return rhs.nodes == nodes;
    }

    bool operator<(const Expr &rhs) const {
        return rhs.nodes < nodes;
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
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid min(x, x)
                //uses_y = true;
                //nodes[size++] = Y0;

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
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                //uses_x = true;
                //nodes[size++] = X0;

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
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid min(y, y)
                //uses_x = true;
                //nodes[size++] = X0;

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
                int d = dec.get(4);
                if (d == 0) {
                    uses_x = true;
                    nodes[size++] = X0;
                } else if (d == 1) {
                    uses_x = true;
                    nodes[size++] = X0;
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

            /*int d = dec.get(4);
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

struct AssociativeTuple {
    vector<Expr> exprs;

    AssociativeTuple(const Expr &e0, const Expr &e1) : exprs(2) {
        exprs[0] = e0;
        exprs[1] = e1;
    }

    AssociativeTuple(const vector<Expr> &eqs) : exprs(eqs) {}

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

Value random_value() {
    return (((rand() << 16) ^ (rand() << 8) ^ rand()) & 0x0ffffff) - 0x07fffff;
}

bool generate_expr(int index, uint64_t leaves, uint64_t i, set<Expr> &seen, Expr &e) {
    string shift = "";
    for (int a = 0; a < index; ++a) {
        shift += "\t";
    }

    e = Expr();
    DecisionSource dec;
    dec.val = i;
    e.create(dec, leaves);

    //std::cout << shift << "Leaves: " << leaves << ", i: " << i << ", expr: " << e.get_expr() << ", dec.val: " << dec.val << "\n";

    if (dec.val == 0) {
        if (seen.find(e) != seen.end()) {
            //std::cout << shift << "***Double: " << e.get_expr() << ", leaves: " << leaves << ", i: " << i << "\n";
            return true;
        }
        //std::cout << shift << "Index: " << index << ", UNIQUE Leaves: " << leaves << ", i: " << i << ", expr: " << e.get_expr() << ", dec.val: " << dec.val << "\n";
        seen.insert(e);
        return false;
    } else {
        //std::cout << shift << "***SEEN EXPR: " << e.get_expr() << "\n";
        //assert(seen.find(e) != seen.end());
        return true;
    }
}

bool should_skip_expression(int index, const Expr &e) {
    string shift = "";
    for (int i = 0; i < index; ++i) {
        shift += "\t";
    }

    Halide::Expr expr = e.get_expr();

    if (e.fail || !e.uses_x || !e.uses_y) {
        DEBUG_PRINT2 << shift << "...Skip (" << index << ") " << expr << "\t; fail? " << e.fail << "; uses_x: "
                     << e.uses_x << "; uses_y: " << e.uses_y << "\n";
        return true;
    }

    bool uses_y = uses_vars(expr, kYNames);
    bool uses_x = uses_vars(expr, kXNames);

    Halide::Expr simplified;
    bool boring = is_expr_boring(expr, simplified);
    if (boring || !uses_y || !uses_x) {
        DEBUG_PRINT2 << shift << "...Skip (" << index << ") " << expr << " -> " << simplified << "\t; boring? "
                     << boring << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
        return true;
    }
    return false;
}

bool fast_check_associativity(const vector<Expr> &eqs, const set<AssociativeTuple> &associative_sets) {
    if (associative_sets.find(AssociativeTuple(eqs)) != associative_sets.end()) {
        return false;
    }
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

bool z3_check_associativity(const vector<Expr> &eqs) {
    vector<Halide::Expr> temp(eqs.size());
    for (size_t i = 0; i < eqs.size(); ++i) {
        temp[i] = eqs[i].get_expr();
    }

    Halide::Tuple tuple_eqs(temp);
    pair<IsAssociative, AssociativeIds> result = prove_associativity(tuple_eqs, kXVars, kYVars, kConstants);
    if (result.first == IsAssociative::YES) {
        if (result.second.associativity == AssociativeIds::LEFT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "Left-associativity";
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "Right-associativity";
        } else {
            /*std::cout << tuple_eqs << " -> ";
            std::cout << "Unknown-associativity\n";*/
            return false;
        }
        std::cout << " with identity: " << Halide::Tuple(result.second.identities) << "\n";
    } else if (result.first == IsAssociative::UNKNOWN) {
        if (result.second.associativity == AssociativeIds::LEFT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "UNKNOWN associative with left-identity: ";
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            std::cout << tuple_eqs << " -> ";
            std::cout << "UNKNOWN associative with right-identity: ";
        } else {
            /*std::cout << tuple_eqs << " -> ";
            std::cout << "UNKNOWN associative\n";*/
            return false;
        }
        std::cout << Halide::Tuple(result.second.identities) << "\n";
    } else {
        //std::cout << tuple_eqs << " -> " << "NOT associative\n";
        return false;
    }
    return true;
}

struct Point {
    uint64_t leaves;
    uint64_t i;
};

// morton1 - extract even bits
uint32_t morton1(uint32_t x) {
    x = x & 0x55555555;
    x = (x | (x >> 1)) & 0x33333333;
    x = (x | (x >> 2)) & 0x0F0F0F0F;
    x = (x | (x >> 4)) & 0x00FF00FF;
    x = (x | (x >> 8)) & 0x0000FFFF;
    return x;
}

// morton2 - extract odd and even bits
void morton2(uint32_t z, uint32_t &x, uint32_t &y) {
    x = morton1(z >> 1);
    y = morton1(z);
}

Point morton_to_coordinate(uint32_t morton) {
    int multiplier = morton/8;
    morton = morton % 8;

    uint32_t leaves_tile, i_tile;
    morton2(morton, leaves_tile, i_tile);

    i_tile += multiplier*4;
    uint64_t leaves = leaves_tile * LEAVES_TILE + START_LEAVES;
    uint64_t i = i_tile * ITER_TILE;

    //std::cout << "Morton: " << morton << " -> " << "leaves tile: " << leaves_tile << ", i tile: " << i_tile << ", leaves: " << leaves << ", i: " << i << "\n";
    return {leaves, i};
}

int main(int argc, char **argv) {
    vector<set<Expr>> seen(2);
    uint32_t MORTON_START = 33;
    uint32_t MORTON_MAX = 48;

    vector<IntervalSet> invalid(9);
    vector<set<Expr>> seen0(9);

    vector<set<AssociativeTuple>> associative_sets(9);

    uint64_t valid = 0;
    for (uint32_t morton = MORTON_START; morton <= MORTON_MAX; ++morton) {
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

                    Expr e0;
                    bool skip_e0 = generate_expr(0, leaves0, i0, seen0[leaves0], e0);
                    skip_e0 = skip_e0 || should_skip_expression(0, e0);
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

                                Expr e1;
                                bool skip_e1 = generate_expr(1, leaves1, i1, seen[1], e1);
                                // if (Halide::Internal::equal(e0.get_expr(), e1.get_expr())) {
                                //     continue;
                                // }
                                skip_e1 = skip_e1 || should_skip_expression(1, e1);
                                if (skip_e1) {
                                    invalid[leaves1].insert(i1);
                                    continue;
                                }
                                //std::cout << "Leaves1: " << leaves1 << ", i1: " << i1 << ", expr: " << e1.get_expr() << "\n";

                                // Check asssociativity
                                vector<Expr> eqs = {e0, e1};
                                if (!fast_check_associativity(eqs, associative_sets[leaves0])) {
                                    if (z3_check_associativity(eqs)) {
                                        associative_sets[leaves0].insert(AssociativeTuple(e0, e1));
                                        valid++;
                                    }
                                }
                            }
                        }
                    }
                    seen[1] = set<Expr>();
                }
            }
        }
        std::cout << "Valid: " << valid << "\n";
        std::cout << "**************************************************************************\n\n";
    }
    return 0;
}

int main2() {
    IntervalSet outages;

    outages.insert(IntervalVal::closed(1,1));
    outages.insert(IntervalVal::closed(7,10));
    outages.insert(IntervalVal::closed(8,11));
    outages.insert(IntervalVal::closed(90,120));
    outages.insert(2);

    for (auto it = outages.begin(); it != outages.end(); it++){
        std::cout << it->lower() << ", " << it->upper() << "\n";
    }
    std::cout << "Contains 11? " << boost::icl::contains(outages, 11) << "\n";
    std::cout << "Contains 20? " << boost::icl::contains(outages, 20) << "\n";
    std::cout << "First: " << outages.begin()->lower() << " -> " << outages.begin()->upper() << "\n";

    IntervalSet result = outages - IntervalVal::closed(1,1);
    for (auto it = result.begin(); it != result.end(); it++){
        std::cout << it->lower() << ", " << it->upper() << "\n";
    }
    std::cout << "Contains 1? " << boost::icl::contains(result, 1) << "\n";
    std::cout << "Contains 2? " << boost::icl::contains(result, 2) << "\n";

    for (uint32_t morton = 0; morton <= 64; ++morton) {
        Point point = morton_to_coordinate(morton);
        uint64_t leaves_start = std::min(std::max(point.leaves, START_LEAVES), MAX_LEAVES);
        uint64_t leaves_end =  std::max(std::min(point.leaves + LEAVES_TILE - 1, MAX_LEAVES), START_LEAVES);
        //uint64_t leaves_start = 2, leaves_end = 2;
        uint64_t i_start = point.i;
        uint64_t i_end = point.i + ITER_TILE - 1;

        std::cout << "Morton: " << morton << ", leaves: [" << leaves_start
                  << ", " << leaves_end << "], i: [" << i_start << ", "
                  << i_end << "]" << "\n";
    }

    return 0;
}

