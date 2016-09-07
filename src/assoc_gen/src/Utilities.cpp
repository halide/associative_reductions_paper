#include "z3++.h"
#include "Halide.h"
#include "Z3OpsHelper.h"
#include "HalideToZ3.h"
#include "AssociativityProver.h"
#include "Utilities.h"

#include <cstdlib>
#include <cassert>
#include <cmath>
#include <set>
#include <stdint.h>

using std::pair;
using std::set;
using std::string;
using std::vector;
using Halide::Internal::Variable;
using Halide::Internal::unique_name;

namespace {

template <typename T>
std::ostream &operator<<(std::ostream &out, const set<T> &v) {
    out << '[';
    for (auto iter = v.begin(); iter != v.end(); ++iter) {
        out << (*iter);
        if (iter != (--v.end())) {
            out << ", ";
        }
    }
    out << "]";
    return out;
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

// morton1 - extract even bits
uint32_t morton1(uint32_t x) {
    x = x & 0x55555555;
    x = (x | (x >> 1)) & 0x33333333;
    x = (x | (x >> 2)) & 0x0F0F0F0F;
    x = (x | (x >> 4)) & 0x00FF00FF;
    x = (x | (x >> 8)) & 0x0000FFFF;
    return x;
}

void print_coordinate(const vector<uint64_t> &leaves, const vector<uint64_t> &is) {
    for (size_t i = 0; i < leaves.size(); ++i) {
        if (leaves.size() == 1) {
            std::cout << "Leaves" << ": " << leaves[i] << ", i" << ": " << is[i];
        } else {
            std::cout << "Leaves" << i << ": " << leaves[i] << ", i" << i << ": " << is[i];
        }
        if (i != leaves.size() - 1) {
            std::cout << ", ";
        }
    }
}

vector<set<int>> compute_subgraphs(vector<set<int>> dependencies) {
    vector<set<int>> subgraphs(dependencies.size());
    for (size_t i = 0; i < dependencies.size(); ++i) {
        // Check if the current subgraph is a subset of another
        const auto &current = dependencies[i];
        if (current.empty()) {
            continue;
        }
        bool should_remove = false;
        for (size_t j = 0; j < dependencies.size(); ++j) {
            const auto &other = dependencies[j];
            if ((i == j) || (current.size() > other.size()) || (j < i && subgraphs[i].empty())) {
                continue;
            }
            vector<int> diff;
            // Compute the vertices in the current set that are not contained in the other
            std::set_difference(current.begin(), current.end(), other.begin(), other.end(),
                                std::inserter(diff, diff.begin()));
            if (diff.empty()) {
                // 'current' is fully contained in 'other'
                should_remove = true;
                break;
            }
        }
        if (!should_remove) {
            subgraphs[i] = current;
        }
    }
    return subgraphs;
}

} // anonymous namespace

// morton2 - extract odd and even bits
void morton2(uint32_t z, uint32_t &x, uint32_t &y) {
    x = morton1(z >> 1);
    y = morton1(z);
}

bool uses_vars(Halide::Expr e, const vector<string> &vars) {
    e = simplify(e);
    UseVars uv(vars);
    e.accept(&uv);
    return uv.result;
}

bool is_expr_boring(Halide::Expr e, Halide::Expr &simplified,
                    const vector<string> &kXNames, const vector<string> &kYNames,
                    const vector<string> &kConstantNames) {
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

bool should_skip_expression(int index,
                            Halide::Expr expr,
                            bool e_fail,
                            const vector<bool> e_uses_x,
                            const vector<bool> e_uses_y,
                            const vector<string> &kXNames,
                            const vector<string> &kYNames,
                            const vector<string> &kConstantNames) {
    string shift = "";
    for (int i = 0; i < index; ++i) {
        shift += "\t";
    }

    if (e_fail) {
        DEBUG_PRINT2 << shift << "...Skip (" << index << ") " << expr << "; fail?  " << e_fail << "\n";
        return true;
    }

    bool uses_x = false, uses_y = false;
    for (size_t i = 0; i < e_uses_x.size(); ++i) {
        uses_x = uses_x || e_uses_x[i];
    }
    for (size_t i = 0; i < e_uses_y.size(); ++i) {
        uses_y = uses_y || e_uses_y[i];
    }

    if (!uses_x || !uses_y) {
        DEBUG_PRINT2 << shift << "...Skip (" << index << ") " << expr << "; uses_x: " << uses_x << "; uses_y: " << uses_y << "\n";
        return true;
    }

    Halide::Expr simplified;
    bool boring = is_expr_boring(expr, simplified, kXNames, kYNames, kConstantNames);
    if (boring) {
        DEBUG_PRINT2 << shift << "...Skip (" << index << ") " << expr << " -> " << simplified << "\t; boring? " << boring << "\n";
        return true;
    }
    return false;
}

// Should skip if they are decomposable (need to check both x and y)
bool is_decomposable(const vector<vector<bool>> &eqs_uses_x,
                     const vector<vector<bool>> &eqs_uses_y) {
    assert(eqs_uses_x.size() == eqs_uses_y.size());

    size_t size = eqs_uses_x.size();
    vector<set<int>> dependencies(size);
    for (size_t i = 0; i < size; ++i) {
        assert(eqs_uses_x[i].size() == size);
        assert(eqs_uses_y[i].size() == size);
        for (size_t j = 0; j < eqs_uses_x[i].size(); ++j) {
            if (eqs_uses_x[i][j]) {
                dependencies[i].insert(j);
            }
        }
        for (size_t j = 0; j < eqs_uses_y[i].size(); ++j) {
            if (eqs_uses_y[i][j]) {
                dependencies[i].insert(j);
            }
        }
    }
    //std::cout << "\nOriginal dependencies: " << dependencies << "\n";

    bool change = true;
    while (change) {
        change = false;
        for (size_t i = 0; i < dependencies.size(); ++i) {
            for (size_t j = 0; j < dependencies.size(); ++j) {
                if (i == j) {
                    continue;
                }
                if (dependencies[i].find(j) != dependencies[i].end()) {
                    for (const auto &idx : dependencies[j]) {
                        if (dependencies[i].find(idx) == dependencies[i].end()) {
                            dependencies[i].insert(idx);
                            change = true;
                        }
                    }
                }
            }
        }
    }

    //std::cout << "Dependencies: " << dependencies << "\n";

    const auto &subgraphs = compute_subgraphs(dependencies);
    //std::cout << "Subgraphs: " << subgraphs << "\n";
    for (const auto &s : subgraphs) {
        if (s.size() == size) {
            return false;
        }
    }
    return true;
}

bool z3_check_associativity(vector<Halide::Expr> &eqs, vector<Halide::Expr> &kXVars,
                            vector<Halide::Expr> &kYVars, vector<Halide::Expr> &kConstants,
                            vector<uint64_t> leaves, vector<uint64_t> is) {
    Halide::Tuple tuple_eqs(eqs);
    pair<IsAssociative, AssociativeIds> result = prove_associativity(tuple_eqs, kXVars, kYVars, kConstants);
    if (result.first == IsAssociative::YES) {
        if (result.second.associativity == AssociativeIds::LEFT) {
            print_coordinate(leaves, is);
            std::cout << ", " << tuple_eqs << " -> Left-associativity";
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            print_coordinate(leaves, is);
            std::cout << ", " << tuple_eqs << " -> Right-associativity";
        } else {
            //print_coordinate(leaves, is);
            //std::cout << tuple_eqs << " -> Unknown-associativity\n";
            return false;
        }
        std::cout << " with identity: " << Halide::Tuple(result.second.identities) << "\n";
    } else if (result.first == IsAssociative::UNKNOWN) {
        if (result.second.associativity == AssociativeIds::LEFT) {
            print_coordinate(leaves, is);
            std::cout << ", " << tuple_eqs << " -> UNKNOWN associative with left-identity: ";
        } else if (result.second.associativity == AssociativeIds::RIGHT) {
            print_coordinate(leaves, is);
            std::cout << ", " << tuple_eqs << " -> UNKNOWN associative with right-identity: ";
        } else {
            //print_coordinate(leaves, is);
            //std::cout << tuple_eqs << " -> UNKNOWN associative\n";
            return false;
        }
        std::cout << Halide::Tuple(result.second.identities) << "\n";
    } else {
        //print_coordinate(leaves, is);
        //std::cout << tuple_eqs << " -> " << "NOT associative\n";
        return false;
    }
    return true;
}

void is_decomposable_test() {
    if (0) {
        Expr e0(4), e1(4), e2(4), e3(4);
        e0.uses_x[0] = true;
        e0.uses_x[1] = true;
        e0.uses_y[0] = true;
        e0.uses_y[2] = true;

        e1.uses_x[0] = true;
        e1.uses_x[1] = true;
        e1.uses_y[1] = true;
        e1.uses_y[3] = true;

        e2.uses_x[2] = true;
        e2.uses_x[3] = true;
        e2.uses_y[0] = true;
        e2.uses_y[2] = true;

        e3.uses_x[2] = true;
        e3.uses_x[3] = true;
        e3.uses_y[1] = true;
        e3.uses_y[3] = true;

        vector<vector<bool>> eqs_uses_x = {e0.uses_x, e1.uses_x, e2.uses_x, e3.uses_x};
        vector<vector<bool>> eqs_uses_y = {e0.uses_y, e1.uses_y, e2.uses_y, e3.uses_y};
        bool result = is_decomposable(eqs_uses_x, eqs_uses_y);
        std::cout << "Decomposable? " << result << "\n";
    }
    {
        Expr e0(3), e1(3), e2(3);
        e0.uses_x[0] = true;
        e0.uses_y[0] = true;

        e1.uses_x[0] = true;
        e1.uses_y[1] = true;

        e2.uses_x[2] = true;
        e2.uses_y[2] = true;

        vector<vector<bool>> eqs_uses_x = {e0.uses_x, e1.uses_x, e2.uses_x};
        vector<vector<bool>> eqs_uses_y = {e0.uses_y, e1.uses_y, e2.uses_y};
        bool result = is_decomposable(eqs_uses_x, eqs_uses_y);
        std::cout << "Decomposable? " << result << "\n";
    }
}