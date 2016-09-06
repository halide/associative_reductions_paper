#include "AssociativityProver.h"
#include "Z3OpsHelper.h"
#include "HalideToZ3.h"
#include "Error.h"

#include <map>

using namespace Halide;
using namespace Halide::Internal;

using std::map;
using std::pair;
using std::string;
using std::vector;

const unsigned TIMEOUT = 1000*10u;

namespace {

void print_tuple(const Tuple &tuple) {
    std::cout << "{ ";
    for (size_t i = 0; i < tuple.size(); ++i) {
        std::cout << tuple[i];
        if (i != tuple.size() - 1) {
            std::cout << ", ";
        }
    }
    std::cout << " }\n";
}

class CheckVars : public IRVisitor {
    using IRVisitor::visit;

    vector<string> vars;

    bool valid_var(const string &name, int expected_index = -1) {
        if (!valid) {
            return valid;
        }

        if (name.size() == 1) {
            return (name == "x") || (name == "y") || (name == "k");
        }

        const char &var = name[0];
        if (!((var == 'x') || (var == 'y') || (var == 'k'))) {
            valid = false;
            return valid;
        }

        string index_str = name.substr(1, name.size()-1);
        // Check if index contains only digits
        valid = (index_str.find_first_not_of( "0123456789" ) == string::npos);
        if (!valid) {
            return valid;
        }

        if ((var != 'k') && (expected_index != -1)) {
            int index = std::stoi(index_str);
            valid = (index == expected_index);
        }
        return valid;
    }

    void visit(const Variable *op) {
        if (!valid_var(op->name)) {
            valid = false;
        }
        if (std::find(vars.begin(), vars.end(), op->name) == vars.end()) {
            DEBUG_PRINT << "Could not find " << op->name << "\n";
            valid = false;
        }
    }

public:
    bool valid;
    CheckVars(const vector<Expr> &xvars, const vector<Expr> &yvars,
              const vector<Expr> &constants) : valid(true) {
        for (size_t i = 0; i < xvars.size(); ++i) {
            const Variable *var = xvars[i].as<Variable>();
            ASSERT(var != nullptr, "Expect a variable\n");
            if (!valid_var(var->name, i)) {
                DEBUG_PRINT << var->name << " is NOT valid\n";
                break;
            }
            vars.push_back(var->name);
        }

        for (size_t i = 0; i < yvars.size(); ++i) {
            const Variable *var = yvars[i].as<Variable>();
            ASSERT(var != nullptr, "Expect a variable\n");
            if (!valid_var(var->name, i)) {
                DEBUG_PRINT << var->name << " is NOT valid\n";
                break;
            }
            vars.push_back(var->name);
        }

        for (size_t i = 0; i < constants.size(); ++i) {
            const Variable *var = constants[i].as<Variable>();
            ASSERT(var != nullptr, "Expect a constant variable\n");
            if (!valid_var(var->name, i)) {
                DEBUG_PRINT << var->name << " is NOT valid\n";
                break;
            }
            vars.push_back(var->name);
        }
    }
};

bool check_vars_validity(Expr e, const vector<Expr> &xvars, const vector<Expr> &yvars,
                         const vector<Expr> &constants) {
    CheckVars check(xvars, yvars, constants);
    e.accept(&check);
    return check.valid;
}

bool z3_find_identity(const z3::expr &equation, const vector<Type> types,
                      const z3::expr_vector &qvars, const z3::expr_vector &evars,
                      vector<Expr> &result) {
    DEBUG_PRINT << "Finding identity of " << equation << "\n";
    z3::context &ctx = equation.ctx();
    z3::solver s(ctx);
    z3::params p(ctx);
    p.set(":timeout", TIMEOUT);
    s.set(p);
    z3::expr qf = forall(qvars, equation);
    s.add(qf);
    DEBUG_PRINT << s.to_smt2() << "\n";

    if (s.check() != z3::sat) {
        DEBUG_PRINT << "Failed to find identity of " << equation << "\n";
        return false;
    }

    z3::model m = s.get_model();
    DEBUG_PRINT << "\nModel: \n" << m << "\n";

    result.resize(evars.size());
    for (size_t i = 0; i < evars.size(); ++i) {
        // Convert z3 id to halide expr
        z3::expr z3_id = m.eval(evars[i]);
        const Type &t = types[i];
        bool is_signed = t.is_int();

        //TODO(psuriana): add handler for float
        if (!z3_id.is_numeral()) {
            // Since evars[i] is not constrained by the model, we can pick any
            // value. We'll pick 0 here.
            if (is_signed) {
                result[i] = IntImm::make(t, 0);
            } else {
                result[i] = UIntImm::make(t, 0);
            }
        } else {
            if (is_signed) {
                Expr min_int_expr = t.min();
                const IntImm *min_int = min_int_expr.as<IntImm>();
                ASSERT(min_int != nullptr, "Should have been an int\n");
                result[i] = IntImm::make(t, z3::to_int(z3_id, t.bits(), min_int->value));
            } else {
                result[i] = UIntImm::make(t, z3::to_uint(z3_id));
            }
        }
    }
    return true;
}

IsAssociative z3_prove_associativity(const z3::expr &conjecture) {
    DEBUG_PRINT << "Proving associativity of:\n" << conjecture << "\n";

    z3::context &ctx = conjecture.ctx();
    z3::solver s(ctx);
    // Set solver timeout
    z3::params p(ctx);
    p.set(":timeout", TIMEOUT);
    s.set(p);
    s.add(!conjecture);

    if (s.check() == z3::unsat) {
        DEBUG_PRINT << "Succeeded at proving associativity\n";
        return IsAssociative::YES;
    } else if (s.check() == z3::unknown) {
        return IsAssociative::UNKNOWN;
    } else {
        DEBUG_PRINT << "Failed to prove associativity\n";
        DEBUG_PRINT << "Counter example:\n" << s.get_model() << "\n";
        return IsAssociative::NO;
    }
}

IsAssociative prove_associativity_helper(const Halide::Tuple &tuple,
                                         const vector<Expr> &xvars,
                                         const vector<Expr> &yvars,
                                         const vector<Expr> &constants,
                                         z3::context &ctx) {
    const vector<Expr> &ops = tuple.as_vector();

    vector<string> xnames(ops.size()), ynames(ops.size()), znames(ops.size());

    vector<Expr> zvars(ops.size());
    for (size_t i = 0; i < ops.size(); ++i) {
        const Variable *x = xvars[i].as<Variable>();
        const Variable *y = yvars[i].as<Variable>();
        ASSERT((x != nullptr) && (y != nullptr), "x and y should be variables\n");
        ASSERT(x->type == y->type, "Expect xvar and yvar to be of the same type\n");

        xnames[i] = x->name;
        ynames[i] = y->name;
        znames[i] = "z" + std::to_string(i);
        zvars[i] = Variable::make(xvars[i].type(), znames[i]);
    }

    vector<Expr> lhs(ops), rhs(ops);
    {
        // f(x, z) -> f(f(x, y), z)
        map<string, Expr> replacement1, replacement2;
        for (size_t j = 0; j < ops.size(); ++j) {
            replacement1.emplace(ynames[j], zvars[j]);  // y -> z
            replacement2.emplace(xnames[j], ops[j]);    // x -> f(x, y)
        }
        for (size_t i = 0; i < ops.size(); ++i) {
            lhs[i] = substitute(replacement1, lhs[i]);
            lhs[i] = substitute(replacement2, lhs[i]);
        }
    }

    DEBUG_PRINT << "LHS:\n{\n";
    for (size_t i = 0; i < ops.size(); ++i) {
        DEBUG_PRINT << "   " << lhs[i] << "\n";
    }
    DEBUG_PRINT << "}\n";

    {
        map<string, Expr> replacement1;
        for (size_t j = 0; j < ops.size(); ++j) {
            replacement1.emplace(xnames[j], yvars[j]);  // x -> y
            replacement1.emplace(ynames[j], zvars[j]);  // y -> z
        }
        vector<Expr> tmp(ops);
        for (size_t i = 0; i < ops.size(); ++i) {
            // f(x, y) -> f(y, z)
            tmp[i] = substitute(replacement1, tmp[i]);
        }
        map<string, Expr> replacement2;
        for (size_t j = 0; j < ops.size(); ++j) {
            replacement2.emplace(ynames[j], tmp[j]);
        }
        for (size_t i = 0; i < ops.size(); ++i) {
            // f(x, y) -> f(x, f(y, z))
            rhs[i] = substitute(replacement2, rhs[i]);
        }
    }

    DEBUG_PRINT << "RHS:\n{\n";
    for (size_t i = 0; i < ops.size(); ++i) {
        DEBUG_PRINT << "   " << rhs[i] << "\n";
    }
    DEBUG_PRINT << "}\n";

    Expr conjecture = (lhs[0] == rhs[0]);
    for (size_t i = 1; i < ops.size(); ++i) {
        conjecture = conjecture && (lhs[i] == rhs[i]);
    }

    IsAssociative result = z3_prove_associativity(convert_halide_to_z3(conjecture, &ctx, true));
    if (result != IsAssociative::YES) {
        DEBUG_PRINT << "Cannot prove associativity of Tuple\n";
        /*result = z3_prove_associativity(convert_halide_to_z3(conjecture, &ctx, false));
        if (result != IsAssociative::YES) {
            DEBUG_PRINT << "Cannot prove associativity of Tuple\n";
        }*/
    }
    return result;
}

AssociativeIds find_identity(const Halide::Tuple &tuple,
                             const vector<Expr> &xvars,
                             const vector<Expr> &yvars,
                             const vector<Expr> &constants,
                             z3::context &ctx,
                             bool use_bv) {
    const vector<Expr> &ops = tuple.as_vector();

    vector<Type> types(ops.size());
    vector<string> xnames(ops.size()), ynames(ops.size()), enames(ops.size());
    vector<Expr> evars(ops.size());
    z3::expr_vector z3_xqvars(ctx), z3_yqvars(ctx), z3_constants(ctx), z3_evars(ctx);

    for (size_t i = 0; i < ops.size(); ++i) {
        const Variable *x = xvars[i].as<Variable>();
        const Variable *y = yvars[i].as<Variable>();
        ASSERT((x != nullptr) && (y != nullptr), "x and y should be variables\n");
        ASSERT(x->type == y->type, "Expect xvar and yvar to be of the same type\n");

        types[i] = x->type;
        xnames[i] = x->name;
        ynames[i] = y->name;
        enames[i] = "e" + std::to_string(i);
        evars[i] = Variable::make(xvars[i].type(), enames[i]);
        z3_xqvars.push_back(convert_halide_to_z3(xvars[i], &ctx, use_bv));
        z3_yqvars.push_back(convert_halide_to_z3(yvars[i], &ctx, use_bv));
        z3_evars.push_back(convert_halide_to_z3(evars[i], &ctx, use_bv));
    }
    for (size_t i = 0; i < constants.size(); ++i) {
        z3_xqvars.push_back(convert_halide_to_z3(constants[i], &ctx, use_bv));
        z3_yqvars.push_back(convert_halide_to_z3(constants[i], &ctx, use_bv));
    }

    AssociativeIds result;

    // First, try to find a left-identity
    {
        vector<Expr> lhs(ops);

        map<string, Expr> replacement;
        for (size_t j = 0; j < ops.size(); ++j) {
            replacement.emplace(xnames[j], evars[j]);
        }
        for (size_t i = 0; i < ops.size(); ++i) {
            // f(e, y) : x -> e
            lhs[i] = substitute(replacement, lhs[i]);
        }

        DEBUG_PRINT << "Left-identity:\n{\n";
        for (size_t i = 0; i < ops.size(); ++i) {
            DEBUG_PRINT << "   " << lhs[i] << "\n";
        }
        DEBUG_PRINT << "}\n";

        Expr equation = (lhs[0] == yvars[0]);
        for (size_t i = 1; i < ops.size(); ++i) {
            equation = equation && (lhs[i] == yvars[i]);
        }

        DEBUG_PRINT << "\n****Finding identity of " << equation << "\n";
        if (z3_find_identity(convert_halide_to_z3(equation, &ctx, use_bv),
                             types, z3_yqvars, z3_evars,
                             result.identities)) {
            result.associativity = AssociativeIds::LEFT;
            DEBUG_PRINT << "Found left-identity\n";
            return result;
        }
    }

    // Failed to find left-identity, try to find a right-identity
    {
        vector<Expr> rhs(ops);

        // Right identity f(x, e) : y -> e
        map<string, Expr> replacement;
        for (size_t j = 0; j < ops.size(); ++j) {
            replacement.emplace(ynames[j], evars[j]);  // y -> e
        }
        for (size_t i = 0; i < ops.size(); ++i) {
            rhs[i] = substitute(replacement, rhs[i]);
        }

        DEBUG_PRINT << "Right-identity:\n{\n";
        for (size_t i = 0; i < ops.size(); ++i) {
            DEBUG_PRINT << "   " << rhs[i] << "\n";
        }
        DEBUG_PRINT << "}\n";

        Expr equation = (rhs[0] == xvars[0]);
        for (size_t i = 1; i < ops.size(); ++i) {
            equation = equation && (rhs[i] == xvars[i]);
        }

        if (z3_find_identity(convert_halide_to_z3(equation, &ctx, use_bv),
                             types, z3_xqvars, z3_evars,
                             result.identities)) {
            result.associativity = AssociativeIds::RIGHT;
            DEBUG_PRINT << "Found right-identity\n";
            return result;
        }
    }

    return result;
}

} // anonymous namespace

pair<IsAssociative, AssociativeIds> prove_associativity(const Halide::Expr &expr,
                                                        const vector<Expr> &xvars,
                                                        const vector<Expr> &yvars,
                                                        const vector<Expr> &constants) {
    return prove_associativity(Tuple(expr), xvars, yvars, constants);
}


pair<IsAssociative, AssociativeIds> prove_associativity(const Halide::Tuple &tuple,
                                                        const vector<Expr> &xvars,
                                                        const vector<Expr> &yvars,
                                                        const vector<Expr> &constants) {

    ASSERT((xvars.size() == yvars.size()) && (xvars.size() == tuple.size()),
        "Expect xvars, yvars, and tuple of exprs to all be of the same size\n");

    for (const auto &e : tuple.as_vector()) {
        ASSERT(check_vars_validity(e, xvars, yvars, constants), "Contains invalid vars\n");
    }

    z3::context ctx;
    AssociativeIds identities;

    IsAssociative is_associative = prove_associativity_helper(tuple, xvars, yvars, constants, ctx);

    if (is_associative != IsAssociative::NO) {
        identities = find_identity(tuple, xvars, yvars, constants, ctx, true);
        /*if (identities.associativity == AssociativeIds::UNKNOWN) {
            DEBUG_PRINT << "SWITCH to infinite integer when finding identity\n";
            identities = find_identity(tuple, xvars, yvars, constants, ctx, false);
        }*/
        return std::make_pair(is_associative, identities);
    }
    return std::make_pair(is_associative, identities);
}

namespace {

void run_test(const Tuple &eq, const vector<Expr> &xvars, const vector<Expr> &yvars,
              const vector<Expr> &constants, IsAssociative is_associative,
              AssociativeIds::Associativity expected_associativity,
              const vector<Expr> &expected_identities) {
    std::cout << "\nProving associativity of:\n  ";
    print_tuple(eq);
    pair<IsAssociative, AssociativeIds> result = prove_associativity(eq, xvars, yvars, constants);

    //ASSERT(is_associative == result.first, "");
    std::cout << "   Is associative? ";
    if (result.first == IsAssociative::YES) {
        std::cout << "YES\n";
    } else if (result.first == IsAssociative::NO) {
        std::cout << "NO\n";
    } else {
        std::cout << "UNKNOWN\n";
    }
    if (is_associative != IsAssociative::YES) {
        return;
    }

    std::cout << "   Associativity? ";
    if (result.second.associativity == AssociativeIds::LEFT) {
        std::cout << "left\n";
    } else if (result.second.associativity == AssociativeIds::RIGHT) {
        std::cout << "right\n";
    } else {
        std::cout << "unknown\n";
        return;
    }
    std::cout << "   Identity: ";
    print_tuple(Tuple(result.second.identities));

    /*for (size_t i = 0; i < eq.size(); ++i) {
        if (!equal(result.second.identities[i], expected_identities[i])) {
            std::cout << "Expected identity at index " << i << " to be: "
                      << expected_identities[i] << "\nGot instead: "
                      << result.second.identities[i] << "\n";
            ASSERT(false, "");
        }
    }*/
}

} // anonymous namespace

void associativity_prover_test() {
    /*{
        vector<Type> types = {
            UInt(8),
            UInt(16),
            UInt(32),
            UInt(64),
            Int(8),
            Int(16),
            Int(32),
            Int(64),
        };
        for (const Type &t : types) {
            Expr x = Variable::make(t, "x");
            Expr y = Variable::make(t, "y");
            Expr k = Variable::make(t, "k");

            vector<Expr> xvars = {x};
            vector<Expr> yvars = {y};
            vector<Expr> constants = {k};

            vector<vector<Expr>> eqs = {
                {max(x, y)},
                {min(x, y)},
                {x + y},
                {x * y},
                {x + y + k*x*y},
            };

            vector<vector<Expr>> ids = {
                {t.min()},
                {t.max()},
            };

            if (t.is_int()) {
                ids.push_back({IntImm::make(t, 0)});
                ids.push_back({IntImm::make(t, 1)});
                ids.push_back({IntImm::make(t, 0)});
            } else {
                ids.push_back({UIntImm::make(t, 0)});
                ids.push_back({UIntImm::make(t, 1)});
                ids.push_back({UIntImm::make(t, 0)});
            }

            for (size_t i = 0; i < eqs.size(); ++i) {
                run_test(Tuple(eqs[i]), xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, ids[i]);
            }
        }
    }

    {
        Type t = Int(8);
        Expr x0 = Variable::make(t, "x0");
        Expr y0 = Variable::make(t, "y0");

        vector<Expr> xvars = {x0};
        vector<Expr> yvars = {y0};
        vector<Expr> constants = {};

        Tuple eq = Tuple(cast<uint8_t>(min(cast<uint16_t>(x0) + cast<uint16_t>(y0) , 255)));
        vector<Expr> expected_identities = {IntImm::make(t, 0)};
        run_test(eq, xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, expected_identities);
    }

    {
        Type t = Int(8);
        Expr x0 = Variable::make(t, "x0");
        Expr y0 = Variable::make(t, "y0");

        vector<Expr> xvars = {x0};
        vector<Expr> yvars = {y0};
        vector<Expr> constants = {};

        Tuple eq = Tuple(max(min(y0, x0), y0));
        vector<Expr> expected_identities = {IntImm::make(t, 0)};
        run_test(eq, xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, expected_identities);
    }*/

    /*{
        Type t = Int(32);
        Expr x0 = Variable::make(t, "x0");
        Expr y0 = Variable::make(t, "y0");
        Expr x1 = Variable::make(t, "x1");
        Expr y1 = Variable::make(t, "y1");

        vector<Expr> xvars = {x0, x1};
        vector<Expr> yvars = {y0, y1};
        vector<Expr> constants = {};

        vector<vector<Expr>> eqs = {
            {min(x0, y0), select(x0 < y0, x1, y1)},
            {x0*y0 - x1*y1, x0*y1 + x1*y0},
            {x0 + y0, x1*y1},
        };

        vector<vector<Expr>> ids = {
            {t.max(), t.max()},
            {IntImm::make(t, 1), IntImm::make(t, 0)},
            {IntImm::make(t, 0), IntImm::make(t, 1)},
        };

        for (size_t i = 0; i < eqs.size(); ++i) {
            run_test(Tuple(eqs[i]), xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, ids[i]);
        }
    }*/

    /*{
        Type t = Int(32);
        Expr x0 = Variable::make(t, "x0");
        Expr y0 = Variable::make(t, "y0");

        vector<Expr> xvars = {x0};
        vector<Expr> yvars = {y0};
        vector<Expr> constants = {};

        // f(x, y) = 2*x*y -> requires x and y to be real to find an identity
        Tuple eq = Tuple((((y0 + x0) - (y0 - x0))*y0));
        vector<Expr> expected_identities = {IntImm::make(t, 0)};
        run_test(eq, xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, expected_identities);
    }*/

    /*{
        Type t = Int(8);
        Expr x0 = Variable::make(t, "x0");
        Expr y0 = Variable::make(t, "y0");

        vector<Expr> xvars = {x0};
        vector<Expr> yvars = {y0};
        vector<Expr> constants = {};

        Tuple eq = Tuple((max(y0, x0)*min(y0, x0)));
        vector<Expr> expected_identities = {IntImm::make(t, 0)};
        run_test(eq, xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, expected_identities);
    }*/

    /*{
        Type t = Int(32);
        Expr x0 = Variable::make(t, "x0");
        Expr y0 = Variable::make(t, "y0");
        Expr x1 = Variable::make(t, "x1");
        Expr y1 = Variable::make(t, "y1");

        vector<Expr> xvars = {x0, x1};
        vector<Expr> yvars = {y0, y1};
        vector<Expr> constants = {};

        Expr cond = (x1 > y1) || ((x1 == y1) && (x0 > y0));

        vector<vector<Expr>> eqs = {
            {select(cond, x0, y0), select(cond, x1, y1)},
        };

        vector<vector<Expr>> ids = {
            {t.min(), t.min()},
        };

        for (size_t i = 0; i < eqs.size(); ++i) {
            run_test(Tuple(eqs[i]), xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, ids[i]);
        }
    }*/

    /*{
        Type t = UInt(64);
        Expr x0 = Variable::make(t, "x0");
        Expr y0 = Variable::make(t, "y0");
        Expr x1 = Variable::make(t, "x1");
        Expr y1 = Variable::make(t, "y1");

        vector<Expr> xvars = {x0, x1};
        vector<Expr> yvars = {y0, y1};
        vector<Expr> constants = {};

        Expr cond = x0 > t.max() - y0;

        vector<vector<Expr>> eqs = {
            {x0 + y0, x1 + y1 + select(cond, make_const(t, 1), make_const(t, 0))},
        };

        vector<vector<Expr>> ids = {
            {make_const(t, 0), make_const(t, 0)},
        };

        for (size_t i = 0; i < eqs.size(); ++i) {
            run_test(Tuple(eqs[i]), xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, ids[i]);
        }
    }*/

    {
        Type t = Int(32);
        Expr x0 = Variable::make(t, "x0");
        Expr x1 = Variable::make(t, "x1");
        Expr y0 = Variable::make(t, "y0");
        Expr y1 = Variable::make(t, "y1");
        Expr k0 = Variable::make(t, "k0");

        vector<Expr> xvars = {x0, x1};
        vector<Expr> yvars = {y0, y1};
        vector<Expr> constants = {k0};

        //Tuple eq = Tuple(max((min((k0 - max((x0 + k0), y0)), x0) + x0), x0));
        Tuple eq = {max(max(x0, y1), y0), min(max(x0, y1), y0)};
        vector<Expr> expected_identities = {IntImm::make(t, 0)};
        //run_test(eq, xvars, yvars, constants, IsAssociative::YES, AssociativeIds::LEFT, expected_identities);
        Expr expr = Max::make(Min::make(x1, y1), x0);
        std::cout << expr << "\n";
    }

    /*Type t = Int(32);
    Expr x0 = Variable::make(t, "x0");
    Expr y0 = Variable::make(t, "y0");
    Expr x1 = Variable::make(t, "x1");
    Expr y1 = Variable::make(t, "y1");
    Expr expr = ((x0*y1) - (x1*y0));
    std::cout << expr << " -> " << simplify(expr) << "\n";*/
}
