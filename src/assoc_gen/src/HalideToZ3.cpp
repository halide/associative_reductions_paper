#include "HalideToZ3.h"
#include "Z3OpsHelper.h"
#include "Error.h"

#include <map>

using namespace Halide;
using namespace Halide::Internal;

using std::map;
using std::string;
using std::vector;

namespace {

class HalideToZ3 : public IRVisitor {
private:
    z3::context *ctx_ptr;
    bool use_bv;
    map<string, z3::expr> variables; // Map of name -> z3 variables we have made so far

    void error() {
        ASSERT(false, "Can't convert to z3 expr\n");
    }

    void assert_type(Type t) {
        ASSERT(t.is_scalar(), "Can only handle scalar variable");
        ASSERT(t.is_int() || t.is_uint(),
               "Can only handle int/uint variable");
        //TODO(psuriana): floating-point to be implemented later
    }

public:
    z3::expr expr;

    HalideToZ3(z3::context *c, bool use_bv) : ctx_ptr(c), use_bv(use_bv), expr(*c) {}

    ~HalideToZ3() { ctx_ptr = nullptr; }

    z3::expr mutate(Expr e) {
        ASSERT(e.defined(), "HalideToZ3 can't convert undefined expr\n");
        assert_type(e.type());
        if (e.defined()) {
            e.accept(this);
        }
        return expr;
    }

protected:
    void visit(const IntImm *);
    void visit(const UIntImm *);
    void visit(const FloatImm *);
    void visit(const Cast *);
    void visit(const Variable *);
    void visit(const Add *);
    void visit(const Sub *);
    void visit(const Mul *);
    void visit(const Div *);
    void visit(const Mod *);
    void visit(const Min *);
    void visit(const Max *);
    void visit(const EQ *);
    void visit(const NE *);
    void visit(const LT *);
    void visit(const LE *);
    void visit(const GT *);
    void visit(const GE *);
    void visit(const And *);
    void visit(const Or *);
    void visit(const Not *);
    void visit(const Select *);

    void visit(const StringImm *)           { error(); }
    void visit(const Load *)                { error(); }
    void visit(const Ramp *)                { error(); }
    void visit(const Broadcast *)           { error(); }
    void visit(const Call *)                { error(); }
    void visit(const Let *)                 { error(); }
    void visit(const LetStmt *)             { error(); }
    void visit(const AssertStmt *)          { error(); }
    void visit(const ProducerConsumer *)    { error(); }
    void visit(const For *)                 { error(); }
    void visit(const Store *)               { error(); }
    void visit(const Provide *)             { error(); }
    void visit(const Allocate *)            { error(); }
    void visit(const Realize *)             { error(); }
    void visit(const Block *)               { error(); }
    void visit(const IfThenElse *)          { error(); }
    void visit(const Free *)                { error(); }
    void visit(const Evaluate *)            { error(); }
};

void HalideToZ3::visit(const IntImm *op) {
    expr = ctx_ptr->bv_val((int)op->value, op->type.bits());
}

void HalideToZ3::visit(const UIntImm *op) {
    expr = ctx_ptr->bv_val((unsigned)op->value, op->type.bits());
}

void HalideToZ3::visit(const FloatImm *op) {
    //TODO(psuriana): support floating point
    ASSERT(false, "Other types besides int/uint are not currently supported\n");
}

void HalideToZ3::visit(const Cast *op) {
    z3::expr value = mutate(op->value);
    expr = bvcast(value, op->value.type().bits(), op->type.bits(), !op->type.is_uint());
}

void HalideToZ3::visit(const Variable *op) {
    const auto &iter = variables.find(op->name);
    if (iter != variables.end()) {
        expr = iter->second;
        //TODO(psuriana): add check for floating point
        //ASSERT(expr.is_bv(), "Different types");
    } else {
        if (op->type.is_int() || op->type.is_uint()) {
            if (!use_bv && op->type.bits() >= 32) {
                expr = ctx_ptr->int_const(op->name.c_str());
            } else {
                expr = ctx_ptr->bv_const(op->name.c_str(), op->type.bits());
            }
        } else {
            //TODO(psuriana): support floating point
            ASSERT(false, "Other types besides int/uint are not currently supported\n");
        }
        variables.emplace(op->name, expr);
    }
}

void HalideToZ3::visit(const Add *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    expr = a + b;
}

void HalideToZ3::visit(const Sub *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    expr = a - b;
}

void HalideToZ3::visit(const Mul *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    expr = a * b;
}

void HalideToZ3::visit(const Div *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->type.is_uint()) {
        expr = z3::udiv(a, b);
    } else {
        expr = a / b;
    }
}

void HalideToZ3::visit(const Mod *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->type.is_uint()) {
        expr = z3::bvumod(a, b);
    } else if (op->type.is_int()) {
        expr = z3::bvsmod(a, b);
    } else {
        expr = z3::mod(a, b);
    }
}

void HalideToZ3::visit(const Min *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->type.is_uint()) {
        expr = z3::umin(a, b);
    } else {
        expr = z3::min(a, b);
    }
}

void HalideToZ3::visit(const Max *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->type.is_uint()) {
        expr = z3::umax(a, b);
    } else {
        expr = z3::max(a, b);
    }
}

void HalideToZ3::visit(const EQ *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    expr = (a == b);
}

void HalideToZ3::visit(const NE *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    expr = (a != b);
}

void HalideToZ3::visit(const LT *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->a.type().is_uint()) {
        expr = z3::ult(a, b);
    } else {
        expr = (a < b);
    }
}

void HalideToZ3::visit(const LE *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->a.type().is_uint()) {
        expr = z3::ule(a, b);
    } else {
        expr = (a <= b);
    }
}

void HalideToZ3::visit(const GT *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->a.type().is_uint()) {
        expr = z3::ugt(a, b);
    } else {
        expr = (a > b);
    }
}

void HalideToZ3::visit(const GE *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    if (op->a.type().is_uint()) {
        expr = z3::uge(a, b);
    } else {
        expr = (a >= b);
    }
}

void HalideToZ3::visit(const And *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    expr = (a && b);
}

void HalideToZ3::visit(const Or *op) {
    z3::expr a = mutate(op->a);
    z3::expr b = mutate(op->b);
    expr = (a || b);
}

void HalideToZ3::visit(const Not *op) {
    z3::expr a = mutate(op->a);
    expr = !a;
}

void HalideToZ3::visit(const Select *op) {
    z3::expr cond = mutate(op->condition);
    z3::expr t = mutate(op->true_value);
    z3::expr f = mutate(op->false_value);
    expr = z3::ite(cond, t, f);
}

} // anonymous namespace

z3::expr convert_halide_to_z3(Expr e, z3::context *ctx_ptr, bool use_bv) {
    HalideToZ3 converter(ctx_ptr, use_bv);
    e.accept(&converter);
    return converter.expr;
}

namespace {

void basic_tests(Type t, z3::context *ctx_ptr, const vector<Expr> &additional_tests) {
    Expr x = Variable::make(t, "x");
    Expr y = Variable::make(t, "y");
    Expr z = Variable::make(t, "z");

    vector<Expr> halide_exprs = {
        Add::make(x, y),
        Sub::make(x, y),
        Mul::make(x, y),
        Div::make(x, y),
        Mod::make(x, y),
        Min::make(x, y),
        Max::make(x, y),
        EQ::make(x, y),
        NE::make(x, y),
        LT::make(x, y),
        LE::make(x, y),
        GT::make(x, y),
        GE::make(x, y),
        And::make(x > y, y == 2),
        Or::make(x >= z, y <= 2),
        Not::make(x < y),
        Select::make(x >= y + z, (z * y)/x, (x % y) - z)
    };

    halide_exprs.insert(halide_exprs.end(), additional_tests.begin(), additional_tests.end());
    for (const auto &e : halide_exprs) {
        std::cout << "Halide expr: " << e << ", ";
        z3::expr z3_expr = convert_halide_to_z3(e, ctx_ptr, true);
        std::cout << "\tZ3 expr: " << z3_expr << "\n";
    }
}

} // anonymous namespace

void halide_to_z3_test() {
    z3::context ctx;

    {
        // Signed integer
        Type t = Int(32);
        Expr x = Variable::make(t, "x");
        Expr y = Variable::make(t, "y");
        Expr z = Variable::make(t, "z");

        vector<Expr> additional_tests = {
            IntImm::make(t, 1),
            Cast::make(Int(8), x),
            Cast::make(Int(16), x),
            Cast::make(Int(32), x),
            Cast::make(Int(64), x),
            Cast::make(UInt(32), -1),
        };
        std::cout << "Run tests for signed integers\n";
        basic_tests(t, &ctx, additional_tests);
    }

    {
        // Unsigned integer
        Type t = UInt(32);
        Expr x = Variable::make(t, "x");
        Expr y = Variable::make(t, "y");
        Expr z = Variable::make(t, "z");

        vector<Expr> additional_tests = {
            UIntImm::make(t, 1),
            Cast::make(UInt(8), x),
            Cast::make(UInt(16), x),
            Cast::make(UInt(32), x),
            Cast::make(UInt(64), x),
            Cast::make(Int(32), 1),
        };
        std::cout << "\nRun tests for unsigned integers\n";
        basic_tests(t, &ctx, additional_tests);
    }
}
