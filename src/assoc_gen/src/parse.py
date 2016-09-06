import re
filename = "single_constant.txt"
pattern  = '(\.+)\d, (\.+) -> Left-associativity with identity: \{ (\d+) \}'
single_i32 = set()

p_proven_associative = re.compile("Leaves: \d+, i: \d+, ([\W\w\(\)\+\-\*\/\.]*) -> (\w*)-associativity with identity: \{ ([-]{0,1}\d+) \}")
p_unknown_associative = re.compile("Leaves: \d+, i: \d+, ([\W\w\(\)\+\-\*\/\.]*) -> UNKNOWN associative with (\w*)-identity: \{ ([-]{0,1}\d+) \}")
p_ops = re.compile("(\w*)::make")

def construct_expr(expr):
    expr = expr.replace("x0", "i32_x0")
    expr = expr.replace("y0", "i32_y0")
    expr = expr.replace("x1", "i32_x1")
    expr = expr.replace("y1", "i32_y1")

    expr = expr.replace("Mul::make(i32_x0, i32_y0)", "i32_mul_x0y0")
    expr = expr.replace("Mul::make(i32_x0, i32_x0)", "i32_mul_x0x0")
    expr = expr.replace("Mul::make(i32_y0, i32_y0)", "i32_mul_y0y0")
    expr = expr.replace("Add::make(i32_x0, i32_y0)", "i32_add_x0y0")
    expr = expr.replace("Max::make(i32_x0, i32_y0)", "i32_max_x0y0")
    expr = expr.replace("Min::make(i32_x0, i32_y0)", "i32_min_x0y0")
    expr = expr.replace("Sub::make(i32_x0, i32_y0)", "i32_sub_x0y0")
    expr = expr.replace("Sub::make(i32_y0, i32_x0)", "i32_sub_y0x0")

    expr = expr.replace("Mul::make(i32_x1, i32_y1)", "i32_mul_x1y1")
    expr = expr.replace("Mul::make(i32_x1, i32_x1)", "i32_mul_x1x1")
    expr = expr.replace("Mul::make(i32_y1, i32_y1)", "i32_mul_y1y1")
    expr = expr.replace("Add::make(i32_x1, i32_y1)", "i32_add_x1y1")
    expr = expr.replace("Max::make(i32_x1, i32_y1)", "i32_max_x1y1")
    expr = expr.replace("Min::make(i32_x1, i32_y1)", "i32_min_x1y1")
    expr = expr.replace("Sub::make(i32_x1, i32_y1)", "i32_sub_x1y1")
    expr = expr.replace("Sub::make(i32_y1, i32_x1)", "i32_sub_y1x1")

    return expr

def construct_identity(identity):
    # Replace 2147483647 with i32_tmax
    if (identity == "2147483647"):
        return "i32_tmax"
    # Replace -2147483648 with i32_tmin
    if (identity == "-2147483648"):
        return "i32_tmin"
    # Replace 0 with i32_zero
    if (identity == "0"):
        return "i32_zero"
    # Replace 1 with i32_zero
    if (identity == "1"):
        return "i32_one"
    return identity

def get_all_ops(expr):
    match = p_ops.findall(expr)
    return match

def get_match(line):
    match = p_proven_associative.findall(line)
    if (len(match) == 0):
        match = p_unknown_associative.findall(line)
    return match

# Swap x0 and y0
def swap(expr):
    original = expr
    expr = expr.replace("y0", "_y0")
    expr = expr.replace("x0", "y0")
    expr = expr.replace("_y0", "x0")
    return expr

total = 0
right = 0

# Make sure file gets closed after being iterated
print("Try open: " + filename + "\n")
with open(filename, 'r') as f:
    # Read the file contents and generate a list with each line
    lines = f.readlines()
    # Iterate each line
    for line in lines:
        # Regex applied to each line
        match = get_match(line)
        if (len(match) > 0):
            total += 1
            match = match[0]
            expr = match[0]
            identity = match[2]
            if (match[1].lower() == 'right'):
                right += 1
                expr = swap(expr)
            #single_i32.add(("\"" + expr + "\"", identity))
            single_i32.add((expr, identity))

def get_code(expr):
    substr = expr[:3]
    if (substr == "Add"):
        return 0;
    if (substr == "Mul"):
        return 1;
    if (substr == "Max"):
        return 2;
    if (substr == "Min"):
        return 3;
    if (substr == "Sub"):
        return 4;
    assert False
    return 5; # Shouldn't have gotten here

def compare_expr_single(x, y):
    x_ops = [get_code(op) for op in get_all_ops(x[0])]
    y_ops = [get_code(op) for op in get_all_ops(y[0])]
    if (x_ops < y_ops):
        return -1
    elif (x_ops == y_ops):
        return 0
    else:
        return 1


#Sort based on expr string size
#single_i32 = sorted(single_i32)
#single_i32.sort(key = lambda e: (get_code(e[0]), len(e[0])))

single_i32 = sorted(single_i32, cmp=compare_expr_single)

single_i32_add = []
single_i32_mul = []
single_i32_max = []
single_i32_min = []
single_i32_sub = []

double_i32_add = []
double_i32_mul = []
double_i32_max = []
double_i32_min = []
double_i32_sub = []

for (expr, identity) in single_i32:
    if (get_code(expr) == 0):
        table = single_i32_add
    elif (get_code(expr) == 1):
        table = single_i32_mul
    elif (get_code(expr) == 2):
        table = single_i32_max
    elif (get_code(expr) == 3):
        table = single_i32_min
    elif (get_code(expr) == 4):
        table = single_i32_sub
    table.append((construct_expr(expr), construct_identity(identity)))

print("Total exprs: " + str(total))
print("Unique exprs: " + str(len(single_i32)))
print("Right-associativity exprs: " + str(right))
for val in single_i32[:10]:
    print(val)

tab = "    "
header_filename = "AssociativeOpsTable.h"
cpp_filename = "AssociativeOpsTable.cpp"

with open(header_filename, 'w') as f:
    # Go to start of file
    f.seek(0)

    # Actually write the lines
    f.write("#ifndef HALIDE_ASSOCIATIVE_OPS_TABLE_H\n")
    f.write("#define HALIDE_ASSOCIATIVE_OPS_TABLE_H\n\n")

    f.write("/** \\file\n")
    f.write(" * Tables listing associative operators and their identities.\n")
    f.write(" */\n\n")

    #f.write("#include \"IROperator.h\"\n\n")
    f.write("#include \"Halide.h\"\n\n")
    f.write("#include <iostream>\n")
    f.write("#include <vector>\n\n")

    f.write("namespace Halide {\nnamespace Internal {\n\n")

    # Define the AssociativePair struct
    f.write("struct AssociativePair {\n")
    f.write(tab + "Expr op;\n")
    f.write(tab + "Expr identity;\n\n")

    f.write(tab + "AssociativePair() {}\n")
    f.write(tab + "AssociativePair(Expr op) : op(op) {}\n")
    f.write(tab + "AssociativePair(Expr op, Expr id) : op(op), identity(id) {}\n")
    f.write("};\n\n")

    f.write("const std::vector<std::vector<AssociativePair>> &get_i32_ops_table(const std::vector<Expr> &exprs);\n")

    f.write("\n}\n}\n\n")
    f.write("#endif\n")

with open(cpp_filename, 'w') as f:
    # Go to start of file
    f.seek(0)

    # Actually write the lines
    f.write("#include \"" + header_filename + "\"\n\n")
    f.write("using std::vector;\n\n")
    f.write("namespace Halide {\nnamespace Internal {\n\n")

    f.write("namespace {\n\n")
    f.write("const Type i32 = Int(32);\n")
    f.write("const Expr i32_zero = make_const(i32, 0);\n")
    f.write("const Expr i32_one = make_const(i32, 1);\n")
    f.write("const Expr i32_tmax = i32.max();\n")
    f.write("const Expr i32_tmin = i32.min();\n\n")

    f.write("const Expr i32_x0 = Variable::make(i32, \"x0\");\n")
    f.write("const Expr i32_y0 = Variable::make(i32, \"y0\");\n")
    f.write("const Expr i32_x1 = Variable::make(i32, \"x1\");\n")
    f.write("const Expr i32_y1 = Variable::make(i32, \"y1\");\n\n")

    f.write("const Expr i32_mul_x0y0 = Mul::make(i32_x0, i32_y0);\n")
    f.write("const Expr i32_mul_x0x0 = Mul::make(i32_x0, i32_x0);\n")
    f.write("const Expr i32_mul_y0y0 = Mul::make(i32_y0, i32_y0);\n")
    f.write("const Expr i32_add_x0y0 = Add::make(i32_x0, i32_y0);\n")
    f.write("const Expr i32_max_x0y0 = Max::make(i32_x0, i32_y0);\n")
    f.write("const Expr i32_min_x0y0 = Min::make(i32_x0, i32_y0);\n")
    f.write("const Expr i32_sub_x0y0 = Sub::make(i32_x0, i32_y0);\n")
    f.write("const Expr i32_sub_y0x0 = Sub::make(i32_y0, i32_x0);\n\n")

    f.write("const Expr i32_mul_x1y1 = Mul::make(i32_x1, i32_y1);\n")
    f.write("const Expr i32_mul_x1x1 = Mul::make(i32_x1, i32_x1);\n")
    f.write("const Expr i32_mul_y1y1 = Mul::make(i32_y1, i32_y1);\n")
    f.write("const Expr i32_add_x1y1 = Add::make(i32_x1, i32_y1);\n")
    f.write("const Expr i32_max_x1y1 = Max::make(i32_x1, i32_y1);\n")
    f.write("const Expr i32_min_x1y1 = Min::make(i32_x1, i32_y1);\n")
    f.write("const Expr i32_sub_x1y1 = Sub::make(i32_x1, i32_y1);\n")
    f.write("const Expr i32_sub_y1x1 = Sub::make(i32_y1, i32_x1);\n\n")

    f.write("const vector<vector<AssociativePair>> &get_single_i32_ops_table_add() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(single_i32_add)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(single_i32_add)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + single_i32_add[i][0] + ", " + single_i32_add[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_single_i32_ops_table_mul() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(single_i32_mul)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(single_i32_mul)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + single_i32_mul[i][0] + ", " + single_i32_mul[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_single_i32_ops_table_max() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(single_i32_max)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(single_i32_max)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + single_i32_max[i][0] + ", " + single_i32_max[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_single_i32_ops_table_min() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(single_i32_min)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(single_i32_min)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + single_i32_min[i][0] + ", " + single_i32_min[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_single_i32_ops_table_sub() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(single_i32_sub)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(single_i32_sub)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + single_i32_sub[i][0] + ", " + single_i32_sub[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("\n")

    f.write("const vector<vector<AssociativePair>> &get_double_i32_ops_table_add() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(double_i32_add)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(double_i32_add)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + double_i32_add[i][0] + ", " + double_i32_add[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_double_i32_ops_table_mul() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(double_i32_mul)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(double_i32_mul)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + double_i32_mul[i][0] + ", " + double_i32_mul[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_double_i32_ops_table_max() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(double_i32_max)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(double_i32_max)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + double_i32_max[i][0] + ", " + double_i32_max[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_double_i32_ops_table_min() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(double_i32_min)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(double_i32_min)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + double_i32_min[i][0] + ", " + double_i32_min[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("const vector<vector<AssociativePair>> &get_double_i32_ops_table_sub() {\n")
    f.write(tab + "static bool init = false;\n")
    f.write(tab + "static vector<vector<AssociativePair>> exprs(" + str(len(double_i32_sub)) + ");\n")
    f.write(tab + "if (!init) {\n")
    for i in range(len(double_i32_sub)):
        f.write(tab + tab + "exprs[" + str(i) + "] = {{" + double_i32_sub[i][0] + ", " + double_i32_sub[i][1] + "}};\n")
    f.write(tab + tab + "init = true;\n")
    f.write(tab + "}\n")
    f.write(tab + "return exprs;\n")
    f.write("}\n\n");

    f.write("} // anonymous namespace\n\n")

    f.write("const std::vector<std::vector<AssociativePair>> &get_i32_ops_table(const vector<Expr> &exprs) {\n")
    #f.write(tab + "internal_assert(!exprs.empty() && exprs.size() <= 2);\n")
    #f.write(tab + "internal_assert(exprs[0].type() == Int(32));\n")
    f.write("\n")
    f.write(tab + "static std::vector<std::vector<AssociativePair>> empty;\n")
    f.write(tab + "if (exprs[0].as<Add>()) {\n")
    f.write(tab + tab + "debug(5) << \"Returning add root table\\n\";\n")
    f.write(tab + tab + "if (exprs.size() == 1) {\n")
    f.write(tab + tab + tab + "return get_single_i32_ops_table_add();\n")
    f.write(tab + tab + "} else {\n")
    f.write(tab + tab + tab + "return get_double_i32_ops_table_add();\n")
    f.write(tab + tab + "}\n")
    f.write(tab + "} else if (exprs[0].as<Sub>()) {\n")
    f.write(tab + tab + "debug(5) << \"Returning sub root table\\n\";\n")
    f.write(tab + tab + "if (exprs.size() == 1) {\n")
    f.write(tab + tab + tab + "return get_single_i32_ops_table_sub();\n")
    f.write(tab + tab + "} else {\n")
    f.write(tab + tab + tab + "return get_double_i32_ops_table_sub();\n")
    f.write(tab + tab + "}\n")
    f.write(tab + "} else if (exprs[0].as<Mul>()) {\n")
    f.write(tab + tab + "debug(5) << \"Returning mul root table\\n\";\n")
    f.write(tab + tab + "if (exprs.size() == 1) {\n")
    f.write(tab + tab + tab + "return get_single_i32_ops_table_mul();\n")
    f.write(tab + tab + "} else {\n")
    f.write(tab + tab + tab + "return get_double_i32_ops_table_mul();\n")
    f.write(tab + tab + "}\n")
    f.write(tab + "} else if (exprs[0].as<Min>()) {\n")
    f.write(tab + tab + "debug(5) << \"Returning min root table\\n\";\n")
    f.write(tab + tab + "if (exprs.size() == 1) {\n")
    f.write(tab + tab + tab + "return get_single_i32_ops_table_min();\n")
    f.write(tab + tab + "} else {\n")
    f.write(tab + tab + tab + "return get_double_i32_ops_table_min();\n")
    f.write(tab + tab + "}\n")
    f.write(tab + "} else if (exprs[0].as<Max>()) {\n")
    f.write(tab + tab + "debug(5) << \"Returning max root table\\n\";\n")
    f.write(tab + tab + "if (exprs.size() == 1) {\n")
    f.write(tab + tab + tab + "return get_single_i32_ops_table_max();\n")
    f.write(tab + tab + "} else {\n")
    f.write(tab + tab + tab + "return get_double_i32_ops_table_max();\n")
    f.write(tab + tab + "}\n")
    f.write(tab + "}\n")
    f.write(tab + "debug(5) << \"Returning empty table\\n\";\n")
    f.write(tab + "return empty;\n")
    f.write("}\n")

    f.write("\n}\n}\n\n");

    f.write("using namespace Halide;\n")
    f.write("using namespace Halide::Internal;\n\n")
    f.write("int main() {\n");

    f.write(tab + "Expr x = Variable::make(Int(32), \"x\");\n")
    f.write(tab + "Expr y = Variable::make(Int(32), \"y\");\n")
    f.write(tab + "Expr expr = Min::make(x, y);\n")
    f.write(tab + "const auto &table = get_i32_ops_table({expr});\n")
    f.write(tab + "std::cout << \"Op: \" << table[0][0].op << \" with id: \" << table[0][0].identity << \"\\n\";\n")
    f.write(tab + "return 0;\n")
    f.write("}\n\n")


