#include <iostream>
#include <cstdlib>
#include <cassert>
#include <cmath>
#include <vector>
#include <map>
#include <stdint.h>
#include <chrono>
#include <thread>

using std::vector;

namespace {

typedef int Value;

typedef enum {
    X = 0,
    Y,
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
    uint64_t val = 0;

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
    int size = 0;
    bool fail = false;
    bool uses_x = false, uses_y = false;

    void create(DecisionSource &dec, int leaves) {
        assert(size < 64);
        assert(leaves > 0);
        if (leaves == 1) {
            /*if (size > 1 && nodes[size-1] == X &&
                (nodes[size-2] == Min ||
                 nodes[size-2] == Max ||
                 nodes[size-2] == Add ||
                 nodes[size-2] == Sub)) {
                // avoid op(x, x)
                uses_y = true;
                nodes[size++] = Y;
            } else if (size > 1 && nodes[size-1] == Y &&
                       (nodes[size-2] == Min ||
                        nodes[size-2] == Max ||
                        nodes[size-2] == Add ||
                        nodes[size-2] == Sub)) {
                // avoid op(y, y)
                uses_x = true;
                nodes[size++] = X;
            } else if (dec.get(2)) {
                uses_x = true;
                nodes[size++] = X;
            } else {
                uses_y = true;
                nodes[size++] = Y;
            }*/

            if (dec.get(2)) {
                uses_x = true;
                nodes[size++] = X;
            } else {
                uses_y = true;
                nodes[size++] = Y;
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
                assert(false);
            }
        }
    }

    void print_term(int &cursor) {
        switch(nodes[cursor++]) {
        case X:
            std::cout << "X";
            break;
        case Y:
            std::cout << "Y";
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

    void print() {
        int cursor = 0;
        print_term(cursor);
        std::cout << "\n";
    }
};

}

// Compute the possible max number of children within a leave level
uint64_t compute_max_num_children(const vector<uint64_t> &prev, int level) {
    assert(level > 0);
    if (prev.size() >= level) {
        return prev[level];
    }
    return 0;
}

/*int main(int argc, char **argv) {
    const int SLEEP_TIME = 50;
    uint64_t fails = 0;
    int leaves = 1;
    int max_num_children = 2;

    vector<uint64_t> max_num_children = {0, 2, 20, 200, 4000, 40005, 600010, 12000010, 160000110};

    for (uint64_t i = 0;; i++) {
        if ((i & 0xffffffff) == 0) {
            std::cout << i << ", " << fails << "\n";
            std::cout.flush();
        }
        if (i >= max_num_children) {
            leaves++;
            i = 0;
            std::cout << "\n******************************************************************\n";
            std::cout << "Leaves: " << leaves << "\n";
            std::cout.flush();
        }

        Expr e;
        DecisionSource dec;
        dec.val = i;
        e.create(dec, leaves);

        std::cout << i << ": ";
        e.print();
        std::this_thread::sleep_for(std::chrono::milliseconds(SLEEP_TIME));

        if (e.fail || !e.uses_x || !e.uses_y) {
            fails++;
            continue;
        }

        if (leaves == 5) {
            return 0;
        }
    }
    return 0;
}*/

int main(int argc, char **argv) {
    const int SLEEP_TIME = 50;
    uint64_t fails = 0;
    int leaves = 4;
    for (uint64_t i = 0;; i++) {
        if ((i & 0xffffffff) == 0) {
            std::cout << i << ", " << fails << "\n";
            std::cout.flush();
        }
        Expr e;
        DecisionSource dec;
        dec.val = i;
        e.create(dec, leaves);

        while (dec.val) {
            leaves++;
            std::cout << "\n******************************************************************\n";
            std::cout << "Leaves: " << leaves << " -> " << i << "\n";
            i = 0;
            std::cout.flush();
            dec.val = i;
            e = Expr();
            e.create(dec, leaves);
        }

        std::cout << i << ": ";
        e.print();
        std::this_thread::sleep_for(std::chrono::milliseconds(SLEEP_TIME));

        if (e.fail || !e.uses_x || !e.uses_y) {
            fails++;
            continue;
        }

        if (leaves == 5) {
            return 0;
        }
    }
    return 0;
}