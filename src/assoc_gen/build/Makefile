CXX ?= g++
CXX_WARNING_FLAGS = -Wall -Werror -Wno-unused-function -Wcast-qual -Wignored-qualifiers -Wno-comment -Wsign-compare -Wno-unused-value
CXX_FLAGS = $(CXX_WARNING_FLAGS) -fno-rtti
ROOT_DIR = /usr/local/google/home/psuriana/assoc_gen
HALIDE_DIR = /usr/local/google/home/psuriana/Halide

gen: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/Generator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o gen Generator.o HalideToZ3.o AssociativityProver.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

old_gen: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/OldGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o old_gen OldGenerator.o HalideToZ3.o AssociativityProver.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

tuple_gen: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/TupleGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o tuple_gen TupleGenerator.o HalideToZ3.o AssociativityProver.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

old_tuple_gen: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/OldTupleGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o old_tuple_gen OldTupleGenerator.o HalideToZ3.o AssociativityProver.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

four: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/FourGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o four FourGenerator.o HalideToZ3.o AssociativityProver.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

HalideToZ3:
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/HalideToZ3.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	#g++ -o test HalideToZ3.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

AssociativityProver: HalideToZ3
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/AssociativityProver.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src

test: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/test/test.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o test test.o HalideToZ3.o AssociativityProver.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

table: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/AssociativeOpsTable.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o table AssociativeOpsTable.o HalideToZ3.o AssociativityProver.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

run_test: HalideToZ3 AssociativityProver test
	./test

run_gen: HalideToZ3 AssociativityProver gen
	./gen

run_old_gen: HalideToZ3 AssociativityProver old_gen
	./old_gen

run_old_tuple: HalideToZ3 AssociativityProver old_tuple_gen
	./old_tuple_gen

run_tuple: HalideToZ3 AssociativityProver tuple_gen
	./tuple_gen

gen_assoc:
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/gen_assoc.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o gen_assoc gen_assoc.o

run_assoc: gen_assoc
	./gen_assoc

run_four : four
	./four

run_table : table
	./table

clean:
	rm *.o test gen gen_assoc tuple_gen four table