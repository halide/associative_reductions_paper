CXX ?= g++
CXX_WARNING_FLAGS = -Wall -Werror -Wno-unused-function -Wcast-qual -Wignored-qualifiers -Wno-comment -Wsign-compare -Wno-unused-value
CXX_FLAGS = $(CXX_WARNING_FLAGS) -fno-rtti
ROOT_DIR =
HALIDE_DIR =

HalideToZ3:
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/HalideToZ3.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src

AssociativityProver: HalideToZ3
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/AssociativityProver.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src

Utilities: HalideToZ3 AssociativityProver
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/Utilities.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src

gen: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/Generator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o gen Generator.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

select_gen: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/SelectGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o select_gen SelectGenerator.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

tuple_gen: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/TupleGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o tuple_gen TupleGenerator.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

select_tuple_gen: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/SelectTupleGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o select_tuple_gen SelectTupleGenerator.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

select_old_tuple_gen: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/SelectOldTupleGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o select_old_tuple_gen SelectOldTupleGenerator.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

four: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/FourGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o four FourGenerator.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

three: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/ThreeGenerator.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o three ThreeGenerator.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

test: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/test/test.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o test test.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

table: HalideToZ3 AssociativityProver Utilities
	$(CXX) $(CXX_FLAGS) -std=c++11 -c $(ROOT_DIR)/src/AssociativeOpsTable.cpp -I$(HALIDE_DIR)/include -I$(ROOT_DIR)/src
	$(CXX) $(CXX_FLAGS) -o table AssociativeOpsTable.o HalideToZ3.o AssociativityProver.o Utilities.o -lz3 -L$(HALIDE_DIR)/lib -lHalide -ldl -lpthread -lz

run_test: HalideToZ3 AssociativityProver test
	./test

run_table : table
	./table

run_gen: HalideToZ3 AssociativityProver gen
	./gen

run_select_gen: HalideToZ3 AssociativityProver select_gen
	./select_gen

run_tuple: HalideToZ3 AssociativityProver tuple_gen
	./tuple_gen

run_select_tuple: HalideToZ3 AssociativityProver select_tuple_gen
	./select_tuple_gen

run_select_old_tuple: HalideToZ3 AssociativityProver select_old_tuple_gen
	./select_old_tuple_gen

run_three : three
	./three

run_four : four
	./four

clean:
	rm *.o test table gen select_gen tuple_gen select_tuple_gen three four