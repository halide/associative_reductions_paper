CXX ?= g++
CXX_WARNING_FLAGS = -Wall -Werror -Wno-unused-function -Wcast-qual -Wignored-qualifiers -Wno-comment -Wsign-compare -Wno-unused-value
CXX_FLAGS = $(CXX_WARNING_FLAGS) -fno-rtti
MKL_DIR = /opt/intel/mkl
INTEL_DIR = /opt/intel

mkl_dot_product:
	$(CXX) $(CXX_FLAGS) --std=c++11 -o mkl_dot_product mkl_dot_product.cpp \
	-I$(MKL_DIR)/include \
	-L$(MKL_DIR)/lib/intel64 -lmkl_intel_lp64 -lmkl_intel_thread -lmkl_core \
	-L$(INTEL_DIR)/lib/intel64_lin -liomp5 -lpthread -ldl -lm

mkl_max_abs:
	$(CXX) $(CXX_FLAGS) --std=c++11 -o mkl_max_abs mkl_max_abs.cpp \
	-I$(MKL_DIR)/include \
	-L$(MKL_DIR)/lib/intel64 -lmkl_intel_lp64 -lmkl_intel_thread -lmkl_core \
	-L$(INTEL_DIR)/lib/intel64_lin -liomp5 -lpthread -ldl -lm

run_mkl_max_abs: mkl_max_abs
	LD_LIBRARY_PATH=$(MKL_DIR)/lib/intel64:$(INTEL_DIR)/lib/intel64_lin:$LD_LIBRARY_PATH \
	OMP_NUM_THREADS=8 numactl --cpunodebind=0 ./mkl_max_abs

run_mkl_dot_product: mkl_dot_product
	LD_LIBRARY_PATH=$(MKL_DIR)/lib/intel64:$(INTEL_DIR)/lib/intel64_lin:$LD_LIBRARY_PATH \
	OMP_NUM_THREADS=8 numactl --cpunodebind=0 ./mkl_dot_product

clean:
	rm mkl_dot_product mkl_max_abs