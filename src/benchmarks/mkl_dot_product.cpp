#include <iostream>
#include <vector>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <mkl.h>
#include <mkl_cblas.h>
#include <mkl_blas.h>
#include <mkl_lapack.h>
#include <mkl_lapacke.h>

#include "benchmark.h"

//g++ --std=c++11 -o mkl_dot_product mkl_dot_product.cpp -I/opt/intel/mkl/include -L/opt/intel/mkl/lib/intel64 -lmkl_intel_lp64 -lmkl_intel_thread -lmkl_core -L/opt/intel/lib/intel64_lin -liomp5 -lpthread -ldl -lm
//LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:/opt/intel/lib/intel64_lin:$LD_LIBRARY_PATH OMP_NUM_THREADS=8 numactl --cpunodebind=1 ./mkl_dot_product

// dot product sdot
#define N1 4
#define N2 4
const int size = 1024 * 1024 * N1 * N2;
const int trials = 10;
const int iterations = 10;

/*
RDom r(0, size);
Func dot_ref("dot_ref");
dot_ref() = 0;
dot_ref() += cast<int>(A(r.x))*B(r.x);
*/

int main() {
	std::cout << "Input size: " << size << "\n";
	std::vector<float> vec_A(size);
    std::vector<float> vec_B(size);

    // init randomly
    for (int ix = 0; ix < size; ix++) {
        vec_A[ix] = (rand() & 0xffff);
        vec_B[ix] = (rand() & 0xffff);
        //std::cout << "i: " << ix << ", va: " << vec_A[ix] << ", vb: " << vec_B[ix] << "\n";
    }

    std::cout << "Done initializing\n";

    std::cout << "Start benchmarking...\n";
    double t = benchmark(trials, iterations, [&]() {
        cblas_sdot(size, &(vec_A[0]), 1, &(vec_B[0]), 1);
    });

    float gbits = 32 * size * (2.0 / 1e9); // bits per seconds
    printf("Dot-product mkl: %fms, %f Gbps\n", t * 1e3, (gbits / t));
}
