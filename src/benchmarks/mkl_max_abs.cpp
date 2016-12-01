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

//g++ --std=c++11 -o mkl_max_abs mkl_max_abs.cpp -I/opt/intel/mkl/include -L/opt/intel/mkl/lib/intel64 -lmkl_intel_lp64 -lmkl_intel_thread -lmkl_core -L/opt/intel/lib/intel64_lin -liomp5 -lpthread -ldl -lm
//LD_LIBRARY_PATH=/opt/intel/mkl/lib/intel64:/opt/intel/lib/intel64_lin:$LD_LIBRARY_PATH OMP_NUM_THREADS=8 numactl --cpunodebind=0 ./mkl_max_abs

#define N1 4
#define N2 4
const int size = 1024 * 1024 * N1 * N2;
//const int size = 10;
const int trials = 10;
const int iterations = 10;

/*
RDom r(0, size);
max_ref() = 0.0f;
max_ref() = max(max_ref(), abs(A(r)));
*/

int main() {
    std::cout << "Input size: " << size << "\n";
    std::vector<float> vec(size);
    std::vector<float> vec_B(size);

    // init randomly
    for (int ix = 0; ix < size; ix++) {
        vec[ix] = rand();
        //std::cout << ix << ": " << "; v: " << vec[ix] << "\n";
    }

    std::cout << "Done initializing\n";

    //float result = LAPACKE_slange(LAPACK_ROW_MAJOR, 'm', 1, size, &(vec[0]), size);
    //float result = LAPACKE_slange(LAPACK_COL_MAJOR, 'm', size, 1, &(vec[0]), 1);
    //std::cout << "Result: " << result << "\n";

    std::cout << "Start benchmarking...\n";
    double t = benchmark(trials, iterations, [&]() {
        //LAPACKE_slange(LAPACK_ROW_MAJOR, 'm', 1, size, &(vec[0]), size);
        LAPACKE_slange(LAPACK_COL_MAJOR, 'm', size, 1, &(vec[0]), 1);
    });

    float gbits = 32 * size * (2.0 / 1e9); // bits per seconds
    printf("Max abs mkl: %fms, %f Gbps\n", t * 1e3, (gbits / t));
}
