#include <iostream>
#include <vector>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <cblas.h>

#include "benchmark.h"

//g++ --std=c++11 -o openblas_dot_product openblas_dot_product.cpp -I/usr/local/opt/openblas/include -L/usr/local/opt/openblas/lib -lopenblas -lpthread

//g++ --std=c++11 -o openblas_dot_product openblas_dot_product.cpp -I/usr/local/google/home/psuriana/OpenBLAS/installed/include -L/usr/local/google/home/psuriana/OpenBLAS/installed/lib -lopenblas -lpthread -fopenmp

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
    }

    std::cout << "Done initializing\n";

    openblas_set_num_threads(8);
    std::cout << "Number of threads: " << openblas_get_num_threads() << "\n";
    std::cout << "Number of processors: " << openblas_get_num_procs() << "\n";
    std::cout << "Get parallel type: " << openblas_get_parallel() << "\n";

    std::cout << "Start benchmarking...\n";
    double t = benchmark(trials, iterations, [&]() {
        cblas_sdot(size, &(vec_A[0]), 1, &(vec_B[0]), 1);
    });

    float gbits = 32 * size * (2.0 / 1e9); // bits per seconds
    printf("Dot-product cblas: %fms, %f Gbps\n", t * 1e3, (gbits / t));
}
