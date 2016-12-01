#include <iostream>
#include <vector>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <boost/simd/function/dot.hpp>
#include <boost/simd/pack.hpp>

#include "benchmark.h"

//g++ boost_simd_dot_product.cpp -o boost_simd_dot_product -std=c++11 -O3 -msse4.2 -I/Users/psuriana/boost/include/ -I/Users/psuriana/boost/simd/include/

//g++ boost_simd_dot_product.cpp -o boost_simd_dot_product -std=c++11 -O3 -msse4.2 -I/usr/local/google/home/psuriana/boost/boost_1_62_0 -I/usr/local/google/home/psuriana/boost/simd/include/ -L/usr/local/google/home/psuriana/boost/boost_1_62_0/stage/lib

namespace bs = boost::simd;

#define N1 4
#define N2 4
const int size = 1024 * 1024 * N1 * N2;
const int trials = 1;
const int iterations = 1;

/*
RDom r(0, size);
Func dot_ref("dot_ref");
dot_ref() = 0;
dot_ref() += cast<int>(A(r.x))*B(r.x);
*/

int main() {
	std::cout << "Input size: " << size << "\n";
	bs::pack<float, size> vec_A;
    bs::pack<float, size> vec_B;

    // init randomly
    for (int ix = 0; ix < size; ix++) {
        vec_A[ix] = (rand() & 0xffff);
        vec_B[ix] = (rand() & 0xffff);
    }

    std::cout << "Done initializing\n";

    std::cout << "Start benchmarking...\n";
    double t = benchmark(trials, iterations, [&]() {
        bs::dot(vec_A, vec_B);
    });

    float gbits = 32 * size * (2.0 / 1e9); // bits per seconds
    printf("Dot-product cblas: %fms, %f Gbps\n", t * 1e3, (gbits / t));
}
