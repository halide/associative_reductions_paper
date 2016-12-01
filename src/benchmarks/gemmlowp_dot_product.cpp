#include <iostream>
#include <vector>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <eight_bit_int_gemm/eight_bit_int_gemm.h>
#include "benchmark.h"

//g++ --std=c++11 -o dot_product dot_product.cpp -I/usr/local/opt/openblas/include -L/usr/local/opt/openblas/lib -lopenblas -lpthread

//g++ --std=c++11 -o gemmlowp_dot_product gemmlowp_dot_product.cpp /usr/local/google/home/psuriana/gemmlowp/eight_bit_int_gemm/eight_bit_int_gemm.cc -I/usr/local/google/home/psuriana/gemmlowp -lpthread

#define N1 4
#define N2 4
const int size = 1024 * 1024 * N1 * N2;
const int size = 5;
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

    std::vector<uint8_t> vec_A(size);
    std::vector<uint8_t> vec_B(size);
    std::vector<uint8_t> vec_C(1);

    // init randomly
    for (int ix = 0; ix < size; ix++) {
        vec_A[ix] = (rand() & 0xff);
        vec_B[ix] = (rand() & 0xff);
    }

    std::cout << "Done initializing\n";

    std::cout << "Start benchmarking...\n";
    gemmlowp::eight_bit_int_gemm::SetMaxNumThreads(24);

    double t = benchmark(trials, iterations, [&]() {
        gemmlowp::eight_bit_int_gemm::EightBitIntGemm(
            false, false, false, 1, 1, size,
            &(vec_A[0]), 0, 1, &(vec_B[0]), 0, size,
            &(vec_C[0]), 0, 1, 0, size,
            gemmlowp::eight_bit_int_gemm::BitDepthSetting::A8B8);
    });

    float gbits = 8 * size * (2.0 / 1e9); // bits per seconds
    printf("Dot-product gemmlowp: %fms, %f Gbps\n", t * 1e3, (gbits / t));
}
