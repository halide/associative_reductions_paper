#include <iostream>
#include <vector>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <boost/simd/function/minimum.hpp>
#include <boost/simd/pack.hpp>

#include "benchmark.h"

//g++ argmin.cpp -o argmin -std=c++11 -O3 -msse4.2 -I/Users/psuriana/boost/include/ -I/Users/psuriana/boost/simd/include/

//g++ argmin.cpp -o argmin -std=c++11 -O3 -msse4.2 -I/usr/local/google/home/psuriana/boost/boost_1_62_0 -I/usr/local/google/home/psuriana/boost/simd/include/ -L/usr/local/google/home/psuriana/boost/boost_1_62_0/stage/lib

namespace bs = boost::simd;

// argmin
//const int size = 64;
const int size = 4;
const int trials = 10;
const int iterations = 10;

/*
RDom r(0, size, 0, size, 0, size, 0, size);
ref() = Tuple(255, 0, 0, 0, 0);
ref() = Tuple(min(ref()[0], input(r.x, r.y, r.y, r.z)),
              select(ref()[0] < input(r.x, r.y, r.y, r.z), ref()[1], r.x),
              select(ref()[0] < input(r.x, r.y, r.y, r.z), ref()[2], r.y),
              select(ref()[0] < input(r.x, r.y, r.z, r.w), ref()[3], r.z),
              select(ref()[0] < input(r.x, r.y, r.z, r.w), ref()[4], r.w));
*/

int main() {
    std::cout << "Input size: " << size << "\n";

    bs::pack<uint8_t, size*4> vec;

    // init randomly
    for (int iw = 0; iw < size; iw++) {
        for (int iz = 0; iz < size; iz++) {
            for (int iy = 0; iy < size; iy++) {
                for (int ix = 0; ix < size; ix++) {
                    int coordinate = ix + iy*4 + iz*16 + iw * 64;
                    vec[coordinate] = (rand() % 0xff);
                    /*std::cout << "(" << ix << ", " << iy << ", " << iz << ", "
                              << iw << "): " << (int)vec[coordinate] << "\n";*/
                }
            }
        }
    }

    std::cout << "Done initializing\n";

    uint8_t min_val = bs::minimum(vec);
    std::cout << "Min value: " << (int) min_val << "\n";

    std::cout << "Start benchmarking...\n";
    double t = benchmark(trials, iterations, [&]() {

    });

    float gbits = 8 * size / 1e9; // bits per seconds

    printf("Argmin with cblas: %fms, %f Gbps\n", t * 1e3, (gbits / t));

    return 0;
}
