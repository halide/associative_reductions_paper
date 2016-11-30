#include <boost/simd/pack.hpp>
#include <iostream>

//g++ argmax.cpp -std=c++11 -O3 -msse4.2 -I/Users/psuriana/boost/include/ -I/Users/psuriana/boost/simd/include/ -o argmax

namespace bs = boost::simd;

// argmin
const int size = 64;

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
    bs::pack<float,4> p{1.f,2.f,3.f,4.f};
    std::cout << p + 10*p << "\n";

    return 0;
}
