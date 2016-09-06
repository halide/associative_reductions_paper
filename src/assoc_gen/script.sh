g++ -std=c++11 -c ../src/gen_assoc.cpp; g++ -o gen_assoc gen_assoc.o -lz3; ./gen_assoc

g++ -fno-rtti -std=c++11 -c ../src/HalideToZ3.cpp -I/usr/local/google/home/psuriana/Halide/include -I/usr/local/google/home/psuriana/assoc_gen/src
g++ -o test HalideToZ3.o -lz3 -L/usr/local/google/home/psuriana/Halide/lib -lHalide -ldl -lpthread -lz

g++ -fno-rtti -std=c++11 -c ../test/test.cpp -I/usr/local/google/home/psuriana/Halide/include -I/usr/local/google/home/psuriana/assoc_gen/src
g++ -o test test.o HalideToZ3.o -lz3 -L/usr/local/google/home/psuriana/Halide/lib -lHalide -ldl -lpthread -lz

g++ -fno-rtti -std=c++11 -c ../src/FourGenerator.cpp -I/usr/local/google/home/psuriana/Halide/include -I/usr/local/google/home/psuriana/assoc_gen/src
g++ -o four FourGenerator.o HalideToZ3.o -lz3 -L/usr/local/google/home/psuriana/Halide/lib -lHalide -ldl -lpthread -lz

g++ -fno-rtti -std=c++11 -c ../src/FourGenerator.cpp -I/usr/local/google/home/psuriana/Halide/include -I/usr/local/google/home/psuriana/assoc_gen/src
g++ -o four FourGenerator.o HalideToZ3.o -lz3 -L/usr/local/google/home/psuriana/Halide/lib -lHalide -ldl -lpthread -lz

g++ -fno-rtti -std=c++11 -c ../src/AssociativeOpsTable.cpp -I/usr/local/google/home/psuriana/Halide/include -I/usr/local/google/home/psuriana/assoc_gen/src
g++ -o table AssociativeOpsTable.o HalideToZ3.o -lz3 -L/usr/local/google/home/psuriana/Halide/lib -lHalide -ldl -lpthread -lz


##### MAC

g++ -o test HalideToZ3.o -lz3 -L/Users/psuriana/Halide/lib -lHalide -ldl -lpthread -lz

g++ -fno-rtti -std=c++11 -c ../src/AssociativityProver.cpp -I/Users/psuriana/Halide/include -I/Users/psuriana/assoc_gen/src
g++ -fno-rtti -std=c++11 -c ../src/HalideToZ3.cpp -I/Users/psuriana/Halide/include -I/Users/psuriana/assoc_gen/src
g++ -fno-rtti -std=c++11 -c ../test/test.cpp -I/Users/psuriana/Halide/include -I/Users/psuriana/assoc_gen/src
g++ -o test test.o HalideToZ3.o AssociativityProver.o -lz3 -L/Users/psuriana/Halide/lib -lHalide -ldl -lpthread -lz
