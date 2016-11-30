#include <cblas.h>
#include <stdio.h>

//gcc -o dot_product dot_product.cpp -I/usr/local/opt/openblas/include -L/usr/local/opt/openblas/lib -lopenblas -lpthread

// dot product ssdot
#define N1 4
#define N2 4
const int size = 1024 * 1024 * N1 * N2;

/*
RDom r(0, size);
Func dot_ref("dot_ref");
dot_ref() = 0;
dot_ref() += cast<int>(A(r.x))*B(r.x);
*/

int main() {
    double A[6] = {1.0, 2.0, 1.0, -3.0, 4.0, -1.0};
    double B[6] = {1.0, 2.0, 1.0, -3.0, 4.0, -1.0};
    double C[9] = {0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5};
    cblas_dgemm(CblasColMajor, CblasNoTrans, CblasTrans, 3, 3, 2, 1, A, 3, B, 3, 2, C, 3);

    for(int i = 0; i < 9; i++) {
        printf("%lf ", C[i]);
    }
    printf("\n");
}
