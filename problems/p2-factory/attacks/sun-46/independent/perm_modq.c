/* INDEPENDENT mod-q permanent for the sun-46 verification job.
 * Written from scratch (plain __uint128_t mulmod, no Montgomery; not derived
 * from the attack's ryser_mod.c).
 *
 * usage: perm_modq m q < matrix.txt
 *   stdin: m*m decimal residues (row major), 0 <= a_{jk} < q < 2^62.
 *   stdout: per(A) mod q in decimal.
 *
 * Ryser with Gray-code subset walk, block-partitioned across OpenMP threads:
 *   per(A) = (-1)^m * sum_{S != empty} (-1)^{|S|} prod_j sum_{k in S} A_{jk}.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <omp.h>

static uint64_t Q;

static inline uint64_t mulmod(uint64_t a, uint64_t b) {
    return (uint64_t)((unsigned __int128)a * b % Q);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: perm_modq m q\n"); return 2; }
    int m = atoi(argv[1]);
    Q = strtoull(argv[2], NULL, 10);
    if (m < 1 || m > 40) { fprintf(stderr, "bad m\n"); return 2; }
    uint64_t *A = malloc(sizeof(uint64_t) * m * m);
    for (int i = 0; i < m * m; i++)
        if (scanf("%llu", (unsigned long long *)&A[i]) != 1) {
            fprintf(stderr, "matrix read error\n"); return 2;
        }
    uint64_t total = 1ULL << m;
    uint64_t acc = 0;            /* sum over S of (-1)^{m-|S|} prod */
    #pragma omp parallel
    {
        int nt = omp_get_num_threads();
        int id = omp_get_thread_num();
        uint64_t lo = total / nt * id + (id < (int)(total % nt) ? id : total % nt);
        uint64_t cnt = total / nt + (id < (int)(total % nt) ? 1 : 0);
        uint64_t hi = lo + cnt;
        if (lo == 0) lo = 1;     /* S=empty gives zero product anyway */
        uint64_t *R = calloc(m, sizeof(uint64_t));
        uint64_t myacc = 0;
        if (lo < hi) {
            uint64_t S = lo ^ (lo >> 1);
            int pop = __builtin_popcountll(S);
            for (int c = 0; c < m; c++)
                if ((S >> c) & 1)
                    for (int j = 0; j < m; j++) {
                        R[j] += A[j * m + c];
                        if (R[j] >= Q) R[j] -= Q;
                    }
            for (uint64_t g = lo; g < hi; g++) {
                if (g != lo) {
                    int c = __builtin_ctzll(g);
                    uint64_t Sg = g ^ (g >> 1);
                    if ((Sg >> c) & 1) {
                        pop++;
                        for (int j = 0; j < m; j++) {
                            R[j] += A[j * m + c];
                            if (R[j] >= Q) R[j] -= Q;
                        }
                    } else {
                        pop--;
                        for (int j = 0; j < m; j++) {
                            R[j] += Q - A[j * m + c];
                            if (R[j] >= Q) R[j] -= Q;
                        }
                    }
                }
                uint64_t prod = R[0];
                for (int j = 1; j < m; j++) prod = mulmod(prod, R[j]);
                if ((m - pop) & 1) prod = (prod ? Q - prod : 0);
                myacc += prod;
                if (myacc >= Q) myacc -= Q;
            }
        }
        free(R);
        #pragma omp critical
        { acc += myacc; if (acc >= Q) acc -= Q; }
    }
    printf("%llu\n", (unsigned long long)acc);
    free(A);
    return 0;
}
