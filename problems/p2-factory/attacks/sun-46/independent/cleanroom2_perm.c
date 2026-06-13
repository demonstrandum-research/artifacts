/* cleanroom2_perm.c -- clean-room session 2026-06-12 (verifier agent).
 * Permanent of an m x m matrix over Z/qZ via Ryser's formula with Gray code,
 * OpenMP-parallelized over contiguous Gray-code ranges.
 * Written from scratch; not derived from ryser_mod.c or perm_modq.c.
 *
 * Input (text file given as argv[1]):  m  q  then m*m entries (row major, in [0,q)).
 * Output: single line "PER <value>".
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <omp.h>

static uint64_t Q;
static inline uint64_t mulmod(uint64_t a, uint64_t b) {
    return (uint64_t)((__uint128_t)a * b % Q);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s jobfile\n", argv[0]); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    int m;
    unsigned long long qq;
    if (fscanf(f, "%d %llu", &m, &qq) != 2) { fprintf(stderr, "bad header\n"); return 2; }
    Q = qq;
    if (m < 1 || m > 32) { fprintf(stderr, "bad m\n"); return 2; }
    uint64_t *A = malloc(sizeof(uint64_t) * m * m);
    for (int i = 0; i < m * m; i++) {
        unsigned long long x;
        if (fscanf(f, "%llu", &x) != 1) { fprintf(stderr, "bad entry\n"); return 2; }
        if (x >= Q) { fprintf(stderr, "entry out of range\n"); return 2; }
        A[i] = x;
    }
    fclose(f);

    const uint64_t NSUB = 1ULL << m;   /* iterate g = 1 .. NSUB-1 */
    uint64_t total = 0;                /* sum mod Q, sign-folded; folded modularly
                                          under a critical section (a plain OpenMP
                                          + reduction could overflow uint64)      */
    int nthreads = omp_get_max_threads();
    int nchunk = nthreads * 8;

    #pragma omp parallel
    {
        uint64_t r[32];
        #pragma omp for schedule(dynamic, 1)
        for (int c = 0; c < nchunk; c++) {
            uint64_t lo = 1 + (NSUB - 1) * (uint64_t)c / nchunk;
            uint64_t hi = 1 + (NSUB - 1) * (uint64_t)(c + 1) / nchunk;
            if (lo >= hi) continue;
            uint64_t prev = (lo - 1) ^ ((lo - 1) >> 1);   /* gray(lo-1) */
            int cnt = __builtin_popcountll(prev);
            for (int i = 0; i < m; i++) r[i] = 0;
            for (int j = 0; j < m; j++)
                if (prev >> j & 1)
                    for (int i = 0; i < m; i++)
                        r[i] = (r[i] + A[i * m + j]) % Q;
            uint64_t sub = 0;
            for (uint64_t g = lo; g < hi; g++) {
                uint64_t gray = g ^ (g >> 1);
                uint64_t bit = gray ^ prev;
                int j = __builtin_ctzll(bit);
                if (gray & bit) {
                    cnt++;
                    for (int i = 0; i < m; i++) {
                        r[i] += A[i * m + j];
                        if (r[i] >= Q) r[i] -= Q;
                    }
                } else {
                    cnt--;
                    for (int i = 0; i < m; i++) {
                        r[i] = (r[i] >= A[i * m + j]) ? r[i] - A[i * m + j]
                                                      : r[i] + Q - A[i * m + j];
                    }
                }
                uint64_t pr = r[0];
                for (int i = 1; i < m; i++) pr = mulmod(pr, r[i]);
                /* sign (-1)^(m-cnt) */
                if ((m - cnt) & 1) pr = (pr == 0) ? 0 : Q - pr;
                sub += pr;
                if (sub >= Q) sub -= Q;
                prev = gray;
            }
            #pragma omp critical
            total = (total + sub) % Q;
        }
    }
    printf("PER %llu\n", (unsigned long long)(total % Q));
    free(A);
    return 0;
}
