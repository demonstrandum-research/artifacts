/* ref_perm_modq.c — hostile-referee independent permanent kernel (2026-06-12).
 *
 * Computes per(A) mod an odd prime q (q < 2^62) for an m x m matrix
 * (1 <= m <= 32) by Ryser's inclusion-exclusion formula with a Gray-code
 * subset walk, Montgomery modular arithmetic, OpenMP-parallel over
 * contiguous blocks of the subset enumeration.
 *
 * Written from scratch for the referee pass on papers/sun-46/note.tex;
 * shares no code with the kill bundle's kernels (ryser_mod.c, perm_modq.c,
 * cleanroom2_perm.c).
 *
 * usage: ref_perm_modq m q     (m*m entries, row-major, whitespace-separated,
 *                               on stdin; prints per(A) mod q)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <omp.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static u64 Q;        /* the modulus (odd, < 2^62)            */
static u64 NQINV;    /* -Q^{-1} mod 2^64                     */
static u64 R2;       /* 2^128 mod Q (to enter Montgomery)    */

static inline u64 redc(u128 t) {
    u64 f = (u64)t * NQINV;
    u128 s = t + (u128)f * Q;
    u64 r = (u64)(s >> 64);
    return (r >= Q) ? r - Q : r;
}
static inline u64 mmul(u64 a, u64 b) { return redc((u128)a * b); }
static inline u64 madd(u64 a, u64 b) { u64 s = a + b; return (s >= Q) ? s - Q : s; }
static inline u64 msub(u64 a, u64 b) { return (a >= b) ? a - b : a + Q - b; }

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: %s m q\n", argv[0]); return 2; }
    int m = atoi(argv[1]);
    Q = strtoull(argv[2], NULL, 10);
    if (m < 1 || m > 32 || !(Q & 1) || Q >> 62) {
        fprintf(stderr, "bad args (need 1<=m<=32, odd q < 2^62)\n"); return 2;
    }

    /* -Q^{-1} mod 2^64 by Newton iteration (Q odd) */
    u64 inv = Q;                     /* correct mod 2^3 */
    for (int i = 0; i < 6; i++) inv *= (u64)2 - Q * inv;
    NQINV = (u64)0 - inv;
    u64 r1 = (u64)(((u128)1 << 64) % Q);
    R2 = (u64)(((u128)r1 * r1) % Q);

    /* read matrix; store column-major in Montgomery form */
    u64 *col = malloc((size_t)m * m * sizeof(u64));
    for (int j = 0; j < m; j++)
        for (int k = 0; k < m; k++) {
            unsigned long long v;
            if (scanf("%llu", &v) != 1) { fprintf(stderr, "bad input\n"); return 2; }
            col[(size_t)k * m + j] = mmul((u64)(v % Q), R2);
        }

    const u64 NS = (u64)1 << m;          /* subsets 0 .. NS-1; we walk 1 .. NS-1 */
    int T = omp_get_max_threads();
    u64 *part = calloc((size_t)T, sizeof(u64));

#pragma omp parallel num_threads(T)
    {
        int t  = omp_get_thread_num();
        int nt = omp_get_num_threads();
        u64 lo = 1 + (NS - 1) * (u64)t / nt;
        u64 hi = 1 + (NS - 1) * (u64)(t + 1) / nt;
        if (lo < hi) {
            u64 r[32];
            for (int j = 0; j < m; j++) r[j] = 0;
            u64 g = lo ^ (lo >> 1);          /* Gray code of first index */
            int pc = 0;
            for (int k = 0; k < m; k++)
                if ((g >> k) & 1) {
                    const u64 *ck = col + (size_t)k * m;
                    for (int j = 0; j < m; j++) r[j] = madd(r[j], ck[j]);
                    pc++;
                }
            u64 acc = 0;
            for (u64 c = lo; c < hi; c++) {
                if (c != lo) {
                    u64 gn = c ^ (c >> 1);
                    u64 d  = gn ^ g;
                    int k  = __builtin_ctzll(d);
                    const u64 *ck = col + (size_t)k * m;
                    if (gn & d) { for (int j = 0; j < m; j++) r[j] = madd(r[j], ck[j]); pc++; }
                    else        { for (int j = 0; j < m; j++) r[j] = msub(r[j], ck[j]); pc--; }
                    g = gn;
                }
                u64 prod = r[0];
                for (int j = 1; j < m; j++) prod = mmul(prod, r[j]);
                if ((m - pc) & 1) acc = msub(acc, prod);   /* sign (-1)^(m-|S|) */
                else              acc = madd(acc, prod);
            }
            part[t] = acc;
        }
    }
    u64 total = 0;
    for (int t = 0; t < T; t++) total = madd(total, part[t]);
    total = redc((u128)total);            /* leave Montgomery domain */
    printf("%llu\n", (unsigned long long)total);
    return 0;
}
