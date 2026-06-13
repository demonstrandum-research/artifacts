/* rederive_filter.c
 *
 * INDEPENDENT re-derivation filter for IRIS Conjecture 6.1 (NuevaMirada),
 * Davila-De Loera-Eddy-Fang-Lu-Yang, ICML 2025 AI4Math workshop
 * (OpenReview v6Ulp3U1ZT).  Written from scratch on 2026-06-11 without
 * consulting problems/p0-iris/code/iris_filter.c or run_iris.sh.
 *
 * Conjecture: if P is a simple 3-polytope with face vector (p3,...,pm)
 * and S := sum_{k>=7} pk >= 3, then
 *      p6 >= 39/20 + p3/2 - p5/4 - S.
 * Integer violation test (p6 integral):
 *      20*p6 < 39 + 10*p3 - 5*p5 - 20*S.
 *
 * Input: plantri -a (ascii) output on stdin.  Each line:
 *      "<n> <list_1>,<list_2>,...,<list_n>"
 * where <list_i> is the rotation (adjacency) list of vertex i of a simple
 * planar TRIANGULATION T, vertices named 'a','b',... (n <= 26 assumed).
 *
 * Dual-degree equivalence: the polytope graph G is the planar dual of T;
 * the k-gonal faces of G correspond exactly to the degree-k vertices of T.
 * Hence pk = #{vertices of T with degree k}, and deg(v) = length of v's
 * adjacency list.  (This equivalence is verified independently by explicit
 * dual construction in verify_dual.py.)
 *
 * Output: violating input lines are echoed to stdout; a summary line
 *      "SUMMARY total=<T> Sge3=<A> violations=<V>"
 * is written to stderr at EOF.
 */

#include <stdio.h>
#include <string.h>

#define MAXLINE 4096
#define MAXDEG  64

int main(void)
{
    char line[MAXLINE];
    long long total = 0, sge3 = 0, viol = 0;

    while (fgets(line, sizeof line, stdin) != NULL) {
        /* skip leading vertex count */
        char *p = line;
        while (*p == ' ') p++;
        if (*p < '0' || *p > '9') continue;   /* not a graph line */
        while (*p >= '0' && *p <= '9') p++;
        if (*p != ' ') continue;
        p++;

        total++;

        /* degree histogram: deg of vertex = length of its letter-run */
        long long cnt[MAXDEG + 1];
        memset(cnt, 0, sizeof cnt);
        int d = 0;
        for (;; p++) {
            if (*p >= 'a' && *p <= 'z') {
                d++;
            } else {                      /* ',', '\n', '\r', or '\0' */
                if (d > 0) {
                    if (d > MAXDEG) d = MAXDEG;
                    cnt[d]++;
                    d = 0;
                }
                if (*p == ',' ) continue;
                break;                    /* end of adjacency section */
            }
        }

        long long p3 = cnt[3], p5 = cnt[5], p6 = cnt[6];
        long long S = 0;
        for (int k = 7; k <= MAXDEG; k++) S += cnt[k];

        if (S >= 3) {
            sge3++;
            if (20 * p6 < 39 + 10 * p3 - 5 * p5 - 20 * S) {
                viol++;
                fputs(line, stdout);
            }
        }
    }

    fprintf(stderr, "SUMMARY total=%lld Sge3=%lld violations=%lld\n",
            total, sge3, viol);
    return 0;
}
