/* domfilter: read graph6 lines (n<=31) on stdin; for each graph compute
   exact domination number gamma and, when edges > m(n,gamma) (intended
   Koch-Narayan formula), count ALL gamma-sized dominating sets.
   Print any graph that satisfies the conjecture's hypotheses
   (bipartite assumed from geng -b, no isolated assumed from -d1,
   gamma>=2, n>=3*gamma, unique min dominating set) yet exceeds m(n,gamma).
   Also track per-(n,gamma) the max edges seen among unique-UMD graphs
   if TRACK_MAX is set via -t flag (then it counts dom sets whenever gamma>=2
   and n>=3gamma — slower).
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n;
static unsigned int nbhd[32];   /* closed neighborhoods */
static unsigned int FULL;

static int mformula(int nn, int g) {
    int cg = (g + 1) / 2, fg = g / 2;
    int base = 2 * g + 2 * cg * fg;
    int cap = 2 * cg - fg + 1;
    int k = nn - 3 * g; if (k > cap) k = cap;
    int mid = k * (2 * cg + 1);
    int phi = nn - 3 * g - cap; if (phi < 0) phi = 0;
    int tail = 0, i;
    for (i = 1; i <= phi; i++) tail += (2 * cg + 1) + (i + 1) / 2;
    return base + mid + tail;
}

/* count dominating sets of size k; early exit if count exceeds limit */
static long countdom(int k, int limit) {
    int idx[16];
    long cnt = 0;
    int i;
    if (k > n) return 0;
    for (i = 0; i < k; i++) idx[i] = i;
    for (;;) {
        unsigned int m = 0;
        for (i = 0; i < k; i++) m |= nbhd[idx[i]];
        if (m == FULL) { if (++cnt > limit) return cnt; }
        /* next combination */
        for (i = k - 1; i >= 0 && idx[i] == n - k + i; i--);
        if (i < 0) break;
        idx[i]++;
        for (i++; i < k; i++) idx[i] = idx[i - 1] + 1;
    }
    return cnt;
}

int main(int argc, char **argv) {
    char line[256];
    long total = 0, checked = 0;
    (void)argc; (void)argv;
    while (fgets(line, sizeof line, stdin)) {
        int len = (int)strlen(line);
        while (len && (line[len-1] == '\n' || line[len-1] == '\r')) line[--len] = 0;
        if (!len) continue;
        total++;
        /* decode graph6 */
        const char *p = line;
        n = *p++ - 63;
        if (n < 1 || n > 31) { fprintf(stderr, "bad n in %s\n", line); exit(1); }
        FULL = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
        unsigned int adj[32];
        memset(adj, 0, sizeof adj);
        int i, j, edges = 0, bitpos = 0;
        int val = 0;
        for (j = 1; j < n; j++) {
            for (i = 0; i < j; i++) {
                if (bitpos % 6 == 0) val = *p++ - 63;
                int bit = (val >> (5 - (bitpos % 6))) & 1;
                bitpos++;
                if (bit) { adj[i] |= 1u << j; adj[j] |= 1u << i; edges++; }
            }
        }
        for (i = 0; i < n; i++) nbhd[i] = adj[i] | (1u << i);
        /* gamma by existence */
        int gamma = 0, k;
        for (k = 1; k <= n; k++) {
            if (countdom(k, 0) > 0) { gamma = k; break; }
        }
        if (gamma < 2) continue;
        if (n < 3 * gamma) continue;
        int m = mformula(n, gamma);
        if (edges <= m) continue;
        checked++;
        long c = countdom(gamma, 1);
        if (c == 1) {
            printf("VIOLATION %s n=%d gamma=%d edges=%d m=%d\n", line, n, gamma, edges, m);
            fflush(stdout);
        }
    }
    fprintf(stderr, "processed %ld graphs, %ld exceeded m(n,gamma) pre-uniqueness\n",
            total, checked);
    return 0;
}
