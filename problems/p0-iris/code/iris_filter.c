/* PLUGIN for plantri: accept only triangulations whose DUAL simple
   3-polytope violates IRIS Conjecture 6.1 (NuevaMirada, ICML 2025 AI4MATH):
   hypothesis  S = sum_{k>=7} pk >= 3;
   violation   20*p6 < 39 + 10*p3 - 5*p5 - 20*S
   where pk = number of degree-k vertices of the triangulation
   (= number of k-gonal faces of the dual simple 3-polytope). */

#define FILTER iris_check

static unsigned long long iris_hyp = 0, iris_viol = 0;

static int
iris_check(int nbtot, int nbop, int doflip)
{
    int i, p3, p5, p6, S, d;

    p3 = p5 = p6 = S = 0;
    for (i = 0; i < nv; ++i)
    {
        d = degree[i];
        if (d == 3) ++p3;
        else if (d == 5) ++p5;
        else if (d == 6) ++p6;
        else if (d >= 7) ++S;
    }
    if (S < 3) return FALSE;            /* hypothesis fails */
    ++iris_hyp;
    if (20*p6 - 10*p3 + 5*p5 + 20*S <= 38)   /* strict violation of 6.1 */
    {
        ++iris_viol;
        fprintf(stderr, "VIOLATION p3=%d p5=%d p6=%d S=%d nv=%d\n",
                p3, p5, p6, S, nv);
        return TRUE;
    }
    return FALSE;
}

#define SUMMARY iris_summary
static void
iris_summary(void)
{
    fprintf(msgfile, "IRIS: hypothesis-met=%llu violations=%llu\n",
            iris_hyp, iris_viol);
}
