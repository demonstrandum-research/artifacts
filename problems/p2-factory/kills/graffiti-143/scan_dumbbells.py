#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Float-level exhaustive scan of the dumbbell family for Graffiti-143
violations: all dumbbell(t1,p,t2) with t1>=1, t2>=t1, p>=0, n=t1+t2+p <= 48.
Reports the best margin per order n under both "average distance" readings.
Float results guide which instances get exact certification (checker_g143.py);
they are not themselves certificates.
"""
import numpy as np
from itertools import combinations


def dumbbell(t1, p, t2):
    n = t1 + p + t2
    A = np.zeros((n, n), dtype=int)
    for i, j in combinations(range(t1), 2):
        A[i, j] = A[j, i] = 1
    for i, j in combinations(range(t1 + p, n), 2):
        A[i, j] = A[j, i] = 1
    chain = [0] + list(range(t1, t1 + p)) + [t1 + p]
    for a, b in zip(chain, chain[1:]):
        A[a, b] = A[b, a] = 1
    return A


def margins(A):
    n = len(A)
    m = int(A.sum()) // 2
    nbrs = [np.nonzero(A[i])[0] for i in range(n)]
    W = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        q = [s]
        while q:
            nq = []
            for u in q:
                for v in nbrs[u]:
                    if dist[v] < 0:
                        dist[v] = dist[u] + 1
                        nq.append(v)
            q = nq
        W += sum(dist)
    W //= 2
    ev = np.linalg.eigvalsh(A.astype(float))
    pos = ev[ev > 1e-9]
    var = pos.var()
    return var - m * n * n / (2 * W), var - m * n * (n - 1) / (2 * W)


def main():
    NMAX = 48
    best2, bestp = {}, {}
    for t1 in range(1, NMAX):
        for t2 in range(t1, NMAX):
            for p in range(0, NMAX):
                n = t1 + t2 + p
                if n > NMAX:
                    break
                if n < 3:
                    continue
                mg2, mgp = margins(dumbbell(t1, p, t2))
                spec = (t1, p, t2)
                if n not in best2 or mg2 > best2[n][0]:
                    best2[n] = (mg2, spec)
                if n not in bestp or mgp > bestp[n][0]:
                    bestp[n] = (mgp, spec)
    print("n   best margin_n2 (spec)         best margin_pairs (spec)")
    for n in sorted(best2):
        m2, s2 = best2[n]
        mp, sp = bestp[n]
        flag = (' <-- VIOLATES n2' if m2 > 0
                else (' <-- violates pairs' if mp > 0 else ''))
        print("%3d %+10.5f D%s   %+10.5f D%s%s" % (n, m2, s2, mp, sp, flag))


if __name__ == '__main__':
    main()
