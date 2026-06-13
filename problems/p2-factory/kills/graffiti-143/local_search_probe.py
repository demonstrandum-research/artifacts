#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Float-level local-search probe for Graffiti-143 violations OUTSIDE / below the
dumbbell family record sizes:
  * n <= 38 under the strict n^2 convention   (dumbbell record: n=39)
  * n <= 36 under the pairs convention        (dumbbell record: n=37)
Simulated annealing over edge flips, seeded from dumbbell-like graphs and
random graphs. Results are heuristic (float); any hit would be exact-verified
separately. Negative outcome = evidence, not proof.
"""
import numpy as np
from itertools import combinations
import random

rng = random.Random(143)


def margins(A, conv):
    n = len(A)
    m = int(A.sum()) // 2
    # BFS all-pairs
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
        if any(d < 0 for d in dist):
            return None
        W += sum(dist)
    W //= 2
    ev = np.linalg.eigvalsh(A.astype(float))
    pos = ev[ev > 1e-9]
    if len(pos) == 0:
        return None
    var = pos.var()
    if conv == "n2":
        return var - m * n * n / (2 * W)
    return var - m * n * (n - 1) / (2 * W)


def seed_graph(n):
    kind = rng.random()
    A = np.zeros((n, n), dtype=int)
    if kind < 0.5:
        # random dumbbell-ish split
        t1 = rng.randint(3, max(4, n // 3))
        p = rng.randint(6, min(16, n - t1 - 3))
        t2 = n - t1 - p
        if t2 < 3:
            t2 = 3
            p = n - t1 - t2
        for i, j in combinations(range(t1), 2):
            A[i, j] = A[j, i] = 1
        for i, j in combinations(range(t1 + p, n), 2):
            A[i, j] = A[j, i] = 1
        chain = [0] + list(range(t1, t1 + p)) + [t1 + p]
        for a, b in zip(chain, chain[1:]):
            A[a, b] = A[b, a] = 1
    else:
        # connected random graph
        order = list(range(n))
        rng.shuffle(order)
        for a, b in zip(order, order[1:]):
            A[a, b] = A[b, a] = 1
        for i, j in combinations(range(n), 2):
            if A[i, j] == 0 and rng.random() < 0.25:
                A[i, j] = A[j, i] = 1
    return A


def anneal(n, conv, iters=4000, T0=0.5):
    A = seed_graph(n)
    cur = margins(A, conv)
    while cur is None:
        A = seed_graph(n)
        cur = margins(A, conv)
    best = cur
    bestA = A.copy()
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-3
        i = rng.randrange(n)
        j = rng.randrange(n)
        if i == j:
            continue
        A[i, j] ^= 1
        A[j, i] ^= 1
        new = margins(A, conv)
        if new is not None and (new > cur or
                                rng.random() < np.exp((new - cur) / T)):
            cur = new
            if new > best:
                best = new
                bestA = A.copy()
        else:
            A[i, j] ^= 1
            A[j, i] ^= 1
    return best, bestA


def main():
    tasks = [("n2", 38), ("n2", 37), ("pairs", 36), ("pairs", 35)]
    RESTARTS = 24
    for conv, n in tasks:
        overall = -1e9
        bestA = None
        for r in range(RESTARTS):
            b, A = anneal(n, conv, iters=3000)
            if b > overall:
                overall = b
                bestA = A
        print("conv=%-5s n=%d best margin over %d anneals: %+.6f %s" % (
            conv, n, RESTARTS, overall,
            "*** VIOLATION ***" if overall > 0 else ""))
        if overall > 0:
            np.save("probe_hit_%s_n%d.npy" % (conv, n), bestA)
    print("probe done")


if __name__ == "__main__":
    main()
