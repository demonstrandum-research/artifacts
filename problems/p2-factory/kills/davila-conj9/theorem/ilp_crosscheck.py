#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ilp_crosscheck.py -- optional CP-SAT cross-checks for induction-transfer.md.

1. gamma(G_k) by ILP for k = 2..KMAX_GAMMA: must equal floor(7k/3).
2. (optional, off by default) Z(G_k) by the fort-cover loop for k in Z_KS:
   must equal 3k+1. The loop is exact when it terminates: the hitting-set
   optimum over any subset of fort constraints is a lower bound on Z (every
   forcing set hits every fort), and when the optimum B actually forces,
   |B| >= Z, so |B| = Z.  NOTE: at k >= 6 (n >= 46) the naive loop converges
   far too slowly to be useful (observed: >2000 forts with LB still 3);
   use z_chrono_check.py for exact Z at those sizes instead.

Requires ortools. This is a validation aid, not part of the proof.
"""

import sys
import time
from ortools.sat.python import cp_model
from validate_induction import chain, masks, closure

KMAX_GAMMA = int(sys.argv[1]) if len(sys.argv) > 1 else 14
Z_KS = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else []


def gamma_ilp(n, nbr):
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f"x{v}") for v in range(n)]
    for v in range(n):
        model.AddBoolOr([x[v]] + [x[u] for u in range(n) if (nbr[v] >> u) & 1])
    model.Minimize(sum(x))
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 16
    status = solver.Solve(model)
    assert status == cp_model.OPTIMAL
    return int(solver.ObjectiveValue())


def z_fort_cover(n, nbr, verbose=True):
    full = (1 << n) - 1
    forts = []
    while True:
        model = cp_model.CpModel()
        x = [model.NewBoolVar(f"b{v}") for v in range(n)]
        for F in forts:
            model.AddBoolOr([x[v] for v in range(n) if (F >> v) & 1])
        model.Minimize(sum(x))
        solver = cp_model.CpSolver()
        solver.parameters.num_workers = 16
        status = solver.Solve(model)
        assert status == cp_model.OPTIMAL
        B = 0
        for v in range(n):
            if solver.Value(x[v]):
                B |= 1 << v
        cl = closure(n, nbr, B)
        if cl == full:
            return bin(B).count("1"), len(forts)
        F = full & ~cl
        assert F and (F & B) == 0
        # F must be a fort: no outside vertex has exactly one neighbor in F
        for v in range(n):
            if not (F >> v) & 1:
                inF = nbr[v] & F
                assert not (inF and (inF & (inF - 1)) == 0), "not a fort!"
        forts.append(F)
        if verbose and len(forts) % 50 == 0:
            print(f"    ... {len(forts)} forts, current LB "
                  f"{bin(B).count('1')}", flush=True)


def main():
    print("== gamma ILP cross-check ==", flush=True)
    ok = True
    for k in range(2, KMAX_GAMMA + 1):
        n, edges, _ = chain(k)
        g = gamma_ilp(n, masks(n, edges))
        tag = "OK " if g == 7 * k // 3 else "MISMATCH"
        if g != 7 * k // 3:
            ok = False
        print(f"  k={k:2d}  n={n:3d}  gamma_ILP={g:3d}  floor(7k/3)={7*k//3:3d}  {tag}",
              flush=True)
    print("== Z fort-cover cross-check ==", flush=True)
    for k in Z_KS:
        n, edges, _ = chain(k)
        t0 = time.time()
        z, nf = z_fort_cover(n, masks(n, edges))
        tag = "OK " if z == 3 * k + 1 else "MISMATCH"
        if z != 3 * k + 1:
            ok = False
        print(f"  k={k:2d}  n={n:3d}  Z_exact={z:3d}  3k+1={3*k+1:3d}  "
              f"({nf} forts, {time.time()-t0:.0f}s)  {tag}", flush=True)
    print("ALL OK" if ok else "MISMATCHES FOUND")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
