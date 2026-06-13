#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
z_chrono_check.py -- exact Z(G_k) via the standard chronological CP-SAT model
(Brimkov-Fast-Hicks style), as an INDEPENDENT cross-check of Theorem A
(Z(G_k) = 3k+1). Advisory validation only; not part of the proof chain.

Model: s_v = 1 iff v initially blue; t_v in [0, n] = time v turns blue;
f_{u->v} = 1 iff u forces v.  Constraints:
  s_v = 1  ->  t_v = 0;     s_v = 0  ->  sum_{u in N(v)} f_{u->v} = 1
  f_{u->v} = 1 -> t_u <= t_v - 1  and  t_w <= t_v - 1 for all w in N(u)\{v}
minimize sum s_v.  Optimum = Z(G).

Usage: python z_chrono_check.py k [timelimit_s]
"""

import sys
import time
from ortools.sat.python import cp_model
from validate_induction import chain, masks, forcing_pattern, closure

k = int(sys.argv[1])
tl = float(sys.argv[2]) if len(sys.argv) > 2 else 1800.0

n, edges, blocks = chain(k)
nbr = masks(n, edges)
N = [[u for u in range(n) if (nbr[v] >> u) & 1] for v in range(n)]

model = cp_model.CpModel()
s = [model.NewBoolVar(f"s{v}") for v in range(n)]
t = [model.NewIntVar(0, n, f"t{v}") for v in range(n)]
f = {}
for v in range(n):
    for u in N[v]:
        f[(u, v)] = model.NewBoolVar(f"f{u}_{v}")

for v in range(n):
    model.Add(t[v] == 0).OnlyEnforceIf(s[v])
    model.Add(t[v] >= 1).OnlyEnforceIf(s[v].Not())
    model.Add(sum(f[(u, v)] for u in N[v]) == 1).OnlyEnforceIf(s[v].Not())
    model.Add(sum(f[(u, v)] for u in N[v]) == 0).OnlyEnforceIf(s[v])
for (u, v), fv in f.items():
    model.Add(t[u] <= t[v] - 1).OnlyEnforceIf(fv)
    for w in N[u]:
        if w != v:
            model.Add(t[w] <= t[v] - 1).OnlyEnforceIf(fv)

model.Minimize(sum(s))

# hint: the explicit witness S_k from the theorem (upper bound 3k+1)
_, _, S = forcing_pattern(k)
Sset = set(S)
for v in range(n):
    model.AddHint(s[v], 1 if v in Sset else 0)

solver = cp_model.CpSolver()
solver.parameters.num_workers = 32
solver.parameters.max_time_in_seconds = tl
t0 = time.time()
status = solver.Solve(model)
el = time.time() - t0
name = {cp_model.OPTIMAL: "OPTIMAL", cp_model.FEASIBLE: "FEASIBLE",
        cp_model.INFEASIBLE: "INFEASIBLE"}.get(status, str(status))
print(f"k={k} n={n}  status={name}  obj={solver.ObjectiveValue():.0f}  "
      f"bound={solver.BestObjectiveBound():.0f}  time={el:.0f}s")
if status == cp_model.OPTIMAL:
    z = int(solver.ObjectiveValue())
    wit = [v for v in range(n) if solver.Value(s[v])]
    okclo = closure(n, nbr, sum(1 << v for v in wit)) == (1 << n) - 1
    print(f"  Z(G_{k}) = {z}  (3k+1 = {3*k+1})  "
          f"{'OK' if z == 3*k+1 else 'MISMATCH'}; witness closure check: "
          f"{'forces' if okclo else 'DOES NOT FORCE (model bug!)'}")
    sys.exit(0 if z == 3 * k + 1 and okclo else 1)
sys.exit(2)
