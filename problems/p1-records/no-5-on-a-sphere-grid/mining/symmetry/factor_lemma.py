#!/usr/bin/env python3
"""Factorization lemmas for symmetric 5-subsets + compatibility-density
comparison between the admissible symmetry types (-I, rot180, S4).

LEMMA A (central inversion, type (2,2,1)). For pairs +-u_a, +-u_b (centered
coords) and any 5th point w:
    det5(u_a, -u_a, u_b, -u_b, w) = 4 * (|u_a|^2 - |u_b|^2) * det[u_a, u_b, w]
  (up to a fixed sign from row order). Hence the ENTIRE (2,2,1) family of
  conditions is equivalent to: all pair-norms distinct (L1) AND no third set
  point on the central plane of any two pairs (L3, with L2 as degenerate case).
  In particular the condition is independent of the SIGN of w: the halving.

LEMMA B (rot180 about z, type (2,2,1)). For pairs a,sa and b,sb with
  s(x,y,z)=(-x,-y,z), and 5th point w:
    det5 = 4 * (a x b)_z * det[[a_z,|a|^2,1],[b_z,|b|^2,1],[w_z,|w|^2,1]]
  First factor: xy-projections of a,b not parallel. Second: the (z, r^2)
  profiles of a,b,w not collinear (a,b,w not on a common sphere of revolution
  about the axis... the z-w-profile line).

DENSITY: fraction of random orbit-pairs (and orbit-pair+point triples) that
are degenerate, per symmetry type, in the 13-grid. Lower degeneracy density =
more usable orbit combinations = empirical advantage.
"""
import os, sys, random
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np
import json

rng = random.Random(123)

def det5_rows(rows):
    """exact det of 5x5 [x,y,z,w,1] via symlib's 4x4-diff formula."""
    L = np.array(rows, dtype=np.int64)
    idx = np.array([[0, 1, 2, 3, 4]])
    return int(sl.det5_batch(L[:, :4], idx)[0])

def lift_c(u):
    return (u[0], u[1], u[2], u[0]**2 + u[1]**2 + u[2]**2, 1)

def det3(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0])
          + a[2]*(b[0]*c[1]-b[1]*c[0]))

# ---------------- Lemma A exact check
okA = 0; trials = 2000
for _ in range(trials):
    ua = tuple(rng.randrange(-6, 7) for _ in range(3))
    ub = tuple(rng.randrange(-6, 7) for _ in range(3))
    w = tuple(rng.randrange(-6, 7) for _ in range(3))
    lhs = det5_rows([lift_c(ua), lift_c(tuple(-c for c in ua)),
                     lift_c(ub), lift_c(tuple(-c for c in ub)), lift_c(w)])
    A = sum(c*c for c in ua); B = sum(c*c for c in ub)
    rhs = 4 * (A - B) * det3(ua, ub, w)
    if lhs == rhs or lhs == -rhs:
        okA += 1
print(f"Lemma A: |det5| == |4(A-B)det[ua,ub,w]| in {okA}/{trials} random checks")

# ---------------- Lemma B exact check
okB = 0
for _ in range(trials):
    a = tuple(rng.randrange(-6, 7) for _ in range(3))
    b = tuple(rng.randrange(-6, 7) for _ in range(3))
    w = tuple(rng.randrange(-6, 7) for _ in range(3))
    sa = (-a[0], -a[1], a[2]); sb = (-b[0], -b[1], b[2])
    lhs = det5_rows([lift_c(a), lift_c(sa), lift_c(b), lift_c(sb), lift_c(w)])
    cz = a[0]*b[1] - a[1]*b[0]
    A = sum(c*c for c in a); B = sum(c*c for c in b); W = sum(c*c for c in w)
    prof = det3((a[2], A, 1), (b[2], B, 1), (w[2], W, 1))
    rhs = 4 * cz * prof
    if lhs == rhs or lhs == -rhs:
        okB += 1
print(f"Lemma B: |det5| == |4 (axb)_z * profile-det| in {okB}/{trials} random checks")

# ---------------- degeneracy densities in the 13-grid (centered, exclude fixed pts)
def rand_u():
    while True:
        u = tuple(rng.randrange(-6, 7) for _ in range(3))
        if u != (0, 0, 0):
            return u

N = 200000
out = {}

# -I: quad blocked iff |ua|=|ub| (rectangle) or parallel; (2,2,1) zero iff that or det3=0
bad_quad = bad_221 = 0
for _ in range(N):
    ua, ub, w = rand_u(), rand_u(), rand_u()
    A = sum(c*c for c in ua); B = sum(c*c for c in ub)
    cx = (ua[1]*ub[2]-ua[2]*ub[1], ua[2]*ub[0]-ua[0]*ub[2], ua[0]*ub[1]-ua[1]*ub[0])
    q = (A == B) or cx == (0, 0, 0)
    bad_quad += q
    bad_221 += q or (det3(ua, ub, w) == 0)
out["negI"] = {"quad_blocked": bad_quad / N, "cond221_zero": bad_221 / N}

# rot180z: orbit pairs need z-axis-free points (x,y) != 0
def rand_a_rot():
    while True:
        a = tuple(rng.randrange(-6, 7) for _ in range(3))
        if (a[0], a[1]) != (0, 0):
            return a
bad_quad = bad_221 = 0
for _ in range(N):
    a, b, w = rand_a_rot(), rand_a_rot(), rand_u()
    cz = a[0]*b[1] - a[1]*b[0]
    A = sum(c*c for c in a); B = sum(c*c for c in b); W = sum(c*c for c in w)
    q = (cz == 0)
    bad_quad += q
    prof = det3((a[2], A, 1), (b[2], B, 1), (w[2], W, 1))
    bad_221 += q or (prof == 0)
out["rot180z"] = {"quad_blocked": bad_quad / N, "cond221_zero": bad_221 / N}

# S4z: orbit {p, gp, g2p, g3p}, g(x,y,z)=(y,-x,-z); orbit is a blocked quad iff
# lifted rank <=2; estimate fraction + fraction of (orbit, extra point) 5-subsets zero
def g_s4(p):
    return (p[1], -p[0], -p[2])
bad_orbit = bad_o1 = 0
M = 50000
for _ in range(M):
    p = rand_u()
    o = [p, g_s4(p), g_s4(g_s4(p)), g_s4(g_s4(g_s4(p)))]
    if len(set(o)) != 4:
        continue
    L = [lift_c(q) for q in o]
    # rank of diffs <= 2 iff all 4x4 dets with any 5th pt zero; test with 3 probes
    w = rand_u()
    d = det5_rows(L + [lift_c(w)])
    d2 = det5_rows(L + [lift_c(rand_u())])
    if d == 0 and d2 == 0:
        bad_orbit += 1
    if d == 0:
        bad_o1 += 1
out["S4z"] = {"orbit_blocked_est": bad_orbit / M, "orbit_plus_point_zero": bad_o1 / M}

print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "factor_lemma.json"), "w"), indent=1)
print("written factor_lemma.json")
