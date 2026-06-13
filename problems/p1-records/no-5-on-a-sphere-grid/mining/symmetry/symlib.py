#!/usr/bin/env python3
"""Symmetry-mining library for the no-5-on-a-sphere grid problem (n=13).

Group: the 48 signed permutations (hyperoctahedral B3) acting about the cube
center c=(6,6,6): g(p) = M(p-c)+c. For odd n this is the full group of
similarity transformations of R^3 mapping {0..n-1}^3 onto itself, hence the
full symmetry group of the problem instance (spheres/planes are preserved
exactly by similarities).

All arithmetic exact (Python ints / int64 within proven overflow bounds:
|det| <= 24*12^3*432 < 2^25 for n=13; < 2^36 for n<=15).
"""
import json, itertools, random
from itertools import combinations
import numpy as np

# ---------------------------------------------------------------- group B3
PERMS = list(itertools.permutations(range(3)))
SIGNS = [(s0, s1, s2) for s0 in (1, -1) for s1 in (1, -1) for s2 in (1, -1)]
B3 = [(perm, sign) for perm in PERMS for sign in SIGNS]  # 48 elements

def g_matrix(g):
    """3x3 signed permutation matrix of g (numpy int64)."""
    perm, sign = g
    M = np.zeros((3, 3), dtype=np.int64)
    for i in range(3):
        M[i, perm[i]] = sign[i]
    return M

def apply_g(g, p, n=13):
    """g(p) about center c=( (n-1)/2 )*3, n odd. p int triple."""
    c = (n - 1) // 2
    perm, sign = g
    u = (p[perm[0]] - c, p[perm[1]] - c, p[perm[2]] - c)
    return (sign[0] * u[0] + c, sign[1] * u[1] + c, sign[2] * u[2] + c)

def apply_g_set(g, S, n=13):
    return frozenset(apply_g(g, p, n) for p in S)

def g_det(g):
    return int(round(np.linalg.det(g_matrix(g).astype(float))))

def g_order(g):
    M = g_matrix(g)
    A = M.copy()
    for k in range(1, 13):
        if np.array_equal(A, np.eye(3, dtype=np.int64)):
            return k
        A = A @ M
    return -1

def g_compose(g1, g2):
    """g1 after g2 as group element (matrix product M1@M2)."""
    M = g_matrix(g1) @ g_matrix(g2)
    perm = tuple(int(np.flatnonzero(M[i])[0]) for i in range(3))
    sign = tuple(int(M[i, perm[i]]) for i in range(3))
    return (perm, sign)

IDENT = ((0, 1, 2), (1, 1, 1))
NEG_I = ((0, 1, 2), (-1, -1, -1))

def element_type(g):
    """Classify: identity, -I, rot180, rot120, rot90, mirror, S4(rotoreflection
    order 4), S6 (order 6 rotoreflection)."""
    if g == IDENT:
        return "I"
    if g == NEG_I:
        return "-I"
    d = g_det(g)
    k = g_order(g)
    if d == 1:
        return {2: "rot180", 3: "rot120", 4: "rot90"}[k]
    return {2: "mirror", 4: "S4", 6: "S6"}[k]

def stabilizer(S, n=13):
    """Subgroup of B3 (about center) fixing the set S."""
    Sf = frozenset(tuple(p) for p in S)
    return [g for g in B3 if apply_g_set(g, Sf, n) == Sf]

def canonical_form(S, n=13):
    """Min over 48 images of the sorted point tuple — canonical rep of orbit."""
    Sf = [tuple(p) for p in S]
    best = None
    for g in B3:
        img = tuple(sorted(apply_g(g, p, n) for p in Sf))
        if best is None or img < best:
            best = img
    return best

# ------------------------------------------------------- exact validity
def lift(p):
    x, y, z = p
    return (x, y, z, x * x + y * y + z * z)

_COMBOS5 = {}
def combos5(m):
    if m not in _COMBOS5:
        _COMBOS5[m] = np.array(list(combinations(range(m), 5)), dtype=np.int64)
    return _COMBOS5[m]

def det5_batch(L, idx):
    """L: (m,4) int64 lifted points; idx: (N,5) indices. Returns (N,) dets."""
    P = L[idx]                       # (N,5,4)
    D = P[:, 1:, :] - P[:, :1, :]    # (N,4,4)
    a0, a1, a2, a3 = D[:, 0, 0], D[:, 0, 1], D[:, 0, 2], D[:, 0, 3]
    b0, b1, b2, b3 = D[:, 1, 0], D[:, 1, 1], D[:, 1, 2], D[:, 1, 3]
    c0, c1, c2, c3 = D[:, 2, 0], D[:, 2, 1], D[:, 2, 2], D[:, 2, 3]
    d0, d1, d2, d3 = D[:, 3, 0], D[:, 3, 1], D[:, 3, 2], D[:, 3, 3]
    return ((a0*b1 - a1*b0) * (c2*d3 - c3*d2) - (a0*b2 - a2*b0) * (c1*d3 - c3*d1)
          + (a0*b3 - a3*b0) * (c1*d2 - c2*d1) + (a1*b2 - a2*b1) * (c0*d3 - c3*d0)
          - (a1*b3 - a3*b1) * (c0*d2 - c2*d0) + (a2*b3 - a3*b2) * (c0*d1 - c1*d0))

def lifted(S):
    return np.array([lift(tuple(p)) for p in S], dtype=np.int64)

def all_dets(S):
    L = lifted(S)
    return det5_batch(L, combos5(len(S)))

def is_valid(S):
    pts = [tuple(p) for p in S]
    if len(set(pts)) != len(pts):
        return False
    if len(pts) < 5:
        return True
    return bool((all_dets(pts) != 0).all())

def is_valid_with_new(S, new):
    """S valid already; check S+new (only 5-subsets touching new). Exact."""
    pts = [tuple(p) for p in S] + [tuple(p) for p in new]
    if len(set(pts)) != len(pts):
        return False
    s, m = len(S), len(pts)
    if m < 5:
        return True
    L = lifted(pts)
    idx = combos5(m)
    idx = idx[idx[:, 4] >= s]        # tuples containing >=1 new point
    return bool((det5_batch(L, idx) != 0).all())

# ------------------------------------------------------- structure probes
def shells(S, n=13):
    """Centered squared radii 4*|p-c|^2 (x4 to stay integral for even n)."""
    c2 = n - 1  # 2c
    out = []
    for p in S:
        out.append(sum((2 * p[i] - c2) ** 2 for i in range(3)))
    return out

def inversion_scores(S):
    """For every possible inversion center 2c'=s, count points p with s-p in S.
    Returns dict s -> count (only counts >= 4 retained)."""
    Sf = set(tuple(p) for p in S)
    from collections import Counter
    cnt = Counter()
    for p in Sf:
        for q in Sf:
            cnt[(p[0] + q[0], p[1] + q[1], p[2] + q[2])] += 1
    return {k: v for k, v in cnt.items() if v >= 4}

def sym_core(S, two_c=(12, 12, 12)):
    """Subset of S closed under p -> 2c'-p."""
    Sf = set(tuple(p) for p in S)
    return sorted(p for p in Sf
                  if tuple(two_c[i] - p[i] for i in range(3)) in Sf)

def load_json_set(path):
    with open(path) as f:
        return [tuple(p) for p in json.load(f)]

def load_jsonl_sets(path, key=None):
    out = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            if key is not None:
                obj = obj[key]
            out.append([tuple(p) for p in obj])
    return out
