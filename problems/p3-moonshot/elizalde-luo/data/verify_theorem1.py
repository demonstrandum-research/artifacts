#!/usr/bin/env python3
"""
Verify THEOREM 1 (candidate characterization of {1132,3312}-avoiding nonnesting words).

Setup: nonnesting word = (Dyck shape s, label perm p); arc i = (o_i, c_i) = i-th
opener/closer positions, both labeled p_i.

THEOREM 1 (to verify): (s,p) is an avoider iff
  (a) for every k >= 2, p_k is either a strict new max or strict new min of p_1..p_k
      [encode eps_k = M or m], and
  (b) for every pair 2 <= j1 < j2 <= n with o_{j2} < c_{j1}  (arcs j1,j2 cross)
      and o_{j2} > c_1 (arc j2 opens after the FIRST closer of the word):
      eps_{j1} != eps_{j2}.

Checks:
  T1-set: for n <= MAXN_FULL, the set of (shape, p) avoiders from brute force equals
          the set predicted by Theorem 1.  (exact set equality, every shape)
  T1-n8:  for n = 8, per-shape counts predicted by Theorem 1 (number of proper
          2-colorings = 2^{#components} if bipartite else 0) equal the per-shape
          brute-force counts recorded in refined_stats.json.
"""
import sys, os, json, math
from itertools import permutations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enumerator import dyck_shapes, word_from_shape_perm, is_avoider_fast

HERE = os.path.dirname(os.path.abspath(__file__))

def arcs_of_shape(shape):
    opos, cpos = [], []
    for i, st in enumerate(shape):
        (opos if st else cpos).append(i)
    return opos, cpos

def eps_of_perm(p):
    """Return eps string in {'M','m'} of length n-1, or None if some entry is
    neither a new max nor a new min."""
    n = len(p)
    lo = hi = p[0]
    eps = []
    for k in range(1, n):
        if p[k] > hi:
            eps.append('M'); hi = p[k]
        elif p[k] < lo:
            eps.append('m'); lo = p[k]
        else:
            return None
    return tuple(eps)

def perm_of_eps(eps):
    """Inverse: eps in {M,m}^{n-1} -> permutation p (each entry new max/min)."""
    n = len(eps) + 1
    r = sum(1 for e in eps if e == 'm')
    p = [r + 1]
    lo, hi = r + 1, r + 1
    for e in eps:
        if e == 'M':
            hi += 1; p.append(hi)
        else:
            lo -= 1; p.append(lo)
    return tuple(p)

def theorem1_allowed_eps(shape):
    """All eps tuples allowed by Theorem 1(b) for this shape (brute force over eps,
    used for n small)."""
    opos, cpos = arcs_of_shape(shape)
    n = len(opos)
    c1 = cpos[0]
    pairs = [(j1, j2) for j1 in range(1, n) for j2 in range(j1 + 1, n)
             if opos[j2] < cpos[j1] and opos[j2] > c1]  # 0-based arcs j>=1 means arc index >=2
    out = []
    for mask in range(1 << (n - 1)):
        eps = tuple('M' if (mask >> i) & 1 else 'm' for i in range(n - 1))
        ok = True
        for (j1, j2) in pairs:
            if eps[j1 - 1] == eps[j2 - 1]:
                ok = False; break
        if ok:
            out.append(eps)
    return out

def theorem1_count(shape):
    """#proper 2-colorings of the constraint graph = 2^{#comp} if bipartite else 0.
    Vertices = arcs 2..n (0-based 1..n-1). Computed by union-find with parity."""
    opos, cpos = arcs_of_shape(shape)
    n = len(opos)
    c1 = cpos[0]
    parent = list(range(n - 1))   # vertex v = arc v+2 (0-based arc v+1)
    rank_ = [0] * (n - 1)
    par = [0] * (n - 1)           # parity to parent

    def find(x):
        if parent[x] == x:
            return x, 0
        root, pr = find(parent[x])
        parent[x] = root
        par[x] ^= pr
        return root, par[x]

    bip = True
    for j1 in range(1, n):
        for j2 in range(j1 + 1, n):
            if opos[j2] < cpos[j1] and opos[j2] > c1:
                r1, p1 = find(j1 - 1)
                r2, p2 = find(j2 - 1)
                if r1 == r2:
                    if p1 == p2:
                        bip = False
                else:
                    # union with constraint parity(j1) != parity(j2)
                    if rank_[r1] < rank_[r2]:
                        r1, r2, p1, p2 = r2, r1, p2, p1
                    parent[r2] = r1
                    par[r2] = p1 ^ p2 ^ 1
                    if rank_[r1] == rank_[r2]:
                        rank_[r1] += 1
    if not bip:
        return 0
    comps = sum(1 for x in range(n - 1) if find(x)[0] == x)
    return 2 ** comps

def sstr(shape):
    return "".join("U" if st else "D" for st in shape)

def main():
    MAXN_FULL = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    report = {}
    for n in range(1, MAXN_FULL + 1):
        mismatch_shapes = 0
        total_bf = 0
        total_t1 = 0
        perms = list(permutations(range(1, n + 1)))
        for shape in dyck_shapes(n):
            bf = set()
            for p in perms:
                if is_avoider_fast(word_from_shape_perm(shape, p)):
                    bf.add(p)
            t1 = set(perm_of_eps(e) for e in theorem1_allowed_eps(shape)) if n >= 2 \
                 else ({(1,)} if n == 1 else set())
            total_bf += len(bf)
            total_t1 += len(t1)
            if bf != t1:
                mismatch_shapes += 1
                if mismatch_shapes <= 3:
                    print(f"  MISMATCH n={n} shape={sstr(shape)}")
                    print(f"    bf only: {sorted(bf - t1)[:6]}")
                    print(f"    t1 only: {sorted(t1 - bf)[:6]}")
            # also check the count function agrees with the eps enumeration
            if n >= 2:
                assert theorem1_count(shape) == len(t1), \
                    f"count fn mismatch at {sstr(shape)}: {theorem1_count(shape)} vs {len(t1)}"
        ok = (mismatch_shapes == 0)
        print(f"T1-set n={n}: shapes_mismatched={mismatch_shapes}, "
              f"bf_total={total_bf}, t1_total={total_t1}, "
              f"formula={3**n - 3*2**(n-1) + 1}  {'OK' if ok else 'FAIL'}")
        report[f"set_equality_n{n}"] = {"mismatched_shapes": mismatch_shapes,
                                        "bf_total": total_bf, "t1_total": total_t1,
                                        "ok": ok}
        assert ok

    # n = 8: per-shape counts vs refined_stats.json
    with open(os.path.join(HERE, "refined_stats.json"), encoding="utf-8") as f:
        rs = json.load(f)
    rec8 = [r for r in rs["per_n"] if r["n"] == 8][0]
    bf_shape8 = rec8["stats"]["by_dyck_shape"]
    n = 8
    t1_total = 0
    mism = 0
    nonzero = 0
    for shape in dyck_shapes(n):
        c = theorem1_count(shape)
        t1_total += c
        s = sstr(shape)
        bfc = bf_shape8.get(s, 0)
        if c != bfc:
            mism += 1
            if mism <= 5:
                print(f"  n=8 SHAPE COUNT MISMATCH {s}: t1={c} bf={bfc}")
        if c:
            nonzero += 1
    print(f"T1-n8: per-shape mismatches={mism}, t1_total={t1_total}, "
          f"bf_total={rec8['avoider_count']}, formula={3**8 - 3*2**7 + 1}, "
          f"nonzero_shapes={nonzero}  {'OK' if mism == 0 else 'FAIL'}")
    report["n8_per_shape"] = {"mismatches": mism, "t1_total": t1_total,
                              "bf_total": rec8["avoider_count"],
                              "ok": mism == 0 and t1_total == rec8["avoider_count"]}
    assert mism == 0 and t1_total == rec8["avoider_count"]

    # larger n: Theorem-1 totals vs formula (no brute force available; consistency)
    for n in range(9, 13):
        tot = sum(theorem1_count(shape) for shape in dyck_shapes(n))
        f = 3**n - 3*2**(n-1) + 1
        print(f"T1-total n={n}: {tot} formula={f} {'OK' if tot == f else 'FAIL'}")
        report[f"t1_total_n{n}"] = {"t1_total": tot, "formula": f, "ok": tot == f}
        assert tot == f

    with open(os.path.join(HERE, "verify_theorem1_results.json"), "w",
              encoding="utf-8") as f:
        json.dump(report, f, indent=1)
    print("wrote verify_theorem1_results.json")

if __name__ == "__main__":
    main()
