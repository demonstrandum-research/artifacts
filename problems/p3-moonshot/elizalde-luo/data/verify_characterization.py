#!/usr/bin/env python3
"""
Verification suite for the structural lemmas behind the transfer-matrix proof of
the Elizalde-Luo {1132,3312} conjecture.

Lemma chain being tested:
  L2: avoidance <=> P1 (p avoids 132,312) and P2 (crossing betweenness)
  L3: Av(132,312) = prefix-min/max perms, bijective with sign vectors
  L4: given P1, P2 <=> sign-constraint system E(s)
  L5: per-shape solution count of E(s) factorizes over irreducible components
  L6: component classification formulas N(c), M(c)
  TM: 4-state transfer matrix gives a_n = 3^n - 3*2^(n-1)+1
Run: python verify_characterization.py [max_set_n]
"""
import sys, os, math, json
from itertools import permutations, product
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enumerator import (dyck_shapes, word_from_shape_perm, is_avoider_fast,
                        second_positions, contains_1132_fast, contains_3312_fast)

# ---------------------------------------------------------------- basic objects

def shape_arcs(shape):
    """shape: tuple of bool (True=U). Returns (o, c) 0-based opener/closer pos lists."""
    o, c = [], []
    for i, st in enumerate(shape):
        (o if st else c).append(i)
    return o, c

def avoids_132_312(p):
    n = len(p)
    for q in range(n):
        for r in range(q + 1, n):
            for s in range(r + 1, n):
                a, b, cc = p[q], p[r], p[s]
                if a < cc < b:   # 132
                    return False
                if b < cc < a:   # 312
                    return False
    return True

def prefix_minmax(p):
    """True iff every entry is a strict prefix-min or prefix-max."""
    for m in range(1, len(p)):
        pref = p[:m + 1]
        if p[m] != max(pref) and p[m] != min(pref):
            return False
    return True

def sign_of(p):
    """eps_2..eps_n as tuple of +1/-1 (assumes prefix_minmax)."""
    eps = []
    for m in range(1, len(p)):
        eps.append(+1 if p[m] == max(p[:m + 1]) else -1)
    return tuple(eps)

def perm_of_sign(eps_tail, n):
    """Inverse of sign_of: eps_tail = (eps_2..eps_n). Build from the right."""
    vals = list(range(1, n + 1))
    p = [0] * n
    for m in range(n - 1, 0, -1):
        if eps_tail[m - 1] == +1:
            p[m] = vals.pop()      # max remaining
        else:
            p[m] = vals.pop(0)     # min remaining
    p[0] = vals[0]
    return tuple(p)

def P2(shape, p):
    """Literal crossing-betweenness: for all i<k<j with c_i<o_j<c_k:
       p_i strictly between p_k and p_j."""
    o, c = shape_arcs(shape)
    n = len(o)
    for j in range(n):
        for k in range(j):
            if o[j] < c[k]:                    # arcs k,j cross (k<j)
                for i in range(k):
                    if c[i] < o[j]:            # arc i closed before j opens
                        lo, hi = min(p[k], p[j]), max(p[k], p[j])
                        if not (lo < p[i] < hi):
                            return False
    return True

def beta(shape):
    """beta_j (#closers before j-th opener), 1-indexed arcs -> list 0-indexed."""
    o, c = shape_arcs(shape)
    out = []
    for oj in o:
        out.append(sum(1 for cc in c if cc < oj))
    return out

def E_satisfied(shape, eps_full):
    """eps_full: tuple of +-1 length n (eps_1 included). Constraint system E(s):
       for each arc j (0-idx) with beta_j>=1: eps_k = -eps_j for all beta_j<k+1<j+1
       i.e. 0-idx k in [beta_j, j-1]."""
    b = beta(shape)
    n = len(b)
    for j in range(n):
        if b[j] >= 1:
            for k in range(b[j], j):
                if eps_full[k] != -eps_full[j]:
                    return False
    return True

# ------------------------------------------------------- component classification

def split_components(shape):
    """Split Dyck word (tuple of bool) at returns to 0."""
    comps, cur, h = [], [], 0
    for st in shape:
        cur.append(st)
        h += 1 if st else -1
        if h == 0:
            comps.append(tuple(cur))
            cur = []
    assert not cur
    return comps

def runs(comp):
    """Run-length encoding [(letter,count)...] with letter True=U."""
    out = []
    for st in comp:
        if out and out[-1][0] == st:
            out[-1][1] += 1
        else:
            out.append([st, 1])
    return [(a, b) for a, b in out]

def M_formula(comp):
    """Non-first component: 2 if comp == U(UD)^{m-1}D else 0."""
    m = sum(1 for st in comp if st)
    target = [True] + [True, False] * (m - 1) + [False]
    return 2 if list(comp) == target else 0

def N_formula(comp):
    """First component solution count by classification."""
    r = runs(comp)
    m = sum(1 for st in comp if st)
    a = r[0][1]                       # initial U-run
    if list(comp) == [True] * a + [False] * a:
        return 2 ** a                 # type (i)
    # type (ii): U^a D^x U D^{a-x+1}
    if len(r) == 4:
        (u1, a1), (d1, x), (u2, one), (d2, y) = r
        if one == 1 and 1 <= x <= a1 - 1 and y == a1 - x + 1:
            return 2 ** (x + 1)
        return 0
    # type (iii): U^a D^x U D^{a-x} U (D U)^{t-2} D^2
    if len(r) >= 6 and len(r) % 2 == 0:
        (u1, a1), (d1, x) = r[0], r[1]
        if not (1 <= x <= a1 - 1):
            return 0
        if r[2] != (True, 1) or r[3] != (False, a1 - x):
            return 0
        # remaining must be U (D U)^{t-2} D^2  i.e. runs: (U,1) then alternating (D,1),(U,1)... ending (D,2)
        rest = r[4:]
        if rest[0] != (True, 1):
            return 0
        body, last = rest[1:-1], rest[-1]
        if last != (False, 2):
            return 0
        # body must alternate (D,1),(U,1),(D,1),(U,1),...
        for idx, rr in enumerate(body):
            want = (False, 1) if idx % 2 == 0 else (True, 1)
            if rr != want:
                return 0
        if len(body) % 2 != 0:
            return 0
        return 2 ** (x + 1)
    return 0

def per_shape_formula_count(shape):
    comps = split_components(shape)
    val = N_formula(comps[0])
    for cmp_ in comps[1:]:
        val *= M_formula(cmp_)
    return val // 2  # /2 for eps_1 irrelevance

# ------------------------------------------------------------------ brute solvers

def brute_E_count(shape):
    n = sum(1 for st in shape if st)
    cnt = 0
    for eps in product((1, -1), repeat=n):
        if E_satisfied(shape, eps):
            cnt += 1
    return cnt

def brute_nonfirst_component_count(comp):
    """Solutions of the NON-FIRST system: every arc j>=2 constrained vs open arcs."""
    o, c = shape_arcs(comp)
    m = len(o)
    cnt = 0
    for eps in product((1, -1), repeat=m):
        ok = True
        for j in range(1, m):
            for k in range(j):
                if c[k] > o[j]:          # arc k open at o_j
                    if eps[k] != -eps[j]:
                        ok = False
                        break
            if not ok:
                break
        if ok:
            cnt += 1
    return cnt

def brute_first_component_count(comp):
    """Solutions of the FIRST system: arc j constrained only if some closer < o_j."""
    o, c = shape_arcs(comp)
    m = len(o)
    b = [sum(1 for cc in c if cc < oj) for oj in o]
    cnt = 0
    for eps in product((1, -1), repeat=m):
        ok = True
        for j in range(m):
            if b[j] >= 1:
                for k in range(b[j], j):
                    if eps[k] != -eps[j]:
                        ok = False
                        break
            if not ok:
                break
        if ok:
            cnt += 1
    return cnt

def irreducible_shapes(m):
    """All irreducible Dyck words with m arcs: U (dyck m-1) D."""
    for inner in dyck_shapes(m - 1):
        yield (True,) + tuple(inner) + (False,)

# ------------------------------------------------------------------- transfer mtx

def transfer_count(n):
    # states s1,s2,s3,s4 ; M[i][j] weights
    M = [[2, 2, 0, 2],
         [0, 1, 1, 0],
         [0, 0, 1, 2],
         [0, 0, 0, 3]]
    v = [1, 0, 0, 0]
    for _ in range(n - 1):
        v = [sum(v[i] * M[i][j] for i in range(4)) for j in range(4)]
    f = [1, 0, 1, 1]
    return sum(v[i] * f[i] for i in range(4))

# ============================================================== main verification

def main():
    max_set_n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    report = {}

    # ---- L3: sign bijection
    for n in range(1, 9):
        av, pm = [], []
        for p in permutations(range(1, n + 1)):
            if avoids_132_312(p):
                av.append(p)
            if prefix_minmax(p):
                pm.append(p)
        assert set(av) == set(pm), f"L3 class equality failed n={n}"
        assert len(av) == 2 ** (n - 1), f"L3 count failed n={n}"
        for p in av:
            assert perm_of_sign(sign_of(p), n) == p, f"L3 roundtrip failed {p}"
        seen = set(sign_of(p) for p in av)
        assert len(seen) == 2 ** (n - 1), f"L3 injectivity failed n={n}"
    report["L3"] = "OK n<=8 (class equality, count 2^(n-1), sign bijection roundtrip)"
    print(report["L3"], flush=True)

    # ---- L2 and L4 and full set equality, n <= max_set_n
    for n in range(1, max_set_n + 1):
        brute_avoiders = set()
        char_avoiders = set()
        l2_checked = l4_checked = 0
        for shape in dyck_shapes(n):
            for p in permutations(range(1, n + 1)):
                w = word_from_shape_perm(shape, p)
                av = is_avoider_fast(w)
                p1 = avoids_132_312(p)
                p2 = P2(shape, p)
                assert av == (p1 and p2), f"L2 failed n={n} shape={shape} p={p}"
                l2_checked += 1
                if av:
                    brute_avoiders.add(w)
                if p1:
                    eps_full = (1,) + sign_of(p)
                    e_ok = E_satisfied(shape, eps_full)
                    assert p2 == e_ok, f"L4 failed n={n} shape={shape} p={p}"
                    l4_checked += 1
                    if e_ok:
                        char_avoiders.add(w)
        assert brute_avoiders == char_avoiders, f"set equality failed n={n}"
        expected = 3 ** n - 3 * 2 ** (n - 1) + 1
        assert len(brute_avoiders) == expected, f"count failed n={n}"
        print(f"L2/L4/set-equality OK n={n}: {l2_checked} (shape,p) pairs checked, "
              f"{l4_checked} L4 pairs, {len(brute_avoiders)} avoiders == {expected}",
              flush=True)
    report["L2_L4_setequality"] = f"OK for n<={max_set_n}"

    # ---- L5 + L6 + per-shape counts vs refined_stats for n <= 8
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "refined_stats.json"), encoding="utf-8") as f:
        rs = json.load(f)
    stats_by_n = {e["n"]: e["stats"]["by_dyck_shape"] for e in rs["per_n"]}
    for n in range(1, 9):
        ground = stats_by_n.get(n, {})
        tot = 0
        for shape in dyck_shapes(n):
            sstr = "".join("U" if st else "D" for st in shape)
            bc = brute_E_count(shape)             # brute solutions of E(s)
            # L5: factorization over components
            comps = split_components(shape)
            prod = brute_first_component_count(comps[0])
            for cmp_ in comps[1:]:
                prod *= brute_nonfirst_component_count(cmp_)
            assert bc == prod, f"L5 factorization failed {sstr}: {bc} != {prod}"
            # L6: closed-form component formulas
            fc = per_shape_formula_count(shape)
            assert bc // 2 == fc, f"L6 formula failed {sstr}: {bc//2} != {fc}"
            assert bc % 2 == 0
            # ground truth per shape
            gt = ground.get(sstr, 0)
            assert fc == gt, f"per-shape vs ground truth failed {sstr}: {fc} != {gt}"
            tot += fc
        expected = 3 ** n - 3 * 2 ** (n - 1) + 1
        assert tot == expected, f"total failed n={n}"
        print(f"L5/L6/per-shape-vs-rust OK n={n}: total {tot} == {expected}", flush=True)
    report["L5_L6_pershape"] = "OK n<=8 vs refined_stats (Rust ground truth)"

    # ---- L6 component formulas exhaustively on irreducible comps up to 8 arcs
    for m in range(1, 9):
        for comp in irreducible_shapes(m):
            bn = brute_nonfirst_component_count(comp)
            bf = brute_first_component_count(comp)
            assert bn == M_formula(comp), f"M formula failed {comp}"
            assert bf == N_formula(comp), f"N formula failed {comp}: {bf} vs {N_formula(comp)}"
    report["L6_irreducible"] = "OK all irreducible components with <=8 arcs"
    print(report["L6_irreducible"], flush=True)

    # ---- transfer matrix vs formula
    for n in range(1, 41):
        tm = transfer_count(n)
        expected = 3 ** n - 3 * 2 ** (n - 1) + 1
        assert tm == expected, f"transfer matrix failed n={n}: {tm} != {expected}"
    report["TM"] = "OK transfer matrix == 3^n-3*2^(n-1)+1 for n<=40"
    print(report["TM"], flush=True)

    # ---- recurrence check on formula values
    a = [None] + [3 ** n - 3 * 2 ** (n - 1) + 1 for n in range(1, 41)]
    for n in range(4, 41):
        assert a[n] == 6 * a[n - 1] - 11 * a[n - 2] + 6 * a[n - 3]
    report["recurrence"] = "OK a_n = 6a_(n-1)-11a_(n-2)+6a_(n-3) for 4<=n<=40"
    print(report["recurrence"], flush=True)

    print("\nALL CHECKS PASSED")
    with open(os.path.join(here, "verify_characterization_report.json"), "w",
              encoding="utf-8") as f:
        json.dump(report, f, indent=1)

if __name__ == "__main__":
    main()
