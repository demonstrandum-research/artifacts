#!/usr/bin/env python3
"""CONIC-CONE SYMMETRIC CONSTRUCTION  CC(n; F, p, order)  — canonical reference.

Produces, for every n >= 5, a valid set S in {0..n-1}^3 (no 5 points on a
common sphere or plane), deterministically (zero randomness), via:

  1. POOL (congruence-defined):
        E(n; F, p) = { e in Z^3 : e == (n-1) (mod 2) coordwise,
                       0 < |e|_inf <= n-1,  e > -e lex,
                       Q(e) == 0 (mod p) for some Q in F }
     with F a set of nondegenerate ternary quadratic forms over F_p
     (default F = {xy - z^2, yz - x^2, zx - y^2}, the coordinate-symmetric
     triple-Veronese union; p an odd prime ~ 2n/3).
  2. ORDER: sort E by descending |e|^2 (ties lex)   [default 'desc_norm'].
  3. SELECTION: exact greedy — accept e iff S u {c+e/2, c-e/2} stays valid,
     where c = ((n-1)/2)(1,1,1); validity tested with exact integer
     arithmetic (incremental cofactor blocking + pair-internal det5).

Mathematical layer (all verified; sympy + 3000-instance numeric checks):

  LEMMA 1 (factorization, (2,2,1) class).  For antipodal pairs +-a, +-b and a
  fifth point w (all centered):  det5(a,-a,b,-b,w) = -4 (|a|^2-|b|^2) det3[a,b,w].
  Hence a valid symmetric set REQUIRES distinct pair-norms (C1) and no three
  pair-directions coplanar with the center (C2); conversely C1 + C2 kill the
  whole (2,2,1) class.

  LEMMA 2 (conic arc certificate for C2).  If e1, e2, e3 lie on a cone
  Q == 0 mod p (Q nondegenerate over F_p, p odd) in three DISTINCT nonzero
  projective classes, then det3(e1,e2,e3) != 0 mod p — three distinct points
  of a conic in PG(2,p) are never collinear.  For the monomial subfamily
  e_t ~ c t^k (1, t, t^2) this is the Vandermonde identity
  det3 = c^3 (t1 t2 t3)^k V(t1,t2,t3).
  Same-class multi-lifts (the HJSW torus-unwrapping mechanism, actively used
  by the best sets: 18-20 pairs over 12-17 classes) are exact-checked instead.

  LEMMA 3 (1-pair identity, (2,1,1,1) class; Cayley-Menger/power-of-a-point
  specialization).  det5(a,-a,p,q,r) = 2(|a|^2 (a.u) - a.w) with
  u = pxq+qxr+rxp, w = |p|^2(qxr)+|q|^2(rxp)+|r|^2(pxq).  Writing
  p,q,r = s_b b, s_c c, s_d d (signed picks from three other pairs):
  det5/2 = s_b s_c A + s_c s_d B + s_d s_b C  with
  A = (Na-Nd) det3[a,b,c], B = (Na-Nb) det3[a,c,d], C = (Na-Nc) det3[a,d,b];
  the four sign classes need A+B+C, A-B-C, B-A-C, C-A-B all nonzero —
  norm-gap x bracket sums, not certifiable by the conic alone.

  LEMMA 4 (isotropic-cone cap, negative).  If Q = x^2+y^2+z^2 then all pair
  norms are == 0 mod p and the pair count is capped by the number of
  realizable norm shells divisible by p; e.g. (n,p)=(13,11): 7 pairs.
  Exact search hits these caps exactly — that template is provably dead.

  THEOREM-SHAPE (honest).  For any output of CC(n; F, p, order): every
  5-subset containing two full antipodal pairs whose three directions lie in
  distinct nonzero classes of a single conic is nonzero BY CONSTRUCTION;
  full validity is established by the exact greedy and re-certified
  independently (check_cert.py).  Empirically every instance also admits a
  compact TWO-PRIME certificate (p for the conic layer, a single q ~ 10^4 for
  all remaining 5-subsets), e.g. the deterministic n=17, 36-point set is
  fully certified by congruences mod 13 and mod 15107.

Results (all sets re-verified with code/check_cert.py; see MANIFEST.json):

   n                      11   12   13   14   15   16   17
   deterministic CC(n)    26   26   28   30   34   34   36    (zero search)
   cone-pool + ILS        26   28   30   32   36   36   40
   unrestricted SYM ILS   28   32   36*  36   38   40   40    (*record C(13))
   2.12n--2.36n deterministic, 2.31n--2.50n cone-ILS, 2.35n--2.77n full.

Usage:  python CONSTRUCTION.py n [p] [forms] [order]
        defaults: p = best known per n, forms = ver_vera_verb, desc_norm.
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import (set_idle_priority, make_pool, template_pred,
                     SymPoolSearch, exact_check)
from det_cone_greedy import ORDERS

BEST_P = {11: 11, 12: 11, 13: 11, 14: 11, 15: 11, 16: 13, 17: 13}

def construct(n, p=None, forms="union_ver_vera_verb", order="desc_norm"):
    p = p or BEST_P.get(n, max(q for q in (5, 7, 11, 13, 17, 19, 23)
                               if q <= max(5, (2 * n) // 3)))
    pool = make_pool(n, template_pred(f"{forms}{p}"))
    S = SymPoolSearch(n, pool, seed=0)
    evs = [tuple(int(v) for v in S.E[i]) for i in range(len(S.E))]
    key = ORDERS[order]
    sel = S.build([], order=sorted(range(len(evs)), key=lambda i: key(evs[i])))
    return S.points(sel), p

def construct_best(n, verbose=False):
    """Deterministic max over the fixed finite menu (cone pools x orders).
    Still zero randomness: the menu is part of the construction definition."""
    menu_p = [q for q in (7, 11, 13, 17, 19) if q <= n]
    menu_forms = ["ver", "hyp", "union_ver_hyp", "union_ver_vera_verb"]
    best = None
    for p in menu_p:
        for forms in menu_forms:
            pool = make_pool(n, template_pred(f"{forms}{p}"))
            if len(pool) < 3:
                continue
            S = SymPoolSearch(n, pool, seed=0)
            evs = [tuple(int(v) for v in S.E[i]) for i in range(len(S.E))]
            for oname, key in ORDERS.items():
                order = sorted(range(len(evs)), key=lambda i: key(evs[i]))
                sel = S.build([], order=order)
                pts = S.points(sel)
                if best is None or len(pts) > best["points"]:
                    best = {"n": n, "p": p, "forms": forms, "order": oname,
                            "points": len(pts), "set": pts}
                    if verbose:
                        print(json.dumps({k: best[k] for k in
                                          ("n", "p", "forms", "order", "points")}),
                              flush=True)
    return best

if __name__ == "__main__":
    set_idle_priority()
    n = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == "--best":
        best = construct_best(n, verbose=True)
        ok, why = exact_check(best["set"], n)
        best["valid"] = ok
        fn = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          f"CC_best_n{n}_m{best['points']}.json")
        json.dump(best["set"], open(fn, "w"))
        print(json.dumps({k: best[k] for k in
                          ("n", "p", "forms", "order", "points", "valid")}))
    else:
        p = int(sys.argv[2]) if len(sys.argv) > 2 else None
        forms = sys.argv[3] if len(sys.argv) > 3 else "union_ver_vera_verb"
        order = sys.argv[4] if len(sys.argv) > 4 else "desc_norm"
        pts, p = construct(n, p, forms, order)
        ok, why = exact_check(pts, n)
        print(json.dumps({"n": n, "p": p, "forms": forms, "order": order,
                          "points": len(pts), "valid": ok, "set": pts}))
