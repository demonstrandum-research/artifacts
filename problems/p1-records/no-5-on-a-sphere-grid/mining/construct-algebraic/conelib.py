#!/usr/bin/env python3
"""Library for algebraic (congruence-defined) centrally-symmetric constructions.

Framework
---------
All sets are centrally symmetric: S = { (n-1+e)/2, (n-1-e)/2 : e in E } in {0..n-1}^3,
where E is a set of "e-vectors" (e = p1 - p2, the antipodal difference), with
e == (n-1) mod 2 coordinatewise (so points are integral), 0 < |e|_inf <= n-1,
one representative per +/- class.  For odd n, e = 2d with d the classic d-vector.

Algebraic templates restrict E to a congruence-defined pool:
    E_Q,p = { e : Q(e) == 0 (mod p) }          (a quadric cone mod p)
This is the "directions on a conic in PG(2,p)" design rule:
  * a nondegenerate conic is a maximal arc in PG(2,p) (Segre), so triples of
    pool directions in DISTINCT residue classes have det3 != 0 mod p ==> the
    (2,2,1) factorization lemma det5 = +-(N_i - N_j) * det3(e_i,e_j,e_k) is
    nonzero by construction (given distinct norms N).
  * with p ~ n/2 each projective residue direction has several integer lifts
    (HJSW torus-unwrapping), letting the pool exceed the p+1 arc bound; same-
    residue triples are then checked exactly over Z.

The searcher below does FULL exact validity (no law shortcuts): incremental
cofactor blocking for 5-subsets with one new point, batch det5 for 5-subsets
with both new points.  Final sets are re-verified by the independent checker
code/check_cert.py.
"""
import sys, os, json, time, random
import numpy as np
from itertools import combinations

BASE = r"C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid"
sys.path.insert(0, os.path.join(BASE, "code"))
from check_cert import check as exact_check  # noqa: E402

OUT = os.path.join(BASE, "mining", "construct-algebraic")


def set_idle_priority():
    """Run at IDLE priority so the user keeps the machine."""
    try:
        import ctypes
        h = ctypes.windll.kernel32.GetCurrentProcess()
        ctypes.windll.kernel32.SetPriorityClass(h, 0x00000040)  # IDLE_PRIORITY_CLASS
    except Exception:
        pass


# ---------------------------------------------------------------- pools

def evec_box(n):
    """All canonical e-vectors for grid {0..n-1}^3: e == (n-1) mod 2 coordwise,
    coords in [-(n-1), n-1], e > -e lexicographically (one per +/- class)."""
    par = (n - 1) % 2
    rng = [v for v in range(-(n - 1), n) if v % 2 == par]
    out = []
    for x in rng:
        for y in rng:
            for z in rng:
                if (x, y, z) > (-x, -y, -z):
                    out.append((x, y, z))
    return out


def Q_veronese(x, y, z):       # conic xz = y^2  (rational normal curve directions)
    return x * z - y * y

def Q_iso(x, y, z):            # isotropic cone |e|^2 = 0 mod p
    return x * x + y * y + z * z

def Q_hyp(x, y, z):            # second nondegenerate conic, x^2 + yz
    return x * x + y * z

def Q_vera(x, y, z):           # Veronese conic, coordinate-permuted: xy = z^2
    return x * y - z * z

def Q_verb(x, y, z):           # Veronese conic, coordinate-permuted: yz = x^2
    return y * z - x * x


def make_pool(n, pred):
    return [e for e in evec_box(n) if pred(e)]


# template registry: name -> (description, predicate factory)
def template_pred(name):
    """name like 'full', 'ver7', 'iso7', 'hyp7', 'ver13', 'union_ver_iso7',
    or mixed-prime: 'mix_ver11_ver13', 'mix_ver11_hyp13', ..."""
    if name == "full":
        return lambda e: True
    if name.startswith("mix_"):
        forms = {"ver": Q_veronese, "iso": Q_iso, "hyp": Q_hyp,
                 "vera": Q_vera, "verb": Q_verb}
        parts = []
        for tok in name[4:].split("_"):
            kind = "".join(c for c in tok if c.isalpha())
            pp = int("".join(c for c in tok if c.isdigit()))
            parts.append((forms[kind], pp))
        return lambda e, parts=parts: any(Q(*e) % pp == 0 for Q, pp in parts)
    kind = "".join(c for c in name if c.isalpha() or c == "_")
    p = int("".join(c for c in name if c.isdigit()))
    forms = {"ver": Q_veronese, "iso": Q_iso, "hyp": Q_hyp,
             "vera": Q_vera, "verb": Q_verb}
    if kind in forms:
        Q = forms[kind]
        return lambda e, Q=Q, p=p: Q(*e) % p == 0
    if kind.startswith("union_"):
        parts = kind[len("union_"):].split("_")
        Qs = [forms[k] for k in parts]
        return lambda e, Qs=Qs, p=p: any(Q(*e) % p == 0 for Q in Qs)
    raise ValueError(name)


# ---------------------------------------------------------------- exact search

def _cofactors(L):
    """cofactor vectors of all 4-subsets of rows of L (k,5) -> (C(k,4),5), int64 exact."""
    k = len(L)
    if k < 4:
        return np.zeros((0, 5), np.int64)
    idx = np.array(list(combinations(range(k), 4)), np.int32)
    Qm = L[idx]
    cols = np.arange(5)
    out = np.zeros((len(idx), 5), np.int64)
    for j in range(5):
        sub = Qm[:, :, cols != j]
        a, b, c, d = sub[:, 0], sub[:, 1], sub[:, 2], sub[:, 3]
        det = ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(c[:,2]*d[:,3]-c[:,3]*d[:,2])
             - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(c[:,1]*d[:,3]-c[:,3]*d[:,1])
             + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(c[:,1]*d[:,2]-c[:,2]*d[:,1])
             + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(c[:,0]*d[:,3]-c[:,3]*d[:,0])
             - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(c[:,0]*d[:,2]-c[:,2]*d[:,0])
             + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(c[:,0]*d[:,1]-c[:,1]*d[:,0]))
        out[:, j] = ((-1) ** j) * det
    return out


def _det5_pair_ok(Lmem, l1, l2):
    """all det5 over (triples of members + both new points) nonzero."""
    k = len(Lmem)
    if k < 3:
        if k == 2:
            M = np.stack([Lmem[0], Lmem[1], l1, l2])
            return bool((_cofactors(M) != 0).any())
        return True
    idx = np.array(list(combinations(range(k), 3)), np.int32)
    T = Lmem[idx]
    rows = np.concatenate([T, np.broadcast_to(l1, (len(idx), 1, 5)),
                           np.broadcast_to(l2, (len(idx), 1, 5))], axis=1)
    R = rows[:, 1:, :4] - rows[:, :1, :4]
    a, b, c, d = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
    det = ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(c[:,2]*d[:,3]-c[:,3]*d[:,2])
         - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(c[:,1]*d[:,3]-c[:,3]*d[:,1])
         + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(c[:,1]*d[:,2]-c[:,2]*d[:,1])
         + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(c[:,0]*d[:,3]-c[:,3]*d[:,0])
         - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(c[:,0]*d[:,2]-c[:,2]*d[:,0])
         + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(c[:,0]*d[:,1]-c[:,1]*d[:,0]))
    return not (det == 0).any()


class SymPoolSearch:
    """Greedy + ILS over a restricted e-vector pool, exact incremental validity."""

    def __init__(self, n, evecs, seed=1):
        self.n = n
        E = np.array(sorted(evecs), dtype=np.int64)
        self.E = E
        self.NORM = (E * E).sum(axis=1)
        s = n - 1
        P1 = (s + E) // 2
        P2 = (s - E) // 2
        assert ((s + E) % 2 == 0).all(), "parity violation in e-vector pool"
        assert (P1 >= 0).all() and (P1 < n).all() and (P2 >= 0).all() and (P2 < n).all()
        self.P1, self.P2 = P1, P2
        self.L1 = np.concatenate([P1, (P1*P1).sum(1, keepdims=True),
                                  np.ones((len(E), 1), np.int64)], axis=1)
        self.L2 = np.concatenate([P2, (P2*P2).sum(1, keepdims=True),
                                  np.ones((len(E), 1), np.int64)], axis=1)
        self.rng = random.Random(seed)

    def build(self, start, tabu=frozenset(), order=None):
        sel = list(start)
        used_norm = set(int(self.NORM[i]) for i in sel)
        pts = []
        for i in sel:
            pts.append(self.L1[i]); pts.append(self.L2[i])
        Lmem = np.array(pts, np.int64).reshape(-1, 5)
        CF = _cofactors(Lmem)
        if order is None:
            order = [i for i in range(len(self.E)) if i not in sel and i not in tabu]
            self.rng.shuffle(order)
        for i in order:
            if i in sel or i in tabu:
                continue
            if int(self.NORM[i]) in used_norm:
                continue
            l1, l2 = self.L1[i], self.L2[i]
            if len(CF):
                if (CF @ l1 == 0).any() or (CF @ l2 == 0).any():
                    continue
            if not _det5_pair_ok(Lmem, l1, l2):
                continue
            sel.append(i)
            used_norm.add(int(self.NORM[i]))
            Lmem = np.concatenate([Lmem, l1[None], l2[None]], axis=0)
            CF = _cofactors(Lmem)
        return sel

    def ils(self, budget, start=None, verbose=False):
        t0 = time.time()
        cur = self.build(start or [])
        best = list(cur)
        it = 0
        while time.time() - t0 < budget:
            it += 1
            r = self.rng.choice([1, 1, 2, 2, 3])
            if len(cur) <= r:
                cur = self.build([])
            else:
                removed = self.rng.sample(cur, r)
                keep = [i for i in cur if i not in removed]
                cand = self.build(keep, tabu=frozenset(removed))
                cand = self.build(cand)
                if len(cand) >= len(cur):
                    cur = cand
            if len(cur) > len(best):
                best = list(cur)
                if verbose:
                    print(json.dumps({"t": round(time.time()-t0, 1), "iter": it,
                                      "pairs": len(best)}), flush=True)
        return best, it

    def points(self, sel):
        pts = []
        for i in sel:
            pts.append([int(v) for v in self.P1[i]])
            pts.append([int(v) for v in self.P2[i]])
        return sorted(pts)


def verify_and_save(n, pts, tag):
    ok, why = exact_check(pts, n)
    fn = os.path.join(OUT, f"{tag}_n{n}_m{len(pts)}.json")
    if ok:
        json.dump(pts, open(fn, "w"))
    return ok, (fn if ok else why)
