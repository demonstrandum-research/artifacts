#!/usr/bin/env python3
"""Two-prime certificate probe (Codex foil's proposed experiment).

For a verified centrally-symmetric set built on a conic-cone pool mod p:
  * the (2,2,1) layer is certified mod p WHEN the two pair-directions + third
    direction lie in 3 distinct nonzero projective conic classes mod p
    (lemma layer);
  * everything else (all (2,1,1,1), (1^5) subsets, and (2,2,1) subsets hitting
    a repeated/zero class) needs integer-level verification.
This script finds the SMALLEST PRIME q such that every non-p-certified
5-subset determinant is nonzero mod q.  If q is small, validity of the whole
set is certified purely by congruences mod p and mod q.

Method: exact batch det5 of all uncertified 5-subsets; strip prime factors up
to 2^18 by vectorized trial division (any remaining cofactor > 1 is prime
since |det| < 2^36); q_min = smallest prime outside the factor support.

Usage: python second_prime_cert.py set.json n p
"""
import sys, os, json
import numpy as np
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conelib import set_idle_priority


def main():
    set_idle_priority()
    fn, n, p = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    pts = [tuple(q) for q in json.load(open(fn))]
    s = n - 1
    # antipodal pairing
    mate = {q: tuple(s - x for x in q) for q in pts}
    assert all(mate[q] in pts for q in pts), "set is not centrally symmetric"
    reps = sorted(q for q in pts if q > mate[q])
    pair_of = {}
    for i, q in enumerate(reps):
        pair_of[q] = i
        pair_of[mate[q]] = i
    evec = {i: tuple(2 * a - s for a in q) for q, i in
            ((q, pair_of[q]) for q in reps)}

    def projcls(e):
        r = tuple(v % p for v in e)
        if all(v == 0 for v in r):
            return "ZERO"
        for v in r:
            if v % p:
                inv = pow(v, p - 2, p)
                return tuple((inv * w) % p for w in r)

    cls = {i: projcls(e) for i, e in evec.items()}

    # enumerate 5-subsets; mark certified ones: exactly-2-full-pairs and the
    # three involved directions in distinct nonzero classes
    idx_pts = list(range(len(pts)))
    pair_idx = [pair_of[pts[i]] for i in idx_pts]
    L = np.array([(x, y, z, x*x + y*y + z*z) for (x, y, z) in pts], np.int64)
    uncert = []
    n_cert = 0
    for sub in combinations(idx_pts, 5):
        cnt = {}
        for i in sub:
            cnt[pair_idx[i]] = cnt.get(pair_idx[i], 0) + 1
        full = [k for k, v in cnt.items() if v == 2]
        if len(full) == 2:
            third = [k for k, v in cnt.items() if v == 1][0]
            trip = [cls[full[0]], cls[full[1]], cls[third]]
            if "ZERO" not in trip and len(set(trip)) == 3:
                n_cert += 1
                continue
        uncert.append(sub)
    # batch dets
    U = np.array(uncert, np.int64)
    R = L[U[:, 1:]] - L[U[:, :1]]
    a, b, c, d = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
    det = ((a[:,0]*b[:,1]-a[:,1]*b[:,0])*(c[:,2]*d[:,3]-c[:,3]*d[:,2])
         - (a[:,0]*b[:,2]-a[:,2]*b[:,0])*(c[:,1]*d[:,3]-c[:,3]*d[:,1])
         + (a[:,0]*b[:,3]-a[:,3]*b[:,0])*(c[:,1]*d[:,2]-c[:,2]*d[:,1])
         + (a[:,1]*b[:,2]-a[:,2]*b[:,1])*(c[:,0]*d[:,3]-c[:,3]*d[:,0])
         - (a[:,1]*b[:,3]-a[:,3]*b[:,1])*(c[:,0]*d[:,2]-c[:,2]*d[:,0])
         + (a[:,2]*b[:,3]-a[:,3]*b[:,2])*(c[:,0]*d[:,1]-c[:,1]*d[:,0]))
    assert (det != 0).all()
    vals = np.abs(det).astype(np.int64)

    # vectorized factor-support extraction up to 2^18
    LIM = 1 << 18
    sieve = np.ones(LIM, bool); sieve[:2] = False
    for i in range(2, int(LIM ** 0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = False
    primes = np.nonzero(sieve)[0]
    support = set()
    v = vals.copy()
    for pr in primes:
        if (v % pr == 0).any():
            support.add(int(pr))
            while True:
                m = v % pr == 0
                if not m.any():
                    break
                v[m] //= pr
    support |= set(int(x) for x in np.unique(v[v > 1]))  # big prime cofactors
    q_min = next(int(pr) for pr in primes if int(pr) not in support)
    small_kills = {int(pr): int((vals % pr == 0).sum()) for pr in primes[:25]}
    out = {"file": fn, "n": n, "p": p, "points": len(pts),
           "pairs": len(reps), "subsets_total": n_cert + len(uncert),
           "subsets_p_certified": n_cert, "subsets_uncertified": len(uncert),
           "q_min_second_prime": q_min,
           "n_distinct_primes_in_support": len(support),
           "kills_by_small_prime": small_kills}
    print(json.dumps(out, indent=1))
    json.dump(out, open(fn.replace(".json", "") + f"_2prime_p{p}.json", "w"),
              indent=1)


if __name__ == "__main__":
    main()
