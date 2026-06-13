"""Session 2026-06-12 from-scratch exact verifier for the Sun Conjecture 4.6 kill.

Written independently of driver.py / ryser_mod.c / checker.py / independent/*.
Differences from all prior layers:
  - permanent by SUBSET-SUM DP  f[S] = sum_{j in S} A[popcount(S)-1][j] * f[S \ {j}]
    (not Ryser, not Glynn),
  - fresh random 57-bit primes q == 1 (mod 4n), own deterministic Miller-Rabin,
  - own bound derivation (m! for sin; exact-Fraction chord bound for csc),
  - pure Python, exact integer arithmetic only; no floats anywhere in the proof path.

Logic: the ring hom Z[zeta_4n] -> F_q sending zeta_4n to an element w of exact
multiplicative order 4n fixes Z, so the INTEGER s_n (resp. s'_p), being a
Z-linear identity in Z[zeta_4n][1/(2n)], maps to its residue mod q. The identity
used: with zeta = w^4 (image of e^{2pi i/n}), I = w^n (image of i),
   sin(2pi t/n)  -> (zeta^t - zeta^{-t}) * inv(2 I),
   sqrt(n)       -> G := sum_{j mod n} zeta^{j^2}   if n == 1 (mod 4)
                    G * inv(I)                      if n == 3 (mod 4)
(Gauss: the quadratic Gauss sum equals +sqrt(n), resp. +i sqrt(n), for ALL odd n.)
Then  s_n == 2^m * per(sinM) * inv(sqrtn)  (mod q),  m=(n-1)/2,
      s'_p == sqrtp * per(cscM) * inv(2^m) (mod q).
CRT over primes with prod(q) > 4*BOUND proves the integer uniquely; an extra
held-out prime must agree. BOUNDs are rigorous:
      |s_n|  <= 2^m * m! / 1          (|sin|<=1, |per| <= m!)
      |s'_p| <= p * prod_j sum_k p/(2*min(r,p-r)),  r = 2jk mod p
(|per(A)| <= prod_j sum_k |A_jk| since the permutation sum is dominated by the
sum over ALL functions; |csc(2pi jk/p)| = 1/|sin(pi * (2jk mod p)/p)| and
|sin(pi x)| >= 2*dist(x,Z) for the chord bound; sqrt(p) <= p.)
"""
import random, sys
from fractions import Fraction
from math import factorial

random.seed(20260612)

# ---------- own primality (deterministic MR for < 3.3e24) ----------
_MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
def is_prime(n):
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def fresh_prime(mult, lo=1 << 56, hi=1 << 57, used=()):
    while True:
        q = mult * random.randrange(lo // mult, hi // mult) + 1
        if q not in used and q > lo and is_prime(q):
            return q

def trial_factor(n):
    fs, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d)
            n //= d
        d += 1
    if n > 1:
        fs.add(n)
    return fs

def elem_of_order(q, order):
    fs = trial_factor(order)
    while True:
        w = pow(random.randrange(2, q - 1), (q - 1) // order, q)
        if w != 1 and pow(w, order, q) == 1 and all(pow(w, order // r, q) != 1 for r in fs):
            return w

# ---------- permanent by subset DP (NOT Ryser, NOT Glynn) ----------
def permanent_mod(A, q):
    m = len(A)
    f = [0] * (1 << m)
    f[0] = 1
    for S in range(1, 1 << m):
        row = A[bin(S).count('1') - 1]
        T, acc = S, 0
        while T:
            b = T & -T
            acc += row[b.bit_length() - 1] * f[S ^ b]
            T ^= b
        f[S] = acc % q
    return f[-1]

# ---------- one residue of s_n or s'_n ----------
def residue(n, kind, q):
    m = (n - 1) // 2
    w = elem_of_order(q, 4 * n)
    zeta = pow(w, 4, q)
    I = pow(w, n, q)
    assert I * I % q == q - 1
    zp = [pow(zeta, t, q) for t in range(n)]
    inv2I = pow(2 * I, q - 2, q)
    A = []
    for j in range(1, m + 1):
        row = []
        for k in range(1, m + 1):
            t = j * k % n
            v = (zp[t] - zp[(n - t) % n]) * inv2I % q
            if kind == 'csc':
                assert v != 0
                v = pow(v, q - 2, q)
            row.append(v)
        A.append(row)
    G = sum(zp[j * j % n] for j in range(n)) % q
    sqrtn = G if n % 4 == 1 else G * pow(I, q - 2, q) % q
    assert sqrtn * sqrtn % q == n % q, "Gauss-sum sanity failed"
    per = permanent_mod(A, q)
    if kind == 'sin':
        return pow(2, m, q) * per % q * pow(sqrtn, q - 2, q) % q
    return sqrtn * per % q * pow(pow(2, m, q), q - 2, q) % q

# ---------- rigorous bounds ----------
def bound(n, kind):
    m = (n - 1) // 2
    if kind == 'sin':
        return (1 << m) * factorial(m)          # >= 2^m * m!/sqrt(n)
    B = Fraction(1)
    for j in range(1, m + 1):
        rs = Fraction(0)
        for k in range(1, m + 1):
            r = 2 * j * k % n
            rs += Fraction(n, 2 * min(r, n - r))
        B *= rs
    B = B * n / (1 << m)                        # sqrt(p) <= p
    return int(B) + 1

# ---------- exact value with CRT-uniqueness proof + held-out prime ----------
def exact_value(n, kind):
    B = bound(n, kind)
    qs, M = [], 1
    while M <= 4 * B:
        q = fresh_prime(4 * n, used=set(qs))
        qs.append(q)
        M *= q
    held = fresh_prime(4 * n, used=set(qs))
    x, Mc = 0, 1
    for q in qs:
        r = residue(n, kind, q)
        t = (r - x) * pow(Mc, -1, q) % q
        x += Mc * t
        Mc *= q
    if x > Mc // 2:
        x -= Mc
    assert abs(x) <= 2 * B, (n, kind, "reconstruction exceeds rigorous bound")
    assert x % held == residue(n, kind, held), (n, kind, "HELD-OUT prime mismatch")
    return x

SUN = {('sin', 3): 1, ('sin', 5): -1, ('sin', 7): 1, ('sin', 9): 9, ('sin', 11): 1,
       ('sin', 13): 51, ('sin', 15): 45, ('sin', 17): -239, ('sin', 19): 913,
       ('sin', 21): 2835, ('sin', 23): 12145,
       ('csc', 3): 1, ('csc', 5): 1, ('csc', 7): -6, ('csc', 11): 111,
       ('csc', 13): 261, ('csc', 17): 6784, ('csc', 19): 245101, ('csc', 23): -7094142}

def main():
    print("== validation: all 19 values published by Sun (Remark 1.6) ==")
    for (kind, n), v in sorted(SUN.items(), key=lambda kv: (kv[0][1], kv[0][0])):
        got = exact_value(n, kind)
        print(f"  {kind} n={n}: computed {got}, Sun says {v}  {'OK' if got == v else 'MISMATCH!'}")
        assert got == v
    print("all 19 reproduced exactly.\n")

    print("== primary kill: p = 29 (29 == 5 mod 12, 29 == 5 mod 8) ==")
    s29 = exact_value(29, 'sin')
    sp29 = exact_value(29, 'csc')
    print(f"  s_29  = {s29}")
    print(f"  s'_29 = {sp29}")
    assert s29 % 29 == (-1) ** ((29 + 1) // 2) % 29, "proven congruence fails for s_29!"
    assert sp29 % 29 == 1, "proven congruence fails for s'_29!"
    print(f"  proven congruences hold: s_29 == {s29 % 29} == -1, s'_29 == {sp29 % 29} == 1 (mod 29)")
    v1 = (s29 < 0) == (29 % 12 == 5)
    v2 = (sp29 < 0) == (29 % 8 == 7)
    print(f"  clause s_p<0 <=> p==5(12):  conjecture demands s_29 < 0; actual sign {'+' if s29 > 0 else '-'}"
          f" -> {'consistent' if v1 else 'VIOLATED'}")
    print(f"  clause s'_p<0 <=> p==7(8):  conjecture demands s'_29 >= 0; actual sign {'+' if sp29 > 0 else '-'}"
          f" -> {'consistent' if v2 else 'VIOLATED'}")
    assert s29 == 1053859 and sp29 == -4806838304, "values differ from prior sessions' claim!"
    print("  matches prior sessions' claimed values exactly.\n")

    print("== secondary counterexample: p = 41 (41 == 5 mod 12) ==")
    s41 = exact_value(41, 'sin')
    print(f"  s_41 = {s41}  (conjecture demands < 0) -> {'VIOLATED' if s41 > 0 else 'consistent'}")
    assert s41 == 5574476521
    assert s41 % 41 == (-1) ** ((41 + 1) // 2) % 41

    print("\nVERDICT: Conjecture 4.6(ii) fails at p=29 on BOTH iff clauses (and again at p=41")
    print("on the mod-12 clause); Conjecture 4.6 as stated (conjunction of (i) and (ii)) is FALSE.")

if __name__ == '__main__':
    main()
