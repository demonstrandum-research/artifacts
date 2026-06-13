#!/usr/bin/env python3
"""
INDEPENDENT clean-room checker for Zhi-Wei Sun, Conjecture 4.6
(arXiv:2108.07723v7, "Arithmetic properties of some permanents").

Written from scratch for the verification job; shares NO code or algorithmic
approach with the attack artifacts (which used: finite-field CRT Ryser in C
with Montgomery arithmetic; mpmath floating Glynn; mpmath subset-DP).

METHOD (exact integer arithmetic throughout, no floats, no finite fields):

  Let n > 1 be odd, m = (n-1)/2, N = 4n, zeta = e^{2*pi*i/N} (primitive
  N-th root of unity), so that e^{2*pi*i*jk/n} = zeta^{4jk} and i = zeta^n.

  sin definition (Thm 1.6(i)):
      s_n = (2^m / sqrt(n)) * per[ sin(2*pi*jk/n) ]_{1<=j,k<=m}
      sin(2*pi*jk/n) = (zeta^{4jk} - zeta^{-4jk}) / (2i)
   => per(M) = s_n * i^m * sqrt(n)          in Z[zeta_N],          (*)
      where M_{jk} = zeta^{4jk} - zeta^{-4jk}.

  csc definition (Thm 1.6(ii), p an odd prime):
      s'_p = (sqrt(p) / 2^m) * per[ csc(2*pi*jk/p) ]_{1<=j,k<=m}
      csc(2*pi*jk/p) = 2i / (zeta^{4jk} - zeta^{-4jk})
   => with U_{jk} := p / (zeta^{4jk} - zeta^{-4jk})  in Z[zeta_N]:
      per(U) = s'_p * p^{m-1} * sqrt(p) * i^{-m}     in Z[zeta_N].  (**)

  sqrt(n) inside Z[zeta_N] via the classical Gauss-sum theorem (Gauss):
      G := sum_{a=0}^{n-1} zeta^{4 a^2}  =  sqrt(n)   if n = 1 (mod 4)
                                         =  i*sqrt(n) if n = 3 (mod 4),
  valid for ALL odd n >= 3 (prime or composite).

  Everything is computed exactly in the group ring Z[x]/(x^N - 1) with x
  standing for zeta_N.  per(.) is computed by Ryser's formula (Gray-code
  subset walk); ring elements are held as pairs of nonnegative big integers
  via Kronecker substitution x -> 2^K (positive part, negative part), with K
  chosen from a rigorous a-priori L1 bound so that no base-2^K digit can ever
  overflow.  Cyclic reduction mod x^N - 1 is multiplication mod 2^{N*K} - 1.

  Final test: P - R = 0 (mod Phi_N(x)) as integer polynomials, where P is the
  Ryser result and R the right side of (*) / (**).  Phi_N is computed from
  scratch by exact division of x^N - 1 by lower cyclotomics.  Instead of
  verifying a claimed value we SOLVE for the unique integer t with
  P = t * B (mod Phi_N) -- i.e. the checker computes s_n / s'_p itself.

  The U_{jk} for the csc case are obtained by extended Euclid over Q[x]
  modulo Phi_N (Fraction arithmetic), scaled by p, with exact a-posteriori
  verification U_{jk} * (x^{4jk} - x^{-4jk}) = p (mod Phi_N) over Z.

SELF-TESTS run first:
  - brute-force permanent over all permutations (naive cyclic convolution)
    against the Kronecker-Ryser engine, for small n, both sin and csc;
  - float64 Ryser numerical cross-check of every computed value;
  - re-encode-after-decode integrity check on every decode;
  - Gauss-sum element evaluated at e^{2*pi*i/N} must approximate sqrt(n).
"""

import sys, math, time, json, itertools
from fractions import Fraction

LOG_LINES = []
def log(msg):
    print(msg, flush=True)
    LOG_LINES.append(msg)

# ----------------------------------------------------------------------
# Cyclotomic polynomials, exact, from scratch
# ----------------------------------------------------------------------

def poly_divmod_int(num, den):
    """Exact division of integer polynomial num by MONIC integer poly den.
    Coefficient lists, index = degree. Returns (quot, rem)."""
    num = num[:]
    dd = len(den) - 1
    assert den[-1] == 1, "divisor must be monic"
    if len(num) - 1 < dd:
        return [0], num
    quot = [0] * (len(num) - dd)
    for i in range(len(num) - 1, dd - 1, -1):
        c = num[i]
        if c:
            quot[i - dd] = c
            for k in range(dd + 1):
                num[i - dd + k] -= c * den[k]
    while len(num) > 1 and num[-1] == 0:
        num.pop()
    return quot, num

_CYCLO = {}
def cyclotomic(d):
    """Phi_d(x) as integer coefficient list, by exact division."""
    if d in _CYCLO:
        return _CYCLO[d]
    poly = [-1] + [0] * (d - 1) + [1]          # x^d - 1
    for e in range(1, d):
        if d % e == 0:
            q, r = poly_divmod_int(poly, cyclotomic(e))
            assert r == [0], f"cyclotomic division not exact at d={d}, e={e}"
            poly = q
    _CYCLO[d] = poly
    return poly

def poly_rem_int(P, Phi):
    _, r = poly_divmod_int(P, Phi)
    return r

# ----------------------------------------------------------------------
# Extended Euclid over Q[x] for inverses mod Phi (csc entries)
# ----------------------------------------------------------------------

def fpoly_trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def fpoly_divmod(a, b):
    a = [Fraction(c) for c in a]
    b = [Fraction(c) for c in b]
    fpoly_trim(a); fpoly_trim(b)
    db = len(b) - 1
    if len(a) - 1 < db:
        return [Fraction(0)], a
    q = [Fraction(0)] * (len(a) - db)
    inv_lead = 1 / b[-1]
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] * inv_lead
        if c:
            q[i - db] = c
            for k in range(db + 1):
                a[i - db + k] -= c * b[k]
    return q, fpoly_trim(a)

def fpoly_mul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                out[i + j] += ai * bj
    return fpoly_trim(out)

def fpoly_sub(a, b):
    out = [Fraction(0)] * max(len(a), len(b))
    for i, c in enumerate(a): out[i] += c
    for i, c in enumerate(b): out[i] -= c
    return fpoly_trim(out)

def inverse_mod_phi(a_int, Phi_int):
    """Inverse of integer polynomial a modulo Phi over Q[x] (ext. Euclid)."""
    r0 = [Fraction(c) for c in Phi_int]
    r1 = [Fraction(c) for c in a_int]; fpoly_trim(r1)
    s0, s1 = [Fraction(0)], [Fraction(1)]   # s tracks coefficient of a
    while not (len(r1) == 1 and r1[0] == 0):
        q, r2 = fpoly_divmod(r0, r1)
        r0, r1 = r1, r2
        s0, s1 = s1, fpoly_sub(s0, fpoly_mul(q, s1))
    assert len(r0) == 1 and r0[0] != 0, "a not invertible mod Phi"
    g = r0[0]
    inv = [c / g for c in s0]
    _, inv = fpoly_divmod(inv, [Fraction(c) for c in Phi_int])
    return inv   # Fraction coefficients, degree < deg Phi

# ----------------------------------------------------------------------
# Kronecker-substitution group-ring engine  Z[x]/(x^N - 1)
# Elements: pair (pos, neg) of nonnegative ints = sum digit_k * 2^{kK}
# ----------------------------------------------------------------------

class Ring:
    def __init__(self, N, K):
        self.N, self.K = N, K
        self.NK = N * K
        self.MASK = (1 << self.NK) - 1   # also the modulus 2^{NK} - 1

    def fold(self, v):
        NK, MASK = self.NK, self.MASK
        while v >> NK:
            v = (v & MASK) + (v >> NK)
        if v == MASK:
            v = 0
        return v

    def encode_vec(self, vec):
        """coefficient list (any length; indices taken mod N) -> (pos,neg)"""
        K, N = self.K, self.N
        digits_p = [0] * N
        digits_n = [0] * N
        for idx, c in enumerate(vec):
            if c > 0:   digits_p[idx % N] += c
            elif c < 0: digits_n[idx % N] += -c
        pos = neg = 0
        for k in range(N - 1, -1, -1):
            assert digits_p[k] < (1 << (K - 2)) and digits_n[k] < (1 << (K - 2))
            pos = (pos << K) | digits_p[k]
            neg = (neg << K) | digits_n[k]
        return pos, neg

    def decode_signed(self, pos, neg):
        """(pos,neg) -> exact signed coefficient list, with integrity check."""
        K, N = self.K, self.N
        dmask = (1 << K) - 1
        out = []
        for which in (pos, neg):
            v = which
            ds = []
            for _ in range(N):
                d = v & dmask
                assert d < (1 << (K - 1)), "digit overflow: K bound violated"
                ds.append(d)
                v >>= K
            assert v == 0
            # re-encode integrity check
            chk = 0
            for d in reversed(ds):
                chk = (chk << K) | d
            assert chk == which, "decode/re-encode mismatch"
            out.append(ds)
        return [a - b for a, b in zip(out[0], out[1])]

    def pairmul(self, ap, an, bp, bn):
        f = self.fold
        return f(ap * bp + an * bn), f(ap * bn + an * bp)

def ryser_perm_groupring(entry_vecs, m, N, progress=None):
    """Exact permanent of the m x m matrix of group-ring elements
    entry_vecs[j][c] (coefficient lists, len N). Returns coefficient list."""
    # rigorous K from L1 bounds
    L1 = lambda v: sum(abs(c) for c in v)
    Cs = [max(max((L1(entry_vecs[j][c]) for c in range(m))), 1) for j in range(m)]
    walk = (1 << m)
    acc_bound = walk
    for j in range(m):
        acc_bound *= walk * Cs[j]
    K = acc_bound.bit_length() + 2
    ring = Ring(N, K)
    log(f"      [ryser m={m} N={N}: K={K} bits/digit, ints of {N*K} bits]")

    E = [[ring.encode_vec(entry_vecs[j][c]) for c in range(m)] for j in range(m)]
    Rp = [0] * m
    Rn = [0] * m
    accP = accN = 0
    MASK, NK = ring.MASK, ring.NK
    popc = 0
    t0 = time.time()
    for g in range(1, 1 << m):
        c = (g & -g).bit_length() - 1
        S = g ^ (g >> 1)
        if (S >> c) & 1:
            popc += 1
            for j in range(m):
                ep, en = E[j][c]
                Rp[j] += ep
                Rn[j] += en
        else:
            popc -= 1
            for j in range(m):
                ep, en = E[j][c]
                Rp[j] += en
                Rn[j] += ep
        tp, tn = Rp[0], Rn[0]
        pairmul = ring.pairmul
        for j in range(1, m):
            tp, tn = pairmul(tp, tn, Rp[j], Rn[j])
        if (m - popc) & 1:
            tp, tn = tn, tp
        accP += tp
        accN += tn
        if accP >> NK:
            accP = ring.fold(accP)
        if accN >> NK:
            accN = ring.fold(accN)
        if progress and g % progress == 0:
            log(f"        ... {g}/{(1<<m)-1} subsets, {time.time()-t0:.1f}s")
    accP = ring.fold(accP); accN = ring.fold(accN)
    return ring.decode_signed(accP, accN)

# ----------------------------------------------------------------------
# Brute-force reference permanent (naive cyclic convolution + permutations)
# ----------------------------------------------------------------------

def cyc_mul_naive(a, b, N):
    out = [0] * N
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    out[(i + j) % N] += ai * bj
    return out

def perm_bruteforce(entry_vecs, m, N):
    tot = [0] * N
    for tau in itertools.permutations(range(m)):
        prod = [0] * N; prod[0] = 1
        for j in range(m):
            prod = cyc_mul_naive(prod, entry_vecs[j][tau[j]], N)
        for i in range(N):
            tot[i] += prod[i]
    return tot

# ----------------------------------------------------------------------
# Matrix builders and the sqrt(n) element
# ----------------------------------------------------------------------

def sin_entry_vecs(n):
    """M_{jk} = x^{4jk} - x^{-4jk} in Z[x]/(x^N-1), N = 4n."""
    N = 4 * n
    m = (n - 1) // 2
    out = []
    for j in range(1, m + 1):
        row = []
        for k in range(1, m + 1):
            a = (4 * j * k) % N
            v = [0] * N
            if (j * k) % n != 0:
                v[a] += 1
                v[(N - a) % N] -= 1
            row.append(v)
        out.append(row)
    return out

def csc_entry_vecs(p, Phi):
    """U_{jk} = p / (x^{4jk} - x^{-4jk}) mod Phi_{4p}; exact integer vectors,
    verified by exact multiplication back. p must be an odd prime."""
    N = 4 * p
    m = (p - 1) // 2
    cache = {}
    out = []
    for j in range(1, m + 1):
        row = []
        for k in range(1, m + 1):
            a = (4 * j * k) % N
            assert (j * k) % p != 0
            if a not in cache:
                base = [0] * N
                base[a] += 1
                base[(N - a) % N] -= 1
                binv = inverse_mod_phi(base, Phi)
                U = []
                for c in binv:
                    pc = p * c
                    assert pc.denominator == 1, "p*inverse not integral!"
                    U.append(int(pc))
                # exact verification: U * base == p (mod Phi)
                chk = poly_rem_int(cyc_mul_naive(U + [0]*(N - len(U)), base, N), Phi)
                want = [p]
                assert fpoly_trim(chk[:]) == want, f"inverse check failed a={a}"
                cache[a] = U + [0] * (N - len(U))
            row.append(cache[a])
        out.append(row)
    return out

def sqrt_elem(n):
    """Vector for sqrt(n) in Z[x]/(x^N-1) via Gauss sum (N = 4n)."""
    N = 4 * n
    v = [0] * N
    shift = 0 if n % 4 == 1 else 3 * n        # n=3 mod 4: sqrt(n) = G * i^{-1}
    for a in range(n):
        v[(4 * a * a + shift) % N] += 1
    return v

def xpow(e, N):
    v = [0] * N
    v[e % N] = 1
    return v

def sanity_sqrt_float(n):
    """Float sanity: sqrt_elem evaluated at e^{2 pi i / N} ~ sqrt(n)."""
    N = 4 * n
    v = sqrt_elem(n)
    z = sum(c * complex(math.cos(2 * math.pi * k / N), math.sin(2 * math.pi * k / N))
            for k, c in enumerate(v))
    err = abs(z - complex(math.sqrt(n), 0))
    assert err < 1e-6, f"Gauss-sum sqrt sanity failed n={n}: {z} vs sqrt={math.sqrt(n)}"

def solve_scalar(Pvec, Bvec, Phi):
    """Unique integer t with P == t*B (mod Phi); asserts exactness."""
    Pr = poly_rem_int(Pvec, Phi)
    Br = poly_rem_int(Bvec, Phi)
    Pr += [0] * (len(Phi) - 1 - len(Pr))
    Br += [0] * (len(Phi) - 1 - len(Br))
    idx = next((i for i, c in enumerate(Br) if c != 0), None)
    assert idx is not None, "B vanishes mod Phi (impossible)"
    q, r = divmod(Pr[idx], Br[idx])
    assert r == 0, f"P/B not integral at idx {idx}: {Pr[idx]}/{Br[idx]}"
    for i in range(len(Pr)):
        assert Pr[i] == q * Br[i], f"P != t*B at coeff {i}"
    return q

# ----------------------------------------------------------------------
# float64 numerical cross-check (sanity only; exactness comes from above)
# ----------------------------------------------------------------------

def ryser_perm_float(A, m):
    R = [0.0] * m
    tot = 0.0
    popc = 0
    for g in range(1, 1 << m):
        c = (g & -g).bit_length() - 1
        S = g ^ (g >> 1)
        if (S >> c) & 1:
            popc += 1
            for j in range(m): R[j] += A[j][c]
        else:
            popc -= 1
            for j in range(m): R[j] -= A[j][c]
        prod = 1.0
        for j in range(m): prod *= R[j]
        tot += prod if ((m - popc) % 2 == 0) else -prod
    return tot

def s_float(n):
    m = (n - 1) // 2
    A = [[math.sin(2 * math.pi * j * k / n) for k in range(1, m + 1)]
         for j in range(1, m + 1)]
    return (2 ** m / math.sqrt(n)) * ryser_perm_float(A, m)

def sprime_float(p):
    m = (p - 1) // 2
    A = [[1.0 / math.sin(2 * math.pi * j * k / p) for k in range(1, m + 1)]
         for j in range(1, m + 1)]
    return (math.sqrt(p) / 2 ** m) * ryser_perm_float(A, m)

# ----------------------------------------------------------------------
# Top-level computations
# ----------------------------------------------------------------------

def compute_s(n, progress=None):
    """Exact s_n via (*): per(M) = s_n * i^m * sqrt(n)."""
    N = 4 * n
    m = (n - 1) // 2
    sanity_sqrt_float(n)
    Phi = cyclotomic(N)
    P = ryser_perm_groupring(sin_entry_vecs(n), m, N, progress)
    B = cyc_mul_naive(xpow(n * m, N), sqrt_elem(n), N)     # i^m * sqrt(n)
    return solve_scalar(P, B, Phi)

def compute_sprime(p, progress=None):
    """Exact s'_p via (**): per(U) = s'_p * p^{m-1} * sqrt(p) * i^{-m}."""
    N = 4 * p
    m = (p - 1) // 2
    sanity_sqrt_float(p)
    Phi = cyclotomic(N)
    U = csc_entry_vecs(p, Phi)
    P = ryser_perm_groupring(U, m, N, progress)
    B = cyc_mul_naive(xpow((-p * m) % N, N), sqrt_elem(p), N)  # i^{-m} sqrt(p)
    B = [p ** (m - 1) * c for c in B]
    return solve_scalar(P, B, Phi)

# ----------------------------------------------------------------------
# Expected values
# ----------------------------------------------------------------------

# transcribed by ME from MY OWN PyMuPDF extraction of sun-permanents.pdf
SUN_S  = {3: 1, 5: -1, 7: 1, 9: 9, 11: 1, 13: 51, 15: 45, 17: -239,
          19: 913, 21: 2835, 23: 12145}
SUN_SP = {3: 1, 5: 1, 7: -6, 11: 111, 13: 261, 17: 6784, 19: 245101,
          23: -7094142}

# the attack's claims under verification (from kill-certificate.json)
CLAIM_S  = {25: 63125, 27: 59049, 29: 1053859, 31: 10542977, 33: -1643895,
            35: 334186125, 37: 1519663259, 41: 5574476521}
CLAIM_SP = {29: -4806838304, 31: -1518806869720, 37: 43041655439377}

def is_prime(x):
    if x < 2: return False
    for d in range(2, int(x ** .5) + 1):
        if x % d == 0: return False
    return True

def selftest():
    log("== SELF-TESTS: Kronecker-Ryser engine vs brute-force permanent ==")
    for n in (5, 9, 13, 15, 17):
        N, m = 4 * n, (n - 1) // 2
        ev = sin_entry_vecs(n)
        a = ryser_perm_groupring(ev, m, N)
        b = perm_bruteforce(ev, m, N)
        assert a == b, f"sin engine mismatch n={n}"
        log(f"   sin n={n}: Ryser==brute-force OK")
    for p in (5, 7, 11, 13):
        N, m = 4 * p, (p - 1) // 2
        Phi = cyclotomic(N)
        ev = csc_entry_vecs(p, Phi)
        a = ryser_perm_groupring(ev, m, N)
        b = perm_bruteforce(ev, m, N)
        assert a == b, f"csc engine mismatch p={p}"
        log(f"   csc p={p}: Ryser==brute-force OK")
    log("   self-tests PASSED")

def main():
    t00 = time.time()
    log("INDEPENDENT CLEAN-ROOM CHECKER -- Sun Conjecture 4.6 (arXiv:2108.07723v7)")
    log("Method: exact Z[x]/(x^4n - 1) arithmetic, Kronecker-substitution Ryser,")
    log("        Gauss-sum sqrt, verification mod Phi_4n(x). No floats/finite fields.")
    log("")
    selftest()
    log("")
    failures = []
    results_s, results_sp = {}, {}

    log("== s_n (sin) : exact values ==")
    for n in sorted(set(SUN_S) | set(CLAIM_S)):
        if n > int(sys.argv[1]) if len(sys.argv) > 1 else n > 35:
            continue
        t0 = time.time()
        val = compute_s(n, progress=200000)
        results_s[n] = val
        fl = s_float(n)
        src = []
        ok = True
        if n in SUN_S:
            ok &= (val == SUN_S[n]); src.append(f"Sun:{SUN_S[n]}")
        if n in CLAIM_S:
            ok &= (val == CLAIM_S[n]); src.append(f"claim:{CLAIM_S[n]}")
        relerr = abs(fl - val) / max(1, abs(val))
        status = "PASS" if ok and relerr < 1e-4 else "FAIL"
        if status == "FAIL": failures.append(("s", n, val))
        log(f"   s_{n} = {val}   [{', '.join(src) or 'fresh'}; float~{fl:.6g}, "
            f"relerr {relerr:.1e}] {time.time()-t0:.1f}s  {status}")

    log("")
    log("== s'_p (csc) : exact values ==")
    for p in sorted(set(SUN_SP) | set(CLAIM_SP)):
        if p > (int(sys.argv[1]) if len(sys.argv) > 1 else 31):
            continue
        t0 = time.time()
        val = compute_sprime(p, progress=200000)
        results_sp[p] = val
        fl = sprime_float(p)
        src = []
        ok = True
        if p in SUN_SP:
            ok &= (val == SUN_SP[p]); src.append(f"Sun:{SUN_SP[p]}")
        if p in CLAIM_SP:
            ok &= (val == CLAIM_SP[p]); src.append(f"claim:{CLAIM_SP[p]}")
        relerr = abs(fl - val) / max(1, abs(val))
        status = "PASS" if ok and relerr < 1e-4 else "FAIL"
        if status == "FAIL": failures.append(("s'", p, val))
        log(f"   s'_{p} = {val}   [{', '.join(src) or 'fresh'}; float~{fl:.6g}, "
            f"relerr {relerr:.1e}] {time.time()-t0:.1f}s  {status}")

    log("")
    log("== Proven congruences (Thm 1.6(iii)) as internal consistency check ==")
    for p, v in results_s.items():
        if is_prime(p):
            want = (-1) ** ((p + 1) // 2) % p
            got = v % p
            log(f"   s_{p} mod {p} = {got}, expected {want}  "
                f"{'OK' if got == want else 'VIOLATION'}")
            if got != want: failures.append(("cong s", p, v))
    for p, v in results_sp.items():
        got = v % p
        log(f"   s'_{p} mod {p} = {got}, expected 1  "
            f"{'OK' if got == 1 else 'VIOLATION'}")
        if got != 1: failures.append(("cong s'", p, v))

    log("")
    log("== Conjecture 4.6 evaluated on independently computed values ==")
    log("   (i) odd composite n => s_n == 0 (mod n):")
    for n, v in results_s.items():
        if n > 1 and not is_prime(n):
            ok = v % n == 0
            log(f"      n={n}: s_n mod n = {v % n}  {'holds' if ok else 'FAILS'}")
    log("   (ii) s_p < 0  <=>  p == 5 (mod 12):")
    viol = []
    for p, v in results_s.items():
        if is_prime(p):
            lhs, rhs = (v < 0), (p % 12 == 5)
            mark = "ok" if lhs == rhs else "**VIOLATED**"
            log(f"      p={p}: s_p={v} ({'neg' if lhs else 'pos'}), "
                f"p mod 12 = {p % 12}  -> {mark}")
            if lhs != rhs: viol.append(("s", p, v))
    log("   (ii) s'_p < 0  <=>  p == 7 (mod 8):")
    for p, v in results_sp.items():
        lhs, rhs = (v < 0), (p % 8 == 7)
        mark = "ok" if lhs == rhs else "**VIOLATED**"
        log(f"      p={p}: s'_p={v} ({'neg' if lhs else 'pos'}), "
            f"p mod 8 = {p % 8}  -> {mark}")
        if lhs != rhs: viol.append(("s'", p, v))

    log("")
    if failures:
        log(f"CHECKER FAILURES: {failures}")
    else:
        log("ALL CHECKS PASSED (engine self-tests, Sun's 19 published values, "
            "claimed values, proven congruences, float sanity).")
    if viol:
        log(f"CONJECTURE 4.6(ii) VIOLATIONS CONFIRMED at: "
            f"{[(s, p) for s, p, _ in viol]}")
        log("=> Conjecture 4.6(ii) is FALSE; hence Conjecture 4.6 "
            "(conjunction of (i) and (ii)) is FALSE.")
    log(f"total time {time.time()-t00:.1f}s")

    with open(sys.path[0] + "/independent_checker.log", "w", encoding="utf-8") as f:
        f.write("\n".join(LOG_LINES) + "\n")
    with open(sys.path[0] + "/independent_results.json", "w", encoding="utf-8") as f:
        json.dump({"s": results_s, "s_prime": results_sp,
                   "violations": [(s, p, str(v)) for s, p, v in viol],
                   "failures": [(a, b, str(c)) for a, b, c in failures]},
                  f, indent=1)
    return 1 if failures else 0

if __name__ == "__main__":
    sys.exit(main())
