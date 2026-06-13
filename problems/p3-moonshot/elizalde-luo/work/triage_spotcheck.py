# Clean-room triage spot-check (written from the draft STATEMENTS, not project code).
# Checks:
#  S1: literal biconditional containment vs fast criteria (Lemma 1) and FIFO (Lemma 0), small n
#  S2: Theorem A predicate == brute avoidance over ALL (s,p) pairs, n<=7
#  S3: Lemma B per-shape formula (recurrence-structural / dyck-sign) vs eps-brute, sum vs formula, n<=10
#  S4: bijection.md Phi: well-defined, injective, image == W_n, |W_n| == formula, n<=7
import itertools, sys

def multiset_words(n):
    base = []
    for v in range(1, n + 1):
        base += [v, v]
    return set(itertools.permutations(base))

def contains_literal(w, pat):
    k = len(pat)
    for idx in itertools.combinations(range(len(w)), k):
        ok = True
        for r in range(k):
            for s in range(r + 1, k):
                a, b = w[idx[r]], w[idx[s]]
                if ((a < b) != (pat[r] < pat[s])) or ((a == b) != (pat[r] == pat[s])):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False

def snd_positions(w):
    seen, snd = {}, {}
    for i, v in enumerate(w):
        if v in seen:
            snd[v] = i
        else:
            seen[v] = i
    return snd

def fast_1132(w):
    snd = snd_positions(w)
    for a, s in snd.items():
        m = -1
        for x in w[s + 1:]:
            if x > a:
                if m > x:
                    return True
                if x > m:
                    m = x
    return False

def fast_3312(w):
    snd = snd_positions(w)
    big = 10 ** 9
    for a, s in snd.items():
        m = big
        for x in w[s + 1:]:
            if x < a:
                if m < x:
                    return True
                if x < m:
                    m = x
    return False

def fifo_nonnesting(w):
    openers, closers, seen = [], [], set()
    for v in w:
        if v in seen:
            closers.append(v)
        else:
            seen.add(v)
            openers.append(v)
    return openers == closers

def dyck_words(n):
    res = []
    def rec(s, u, d):
        if u == n and d == n:
            res.append(s); return
        if u < n:
            rec(s + 'U', u + 1, d)
        if d < u:
            rec(s + 'D', u, d + 1)
    rec('', 0, 0)
    return res

def arcs(s):
    o, q = [], []
    for i, ch in enumerate(s):
        (o if ch == 'U' else q).append(i)
    return o, q

def word_from(s, p):
    w = []
    ui = di = 0
    for ch in s:
        if ch == 'U':
            w.append(p[ui]); ui += 1
        else:
            w.append(p[di]); di += 1
    return tuple(w)

def sign_word(p):
    eps = []
    lo = hi = p[0]
    for x in p[1:]:
        if x == hi + 1:
            eps.append('H'); hi = x
        elif x == lo - 1:
            eps.append('L'); lo = x
        else:
            return None
    return eps  # eps[j-2] is sign of arc j (1-based, j>=2)

def thmA_pred(s, p, o, q):
    eps = sign_word(p)
    if eps is None:
        return False
    n = len(p)
    q1 = q[0]
    for J in range(n):          # 0-based arc J -> arc J+1
        if o[J] > q1:           # late
            for K in range(J):
                if o[K] < o[J] < q[K]:
                    assert K >= 1, "arc 1 open at late opener?!"
                    if eps[K - 1] == eps[J - 1]:
                        return False
    return True

def classify_shape(s, n, o, q):
    h = 0
    hb = []  # height before each opener
    for ch in s:
        if ch == 'U':
            hb.append(h); h += 1
        else:
            h -= 1
    a = 0
    while a < n and s[a] == 'U':
        a += 1
    qa = q[a - 1]
    gap = [j for j in range(n) if q[0] < o[j] < qa]
    tail = [j for j in range(n) if o[j] > qa]
    delta = {j: hb[j] for j in tail}
    if a == n:
        return ('S',)
    if any(delta[j] >= 2 for j in tail):
        return None
    if len(gap) == 0:
        return ('I', a, delta)
    if len(gap) == 1:
        B = gap[0]
        i_cl = sum(1 for t in q if t < o[B])
        return ('II', a, i_cl, delta)
    return None

def lemmaB_count(s, n, o, q):
    cls = classify_shape(s, n, o, q)
    if cls is None:
        return 0
    if cls[0] == 'S':
        return 2 ** (n - 1)
    if cls[0] == 'I':
        a, delta = cls[1], cls[2]
        u0 = sum(1 for j in delta if delta[j] == 0)
        # delta includes arc a+1 (0-based a) whose height is 0; the formula's u0(T)
        # counts ALL tail U-steps from height 0, including that one -> 2^{(a-1)+u0}
        return 2 ** (a - 1 + u0)
    a, i_cl, delta = cls[1], cls[2], cls[3]
    u0 = sum(1 for j in delta if delta[j] == 0)
    return 2 ** (i_cl + u0)

def eps_brute_count(s, n, o, q):
    cnt = 0
    for bits in itertools.product('LH', repeat=n - 1):
        ok = True
        q1 = q[0]
        for J in range(n):
            if o[J] > q1:
                for K in range(J):
                    if o[K] < o[J] < q[K]:
                        if bits[K - 1] == bits[J - 1]:
                            ok = False; break
                if not ok:
                    break
        cnt += ok
    return cnt

def Phi(s, p, n, o, q):
    eps = sign_word(p)
    cls = classify_shape(s, n, o, q)
    assert eps is not None and cls is not None
    L = {'L': 'A', 'H': 'B'}
    sig = [None] * n
    if cls[0] == 'S':
        sig[0] = 'A'
        for j in range(2, n + 1):
            sig[j - 1] = L[eps[j - 2]]
    elif cls[0] == 'I':
        a = cls[1]; delta = cls[2]
        for j in range(1, a + 1):
            sig[j - 1] = L[eps[(j + 1) - 2]]
        sig[a] = 'C'
        for j in range(a + 2, n + 1):
            sig[j - 1] = 'C' if delta[j - 1] == 1 else L[eps[j - 2]]
    else:
        a, i_cl, delta = cls[1], cls[2], cls[3]
        sig[0] = 'C'
        for j in range(2, i_cl + 1):
            sig[j - 1] = L[eps[j - 2]]
        for j in range(i_cl + 1, a + 1):
            sig[j - 1] = 'C'
        sig[a] = L[eps[(a + 1) - 2]]
        for j in range(a + 2, n + 1):
            sig[j - 1] = 'C' if delta[j - 1] == 1 else L[eps[j - 2]]
    assert all(x is not None for x in sig)
    return ''.join(sig)

def in_W(sig):
    n = len(sig)
    if 'C' not in sig:
        return sig[0] == 'A'
    if sig[0] == 'C':
        for r in range(1, n):
            if sig[r] == 'C':
                for t in range(r + 1, n):
                    if sig[t] != 'C':
                        return True
        return False
    return True

def formula(n):
    return 3 ** n - 3 * 2 ** (n - 1) + 1

# ---------- S1 ----------
print("S1: literal vs fast, n<=4 all words; FIFO vs literal nonnesting")
for n in range(1, 5):
    for w in multiset_words(n):
        nn_lit = (not contains_literal(w, (1, 2, 2, 1))) and (not contains_literal(w, (2, 1, 1, 2)))
        assert nn_lit == fifo_nonnesting(w), (n, w)
        assert contains_literal(w, (1, 1, 3, 2)) == fast_1132(w), (n, w)
        assert contains_literal(w, (3, 3, 1, 2)) == fast_3312(w), (n, w)
    print(f"  n={n} OK")
print("S1b: literal vs fast on all NONNESTING words, n=5")
n = 5
cnt = 0
for s in dyck_words(n):
    for p in itertools.permutations(range(1, n + 1)):
        w = word_from(s, p)
        assert fifo_nonnesting(w)
        assert contains_literal(w, (1, 1, 3, 2)) == fast_1132(w), (s, p)
        assert contains_literal(w, (3, 3, 1, 2)) == fast_3312(w), (s, p)
        cnt += 1
print(f"  n=5 OK ({cnt} nonnesting words)")

# ---------- S2, S3, S4 ----------
NMAX_PAIRS = 7
for n in range(1, NMAX_PAIRS + 1):
    avoiders = set()
    mism = 0
    total = 0
    for s in dyck_words(n):
        o, q = arcs(s)
        for p in itertools.permutations(range(1, n + 1)):
            w = word_from(s, p)
            brute = (not fast_1132(w)) and (not fast_3312(w))
            pred = thmA_pred(s, p, o, q)
            if brute != pred:
                mism += 1
                if mism < 5:
                    print("  MISMATCH", n, s, p, brute, pred)
            if brute:
                avoiders.add((s, p))
            total += 1
    assert mism == 0, f"Theorem A mismatches at n={n}"
    assert len(avoiders) == formula(n), (n, len(avoiders), formula(n))
    print(f"S2 n={n}: Theorem A == brute on all {total} (s,p) pairs; count {len(avoiders)} == formula")

    # S4: bijection
    codes = {}
    for (s, p) in avoiders:
        o, q = arcs(s)
        sig = Phi(s, p, n, o, q)
        assert sig not in codes, ("Phi not injective", n, sig, codes[sig], (s, p))
        codes[sig] = (s, p)
        assert in_W(sig), ("Phi image not in W_n", n, sig, s, p)
    Wn = {''.join(t) for t in itertools.product('ABC', repeat=n) if in_W(''.join(t))}
    assert set(codes) == Wn, (n, len(codes), len(Wn))
    assert len(Wn) == formula(n)
    print(f"S4 n={n}: Phi injective, image == W_n ({len(Wn)} codes)")

print()
print("S3: Lemma B per-shape formula vs eps-brute; totals vs formula")
for n in range(1, 11):
    tot = 0
    for s in dyck_words(n):
        o, q = arcs(s)
        fb = lemmaB_count(s, n, o, q)
        if n <= 8:
            bb = eps_brute_count(s, n, o, q)
            assert fb == bb, (n, s, fb, bb)
        tot += fb
    assert tot == formula(n), (n, tot, formula(n))
    print(f"  n={n}: sum N(s) = {tot} == formula (per-shape brute check {'on' if n<=8 else 'off'})")

print("\nALL SPOT CHECKS PASSED")
