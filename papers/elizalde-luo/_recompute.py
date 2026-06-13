# _recompute.py — clean-room recomputation of the small-n numbers quoted in note.tex.
#
# Implements the literal pattern-containment definition (biconditional convention)
# straight from Elizalde-Luo and re-derives, independently of the proof drafts and
# of the project's enumerators:
#   [R1] avoider counts over ALL words of [n]_2 for n<=5 (literal definition only),
#        nonnesting totals = n! * Catalan(n);
#   [R2] the fast nonnesting test (FIFO, Lemma 2.1 of the note) and the fast
#        {1132,3312}-avoidance criterion (Corollary 2.4) agree with the literal
#        definition on every word of [n]_2 for n<=5 (113,400 words at n=5);
#   [R3] Theorem A (note Thm 4.1): predicted avoider <=> actual avoider for every
#        (Dyck shape, permutation) pair, n<=6 in this script (n=7 via --n7 flag);
#   [R4] shape classification: condition (C) is satisfiable iff the shape is
#        canonical (S/I/II), and the number of valid sign words equals 2^{|F(s)|},
#        checked per-shape by brute force over all 2^{n-1} sign words for n<=9;
#        summing the formula over canonical shapes = 3^n - 3*2^{n-1} + 1 for n<=12;
#   [R5] tail counts f(m,h): closed forms vs direct DP for m<=39;
#   [R6] the summation identity of Section 5 as an exact integer identity, n<=60;
#   [R7] |W_n| = 3^n - 3*2^{n-1} + 1 by brute enumeration of the cube, n<=10,
#        and bullet-predicate == complement description (X1 u X2) on every string;
#   [R8] the bijection Phi: on every valid (s,eps) for n<=8: image in W_n,
#        injective, image = W_n, Psi(Phi(s,eps)) = (s,eps); and the rebuilt words
#        are exactly the avoiders (criterion-checked) for n<=6;
#   [R9] the worked examples in the note (the 16 codes at n=3; the shape
#        UUDUDD; the n=6 example CBCCAC <-> 234523145616).
#
# Usage:  python _recompute.py          (R1-R9; ~15 s under CPython 3.11 on a
#                                         2026 desktop, longer on older Pythons)
#         python _recompute.py --n7    (R3 at n=7: all 2,162,160 pairs, ~5 s)
#
# Every check prints PASS/FAIL; exit code 0 iff all pass.

import sys
import itertools
from math import comb, factorial

FAILURES = []


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ((" — " + detail) if detail else ""))
    if not ok:
        FAILURES.append(name)


def catalan(n):
    return comb(2 * n, n) // (n + 1)


# ---------------------------------------------------------------- literal layer

def literal_contains(w, pat):
    """Biconditional containment: positions i1<...<ik with order AND equality
    relations matching pat exactly (Elizalde-Luo convention)."""
    k = len(pat)
    L = len(w)
    for idx in itertools.combinations(range(L), k):
        good = True
        for r in range(k):
            wr, pr = w[idx[r]], pat[r]
            for s in range(r + 1, k):
                ws, ps = w[idx[s]], pat[s]
                if (wr < ws) != (pr < ps) or (wr == ws) != (pr == ps):
                    good = False
                    break
            if not good:
                break
        if good:
            return True
    return False


def all_words(n):
    """All permutations of the multiset {1,1,...,n,n}, generated recursively."""
    counts = [2] * (n + 1)  # counts[v] for v in 1..n
    word = []
    L = 2 * n

    def rec():
        if len(word) == L:
            yield tuple(word)
            return
        for v in range(1, n + 1):
            if counts[v]:
                counts[v] -= 1
                word.append(v)
                yield from rec()
                word.pop()
                counts[v] += 1

    yield from rec()


def literal_nonnesting(w):
    return not literal_contains(w, (1, 2, 2, 1)) and not literal_contains(w, (2, 1, 1, 2))


def literal_avoider(w):
    return (literal_nonnesting(w)
            and not literal_contains(w, (1, 1, 3, 2))
            and not literal_contains(w, (3, 3, 1, 2)))


# ------------------------------------------------------------------ fast layer

def fast_nonnesting(w):
    """FIFO: the i-th closer carries the letter of the i-th opener (Lemma 2.1)."""
    seen = set()
    openers, closers = [], []
    for c in w:
        if c in seen:
            closers.append(c)
        else:
            seen.add(c)
            openers.append(c)
    return openers == closers


def fast_avoider_given_nonnesting(w):
    """Criterion of Lemma 2.3: no triple snd(v) < x < y with w_y strictly between
    v and w_x.  Equivalent O(L^2) form with running min/max of closed values."""
    L = len(w)
    seen = set()
    closed_min, closed_max = None, None  # over values v with snd(v) < x
    snd = {}
    for i, c in enumerate(w):
        if c in seen:
            snd[c] = i
        else:
            seen.add(c)
    for x in range(L):
        # update closed set: values v with snd(v) < x
        if x > 0:
            v = w[x - 1]
            if snd[v] == x - 1:
                if closed_min is None or v < closed_min:
                    closed_min = v
                if closed_max is None or v > closed_max:
                    closed_max = v
        if closed_min is None:
            continue
        wx = w[x]
        for y in range(x + 1, L):
            wy = w[y]
            if wy < wx and closed_min < wy:
                return False  # some v < w_y < w_x with snd(v) < x : contains 1132
            if wy > wx and closed_max > wy:
                return False  # some v > w_y > w_x with snd(v) < x : contains 3312
    return True


# ----------------------------------------------------------------- shape layer

def dyck_paths(n):
    """All Dyck words as tuples of 1 (U) and 0 (D)."""
    path = []

    def rec(u, d):
        if u == n and d == n:
            yield tuple(path)
            return
        if u < n:
            path.append(1)
            yield from rec(u + 1, d)
            path.pop()
        if d < u:
            path.append(0)
            yield from rec(u, d + 1)
            path.pop()

    yield from rec(0, 0)


def shape_data(s):
    """openers o[i], closers q[i] (1-based arcs, 0-based positions)."""
    o = [i for i, c in enumerate(s) if c == 1]
    q = [i for i, c in enumerate(s) if c == 0]
    return o, q


def constraint_pairs(s):
    """Pairs (K,J), K<J, with q_1 < o_J < q_K  (arcs 1-based) — condition (C)."""
    o, q = shape_data(s)
    n = len(o)
    pairs = []
    for J in range(2, n + 1):
        oJ = o[J - 1]
        if oJ < q[0]:
            continue  # not late
        for K in range(2, J):
            if oJ < q[K - 1]:
                pairs.append((K, J))
    return pairs


def word_from(s, p):
    """Interleave: letter p_i at the i-th U and the i-th D."""
    w = []
    iu = ic = 0
    for c in s:
        if c == 1:
            w.append(p[iu]); iu += 1
        else:
            w.append(p[ic]); ic += 1
    return tuple(w)


def eps_of(p):
    """Sign word of a prefix-interval permutation, or None.
    eps[j] for arc j (2..n), stored at index j-2; 'H' or 'L'."""
    lo = hi = p[0]
    eps = []
    for x in p[1:]:
        if x == lo - 1:
            eps.append('L'); lo = x
        elif x == hi + 1:
            eps.append('H'); hi = x
        else:
            return None
    return eps


def p_of_eps(eps, n):
    """Inverse of eps_of: p_1 = 1 + #L, then min-1 / max+1."""
    p1 = 1 + sum(1 for e in eps if e == 'L')
    p = [p1]
    lo = hi = p1
    for e in eps:
        if e == 'L':
            lo -= 1; p.append(lo)
        else:
            hi += 1; p.append(hi)
    return tuple(p)


def predicted_avoider(s, p):
    """Theorem A: p prefix-interval and eps_K != eps_J for every pair in (C)."""
    eps = eps_of(p)
    if eps is None:
        return False
    for (K, J) in constraint_pairs(s):
        if eps[K - 2] == eps[J - 2]:
            return False
    return True


# --------------------------------------------------- classification (S/I/II)

def classify(s):
    """Parse s into (S), (I) a,delta, or (II) a,i,delta; None if not canonical.
    delta = dict {tail arc j: start height}; returns (case, a, i, delta, |F|)."""
    n = sum(s)
    o, q = shape_data(s)
    a = 0
    while a < n and s[a] == 1:
        a += 1
    # gap openers: openers strictly between q_1 and q_a
    gap = [j + 1 for j in range(n) if q[0] < o[j] < q[a - 1]]
    # tail openers: openers > q_a, with start heights
    heights = []
    h = 0
    pre = []
    for pos, c in enumerate(s):
        pre.append(h)
        h += 1 if c == 1 else -1
    tail = [(j + 1, pre[o[j]]) for j in range(n) if o[j] > q[a - 1]]
    if len(gap) > 1 or any(d > 1 for (_, d) in tail):
        return None
    delta = {j: d for (j, d) in tail}
    if a == n:
        return ('S', a, None, delta, n - 1)
    if not gap:
        # case I: tail arcs a+1..n, delta_{a+1} = 0
        assert delta.get(a + 1) == 0
        nfree = a + sum(1 for j, d in delta.items() if j >= a + 2 and d == 0)
        return ('I', a, None, delta, nfree)
    B = gap[0]
    assert B == a + 1
    i = sum(1 for qq in q if qq < o[B - 1])
    assert 1 <= i <= a - 1
    nfree = i + sum(1 for j, d in delta.items() if j >= a + 2 and d == 0)
    return ('II', a, i, delta, nfree)


def valid_eps_count_brute(s, n):
    cnt = 0
    for bits in itertools.product('LH', repeat=n - 1):
        ok = True
        for (K, J) in constraint_pairs(s):
            if bits[K - 2] == bits[J - 2]:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt


# ------------------------------------------------------------- bijection layer

def in_Wn(sig):
    """Bullet predicate for W_n over alphabet 'A','B','C'."""
    if 'C' not in sig:
        return sig[0] == 'A'
    if sig[0] == 'C':
        for r in range(1, len(sig)):
            if sig[r] == 'C':
                for t in range(r + 1, len(sig)):
                    if sig[t] != 'C':
                        return True
        return False
    return True


def in_Wn_complement(sig):
    """Complement description: not in X1 = B{A,B}^{n-1} and not in X2 = C v C^k."""
    n = len(sig)
    x1 = sig[0] == 'B' and all(c in 'AB' for c in sig)
    x2 = False
    if sig[0] == 'C':
        rest = sig[1:]
        # rest must be in {A,B}* C*
        seen_c = False
        ok = True
        for c in rest:
            if c == 'C':
                seen_c = True
            elif seen_c:
                ok = False
                break
        x2 = ok
    return not x1 and not x2


def phi(s, eps, n):
    """Encode admissible shape + valid sign word as sigma in {A,B,C}^n."""
    cls = classify(s)
    assert cls is not None
    case, a, i, delta, _ = cls
    ell = {'L': 'A', 'H': 'B'}
    sig = [None] * n
    if case == 'S':
        sig[0] = 'A'
        for j in range(2, n + 1):
            sig[j - 1] = ell[eps[j - 2]]
    elif case == 'I':
        for j in range(1, a + 1):
            sig[j - 1] = ell[eps[(j + 1) - 2]]  # one-slot shift
        sig[a] = 'C'
        for j in range(a + 2, n + 1):
            sig[j - 1] = 'C' if delta[j] == 1 else ell[eps[j - 2]]
    else:
        sig[0] = 'C'
        for j in range(2, i + 1):
            sig[j - 1] = ell[eps[j - 2]]
        for j in range(i + 1, a + 1):
            sig[j - 1] = 'C'
        sig[a] = ell[eps[(a + 1) - 2]]
        for j in range(a + 2, n + 1):
            sig[j - 1] = 'C' if delta[j] == 1 else ell[eps[j - 2]]
    return ''.join(sig)


def rebuild_shape(case, a, i, delta, n):
    """Rebuild the Dyck word from classification parameters (Lemma 6.1 converse)."""
    s = [1] * a
    if case == 'S':
        return tuple(s + [0] * a)
    if case == 'I':
        s += [0] * a
        h = 0
        start = a + 1
    else:
        s += [0] * i + [1] + [0] * (a - i)
        h = 1
        start = a + 2
    for j in range(start, n + 1):
        d = delta[j]
        s += [0] * (h - d) + [1]
        h = d + 1
    s += [0] * h
    return tuple(s)


def psi(sig):
    """Parse sigma in W_n back to (case, a, i, delta, eps)."""
    n = len(sig)
    linv = {'A': 'L', 'B': 'H'}
    eps = [None] * (n - 1)  # eps[j-2] for arc j

    def parse_tail(start_arc, prev_known):
        delta = {}
        for j in range(start_arc, n + 1):
            if sig[j - 1] == 'C':
                delta[j] = 1
                eps[j - 2] = 'L' if eps[j - 3] == 'H' else 'H'
            else:
                delta[j] = 0
                eps[j - 2] = linv[sig[j - 1]]
        return delta

    if 'C' not in sig:
        for j in range(2, n + 1):
            eps[j - 2] = linv[sig[j - 1]]
        return ('S', n, None, {}, eps)
    if sig[0] != 'C':
        a = sig.index('C')  # position a+1 (1-based) = first C; a = 0-based index
        for j in range(1, a + 1):
            eps[(j + 1) - 2] = linv[sig[j - 1]]
        delta = {a + 1: 0}
        delta.update(parse_tail(a + 2, None))
        return ('I', a, None, delta, eps)
    # leading C
    i = 1
    while i + 1 <= n and sig[i] in 'AB':
        i += 1
    # positions 2..i are signs; position i+1 is C (must exist for sigma in W_n)
    a = i + 1
    while a + 1 <= n and sig[a] == 'C':
        a += 1
    # positions i+1..a are C; position a+1 is a sign letter
    for j in range(2, i + 1):
        eps[j - 2] = linv[sig[j - 1]]
    eps[(a + 1) - 2] = linv[sig[a]]
    bar = 'L' if eps[(a + 1) - 2] == 'H' else 'H'
    for j in range(i + 1, a + 1):
        eps[j - 2] = bar
    delta = parse_tail(a + 2, None)
    return ('II', a, i, delta, eps)


# ============================================================ the checks

def R1_R2():
    print("== R1/R2: literal definition, n<=5 ==")
    exp_nn = {1: 1, 2: 4, 3: 30, 4: 336, 5: 5040}
    exp_av = {1: 1, 2: 4, 3: 16, 4: 58, 5: 196}
    for n in range(1, 6):
        nn = av = words = 0
        mism_nn = mism_av = 0
        for w in all_words(n):
            words += 1
            lit_nn = literal_nonnesting(w)
            lit_pat = (not literal_contains(w, (1, 1, 3, 2))
                       and not literal_contains(w, (3, 3, 1, 2)))
            # R2 cross-checks on EVERY word (nonnesting or not):
            if fast_nonnesting(w) != lit_nn:
                mism_nn += 1
            if fast_avoider_given_nonnesting(w) != lit_pat:
                mism_av += 1
            if lit_nn:
                nn += 1
                if lit_pat:
                    av += 1
        check(f"R1 n={n}: nonnesting={nn} (= {n}!*Cat={factorial(n)*catalan(n)}), "
              f"avoiders={av} (formula {3**n - 3*2**(n-1) + 1})",
              nn == exp_nn[n] == factorial(n) * catalan(n)
              and av == exp_av[n] == 3**n - 3 * 2**(n - 1) + 1)
        check(f"R2 n={n}: fast tests == literal definition on all {words} words",
              mism_nn == 0 and mism_av == 0)


def R3(nmax=6):
    print(f"== R3: Theorem A on all (shape, permutation) pairs, n<={nmax} ==")
    for n in range(1, nmax + 1):
        pairs = mism = act = 0
        for s in dyck_paths(n):
            cp = constraint_pairs(s)
            for p in itertools.permutations(range(1, n + 1)):
                pairs += 1
                w = word_from(s, p)
                actual = fast_avoider_given_nonnesting(w)
                eps = eps_of(p)
                pred = eps is not None and all(eps[K - 2] != eps[J - 2] for (K, J) in cp)
                if pred != actual:
                    mism += 1
                if actual:
                    act += 1
        check(f"R3 n={n}: {pairs} pairs (= n!*Cat = {factorial(n)*catalan(n)}), "
              f"avoiders={act}, mismatches={mism}",
              mism == 0 and pairs == factorial(n) * catalan(n)
              and act == 3**n - 3 * 2**(n - 1) + 1)


def R4():
    print("== R4: classification + per-shape counts ==")
    for n in range(1, 10):
        bad = 0
        for s in dyck_paths(n):
            cls = classify(s)
            brute = valid_eps_count_brute(s, n)
            pred = 0 if cls is None else 2 ** cls[4]
            if brute != pred:
                bad += 1
        check(f"R4a n={n}: brute valid-eps count == 2^|F(s)| (0 if not canonical) "
              f"for all {catalan(n)} shapes", bad == 0)
    for n in range(1, 13):
        tot = 0
        nshapes = 0
        for s in dyck_paths(n):
            nshapes += 1
            cls = classify(s)
            if cls is not None:
                tot += 2 ** cls[4]
        check(f"R4b n={n}: sum over {nshapes} shapes of 2^|F| = "
              f"{tot} == formula {3**n - 3*2**(n-1) + 1}",
              tot == 3**n - 3 * 2**(n - 1) + 1 and nshapes == catalan(n))


def R5():
    print("== R5: tail counts f(m,h) ==")
    # DP from the recurrences
    f = {(0, 0): 1, (0, 1): 1, (0, 2): 1}
    ok = True
    for m in range(1, 40):
        f[(m, 0)] = 2 * f[(m - 1, 1)]
        f[(m, 2)] = None  # fill after f(m,1)
        f[(m, 1)] = f[(m, 0)] + f[(m - 1, 2)]
        f[(m, 2)] = f[(m, 1)]
        if f[(m, 1)] != 3**m:
            ok = False
        if f[(m, 0)] != (1 if m == 0 else 2 * 3 ** (m - 1)):
            ok = False
    # direct path enumeration for small m: paths from height h to 0, U-steps
    # start at height <= 1, weight 2^{#U-steps starting at height 0}
    def direct(m, h):
        if m == 0:
            return 1  # the path D^h (weight 1)
        tot = 0
        # first step: D (if h>0) or U (h<=1)
        if h > 0:
            tot += direct(m, h - 1)
        if h <= 1:
            tot += (2 if h == 0 else 1) * direct(m - 1, h + 1)
        return tot
    for m in range(0, 12):
        for h in (0, 1, 2):
            if direct(m, h) != f[(m, h)]:
                ok = False
    check("R5: f(m,1)=3^m, f(m,0)=2*3^(m-1) (m>=1), DP == direct enumeration", ok)


def R6():
    print("== R6: summation identity ==")
    ok = True
    for n in range(1, 61):
        lhs = 2 ** (n - 1)
        lhs += sum(2 ** a * 3 ** (n - 1 - a) for a in range(1, n))
        lhs += sum((2 ** a - 2) * 3 ** (n - 1 - a) for a in range(2, n))
        if lhs != 3**n - 3 * 2 ** (n - 1) + 1:
            ok = False
    check("R6: 2^(n-1) + sum_a 2^a 3^(n-1-a) + sum_a (2^a-2) 3^(n-1-a)"
          " == 3^n - 3*2^(n-1) + 1 for n<=60", ok)


def R7():
    print("== R7: the language W_n ==")
    for n in range(1, 11):
        cnt = 0
        mism = 0
        for sig in itertools.product('ABC', repeat=n):
            sg = ''.join(sig)
            b = in_Wn(sg)
            if b != in_Wn_complement(sg):
                mism += 1
            if b:
                cnt += 1
        check(f"R7 n={n}: |W_n| = {cnt} == {3**n - 3*2**(n-1) + 1}; "
              f"predicate==complement on all {3**n} strings",
              cnt == 3**n - 3 * 2 ** (n - 1) + 1 and mism == 0)


def R8():
    print("== R8: the bijection Phi ==")
    for n in range(1, 9):
        images = {}
        bad_member = bad_round = 0
        for s in dyck_paths(n):
            cls = classify(s)
            if cls is None:
                continue
            for bits in itertools.product('LH', repeat=n - 1):
                eps = list(bits)
                ok = all(eps[K - 2] != eps[J - 2] for (K, J) in constraint_pairs(s))
                if not ok:
                    continue
                sig = phi(s, eps, n)
                if not in_Wn(sig):
                    bad_member += 1
                if sig in images:
                    bad_member += 1  # injectivity failure
                images[sig] = (s, tuple(eps))
                # round trip
                case2, a2, i2, delta2, eps2 = psi(sig)
                s2 = rebuild_shape(case2, a2, i2, delta2, n)
                if s2 != s or (n > 1 and list(eps2) != eps):
                    bad_round += 1
        Wn = {''.join(t) for t in itertools.product('ABC', repeat=n) if in_Wn(''.join(t))}
        check(f"R8 n={n}: Phi injective into W_n, image = W_n "
              f"({len(images)} = {len(Wn)}), Psi o Phi = id",
              bad_member == 0 and bad_round == 0 and set(images) == Wn)
    # word-level: rebuilt words from W_n == criterion-checked avoider set, n<=6
    for n in range(1, 7):
        avoiders = set()
        for s in dyck_paths(n):
            for p in itertools.permutations(range(1, n + 1)):
                w = word_from(s, p)
                if fast_avoider_given_nonnesting(w):
                    avoiders.add(w)
        rebuilt = set()
        for sig in itertools.product('ABC', repeat=n):
            sg = ''.join(sig)
            if not in_Wn(sg):
                continue
            case, a, i, delta, eps = psi(sg)
            s = rebuild_shape(case, a, i, delta, n)
            p = p_of_eps(eps if n > 1 else [], n)
            rebuilt.add(word_from(s, p))
        check(f"R8w n={n}: words rebuilt from W_n == avoider set ({len(avoiders)})",
              rebuilt == avoiders and len(avoiders) == 3**n - 3 * 2 ** (n - 1) + 1)


def R9():
    print("== R9: worked examples (n=3 and n=6) ==")
    table = {
        'AAA': '321321', 'AAB': '213213', 'AAC': '323211', 'ABA': '231231',
        'ABB': '123123', 'ABC': '212133', 'ACA': '332211', 'ACB': '221133',
        'ACC': '221313', 'BAC': '232311', 'BBC': '121233', 'BCA': '223311',
        'BCB': '112233', 'BCC': '223131', 'CCA': '232131', 'CCB': '212313',
    }
    ok = True
    for sg, expect in table.items():
        case, a, i, delta, eps = psi(sg)
        s = rebuild_shape(case, a, i, delta, 3)
        p = p_of_eps(eps, 3)
        w = ''.join(map(str, word_from(s, p)))
        if w != expect or not literal_avoider(tuple(map(int, w))):
            ok = False
            print(f"   mismatch {sg}: got {w}, expected {expect}")
    check("R9: all 16 codes of the n=3 table decode to the stated avoiders", ok)
    # shape UUDUDD: avoiders among the 6 label permutations are exactly 212313, 232131
    s = (1, 1, 0, 1, 0, 0)
    got = sorted(''.join(map(str, word_from(s, p)))
                 for p in itertools.permutations((1, 2, 3))
                 if literal_avoider(word_from(s, p)))
    check("R9: shape UUDUDD has exactly the avoiders 212313, 232131",
          got == ['212313', '232131'])
    # n=6 case (II) example: sigma = CBCCAC <-> w = 234523145616
    case, a, i, delta, eps = psi('CBCCAC')
    s6 = rebuild_shape(case, a, i, delta, 6)
    p6 = p_of_eps(eps, 6)
    w6 = rebuild = ''.join(map(str, word_from(s6, p6)))
    ok6 = (w6 == '234523145616'
           and literal_avoider(tuple(map(int, w6)))
           and (case, a, i) == ('II', 4, 2) and delta == {6: 1}
           and ''.join('UD'[1 - c] for c in s6) == 'UUUUDDUDDUDD'
           and p6 == (2, 3, 4, 5, 1, 6)
           and phi(s6, list(eps), 6) == 'CBCCAC')
    check("R9: code CBCCAC decodes to the avoider 234523145616 "
          "(shape UUUUDDUDDUDD, p = 234516) and re-encodes", ok6)


def main():
    if '--n7' in sys.argv:
        R3(nmax=7)
    else:
        R1_R2()
        R3(nmax=6)
        R4()
        R5()
        R6()
        R7()
        R8()
        R9()
    print()
    if FAILURES:
        print("OVERALL: FAILURES:", FAILURES)
        sys.exit(1)
    print("OVERALL: ALL CHECKS PASS")
    sys.exit(0)


if __name__ == '__main__':
    main()
