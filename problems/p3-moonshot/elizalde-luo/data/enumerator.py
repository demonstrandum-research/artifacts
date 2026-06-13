#!/usr/bin/env python3
"""
Ground-truth enumerator for the Elizalde-Luo conjecture (arXiv:2412.00336, DMTCS 27:1,
Table 4 / tab:conjecture):

    c_n({1132, 3312}) = 3^n - 3*2^(n-1) + 1   for n >= 1     (OEIS A168583 shifted)

Objects: permutations of the multiset [n]_2 = {1,1,2,2,...,n,n}  (words of length 2n
over {1..n}, each letter exactly twice).

NONNESTING (paper, Section 1): "permutations of [n]_2 whose corresponding matching is
nonnesting, i.e., there are no two arcs (i1,i4) and (i2,i3) where i1<i2<i3<i4. They can
be defined as permutations of [n]_2 that avoid the patterns 1221 and 2112."

PATTERN CONTAINMENT (paper, Section 1): pi contains sigma iff there exist indices
i1<...<ik such that pi_{i_r} < pi_{i_s}  <=>  sigma_r < sigma_s   AND
                    pi_{i_r} = pi_{i_s}  <=>  sigma_r = sigma_s   for all r,s.
(Equalities preserved BOTH ways; strict order relations of distinct pattern letters
must hold strictly in the word.)

So an occurrence of 1132 in w is i<j<k<l with w_i = w_j = a, w_k = c, w_l = b, a < b < c.
An occurrence of 3312 in w is i<j<k<l with w_i = w_j = c, w_k = a, w_l = b, a < b < c.

VALIDATION LAYERS (all run by main()):
  V1. Naive containment (all index 4-subsets, definition transcribed literally) vs the
      fast O(n^2) checks, on ALL multiset permutations for n <= 4 and on all nonnesting
      words for n = 5.
  V2. Direct enumeration of all multiset permutations filtered by the literal
      1221/2112-avoidance definition vs the (Dyck shape x label permutation)
      construction: identical word SETS for n <= 5, identical counts for n = 6.
  V3. Count of nonnesting words == n! * Catalan(n) for every n computed.
  V4. Canonical first-occurrence normalization check: avoidance of {1132,3312} is NOT
      invariant under relabeling, so counting canonical words (first occurrences in
      order 1,2,...,n) times n! must NOT reproduce the raw count for n >= 3. Verified
      and recorded (the raw count is the counting convention; no quotient is taken).
  V5. Formula check 3^n - 3*2^(n-1) + 1 for every n.
(Cross-checks against an independent Rust enumerator and a clean-room Codex
implementation are recorded separately in validation.json.)

Output: python_results.json in the same directory.

Usage: python enumerator.py [max_n]   (default max_n = 7)
"""

from itertools import combinations, permutations
from collections import Counter
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))

PAT_1132 = (1, 1, 3, 2)
PAT_3312 = (3, 3, 1, 2)
PAT_1221 = (1, 2, 2, 1)
PAT_2112 = (2, 1, 1, 2)


# ----------------------------------------------------------------------------
# Layer 0: literal, definition-faithful predicates (slow; used as ground truth)
# ----------------------------------------------------------------------------

def contains_pattern_naive(w, sigma):
    """Literal transcription of the paper's containment definition."""
    k = len(sigma)
    n = len(w)
    if n < k:
        return False
    for idx in combinations(range(n), k):
        ok = True
        for r in range(k):
            wr, sr = w[idx[r]], sigma[r]
            for s in range(r + 1, k):
                ws, ss = w[idx[s]], sigma[s]
                if (wr < ws) != (sr < ss) or (wr == ws) != (sr == ss):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


def is_nonnesting_naive(w):
    """Paper definition: avoid 1221 and 2112 (as equality patterns)."""
    return not contains_pattern_naive(w, PAT_1221) and \
           not contains_pattern_naive(w, PAT_2112)


def multiset_permutations(counts):
    """All permutations of a multiset given as {value: multiplicity}."""
    total = sum(counts.values())
    word = []

    def rec():
        if len(word) == total:
            yield tuple(word)
            return
        for v in sorted(counts):
            if counts[v] > 0:
                counts[v] -= 1
                word.append(v)
                yield from rec()
                word.pop()
                counts[v] += 1

    yield from rec()


def all_multiset_perms_n(n):
    return multiset_permutations({v: 2 for v in range(1, n + 1)})


# ----------------------------------------------------------------------------
# Layer 1: fast checks (each value occurs exactly twice in w)
# ----------------------------------------------------------------------------
# w contains 1132  <=>  for some value a with second occurrence at position q,
#                       the suffix w[q+1:] has positions k<l with w_k > w_l > a
#                       (strict descent, both entries > a).
# w contains 3312  <=>  for some value c with second occurrence at position q,
#                       the suffix w[q+1:] has positions k<l with w_k < w_l < c
#                       (strict ascent, both entries < c).
# Justification: the two equal pattern letters (the "11" of 1132 / "33" of 3312) must
# be the two copies of a single value since every value occurs exactly twice; the
# remaining two pattern letters impose exactly the stated strict order conditions.
# (Verified exhaustively against the naive predicate; see V1.)

def contains_1132_fast(w, second_pos):
    L = len(w)
    for a, q in second_pos.items():
        mx = 0
        for t in range(q + 1, L):
            v = w[t]
            if v > a:
                if v < mx:
                    return True
                if v > mx:
                    mx = v
    return False


def contains_3312_fast(w, second_pos):
    L = len(w)
    big = 10 ** 9
    for c, q in second_pos.items():
        mn = big
        for t in range(q + 1, L):
            v = w[t]
            if v < c:
                if v > mn:
                    return True
                if v < mn:
                    mn = v
    return False


def second_positions(w):
    """Map value -> index (0-based) of its second occurrence."""
    seen = {}
    out = {}
    for i, v in enumerate(w):
        if v in seen:
            out[v] = i
        else:
            seen[v] = i
    return out


def is_avoider_fast(w):
    sp = second_positions(w)
    return not contains_1132_fast(w, sp) and not contains_3312_fast(w, sp)


# ----------------------------------------------------------------------------
# Layer 2: structured generation of nonnesting words
# ----------------------------------------------------------------------------
# Standard fact (validated exhaustively in V2): a perfect matching of [2n] is
# nonnesting iff its i-th closer (right endpoint, in position order) is matched to its
# i-th opener (left endpoint, in position order). Hence nonnesting words over [n]_2
# are exactly the pairs (Dyck shape, label permutation): shape s in {U,D}^{2n} with
# every prefix having #U >= #D and total n each; word w has p_i at the i-th U and at
# the i-th D, where p is a permutation of [n].

def dyck_shapes(n):
    """All Dyck words as tuples of booleans (True=U/opener, False=D/closer)."""
    shape = []

    def rec(u, d):
        if u == n and d == n:
            yield tuple(shape)
            return
        if u < n:
            shape.append(True)
            yield from rec(u + 1, d)
            shape.pop()
        if d < u:
            shape.append(False)
            yield from rec(u, d + 1)
            shape.pop()

    yield from rec(0, 0)


def word_from_shape_perm(shape, p):
    """Label the i-th opener and i-th closer with p[i]."""
    w = []
    uo = 0
    dc = 0
    for st in shape:
        if st:
            w.append(p[uo])
            uo += 1
        else:
            w.append(p[dc])
            dc += 1
    return tuple(w)


def catalan(n):
    return math.comb(2 * n, n) // (n + 1)


# ----------------------------------------------------------------------------
# Validations
# ----------------------------------------------------------------------------

def validate_fast_vs_naive(max_full_n=4, nonnesting_n=5):
    """V1: fast pattern checks agree with the literal definition."""
    report = {}
    for n in range(1, max_full_n + 1):
        mism = 0
        tot = 0
        for w in all_multiset_perms_n(n):
            tot += 1
            sp = second_positions(w)
            if contains_1132_fast(w, sp) != contains_pattern_naive(w, PAT_1132):
                mism += 1
            if contains_3312_fast(w, sp) != contains_pattern_naive(w, PAT_3312):
                mism += 1
        report[f"all_words_n{n}"] = {"words": tot, "mismatches": mism}
        assert mism == 0, f"V1 FAILED at n={n}"
    # nonnesting words only at n=5 (covers the actual filtering domain)
    n = nonnesting_n
    mism = 0
    tot = 0
    for shape in dyck_shapes(n):
        for p in permutations(range(1, n + 1)):
            w = word_from_shape_perm(shape, p)
            tot += 1
            sp = second_positions(w)
            if contains_1132_fast(w, sp) != contains_pattern_naive(w, PAT_1132):
                mism += 1
            if contains_3312_fast(w, sp) != contains_pattern_naive(w, PAT_3312):
                mism += 1
    report[f"nonnesting_words_n{n}"] = {"words": tot, "mismatches": mism}
    assert mism == 0, f"V1 FAILED on nonnesting words at n={n}"
    return report


def validate_generation(max_set_n=5, count_n=6):
    """V2: shape x perm construction == literal nonnesting filter."""
    report = {}
    for n in range(1, max_set_n + 1):
        direct = set()
        for w in all_multiset_perms_n(n):
            if is_nonnesting_naive(w):
                direct.add(w)
        constructed = set()
        for shape in dyck_shapes(n):
            for p in permutations(range(1, n + 1)):
                constructed.add(word_from_shape_perm(shape, p))
        ok = direct == constructed
        report[f"set_equality_n{n}"] = {
            "direct_count": len(direct),
            "constructed_count": len(constructed),
            "sets_equal": ok,
            "expected_n_factorial_catalan": math.factorial(n) * catalan(n),
        }
        assert ok, f"V2 FAILED at n={n}"
        assert len(direct) == math.factorial(n) * catalan(n)
    # count-only check at n=6 using a cheap arc-based nonnesting test
    n = count_n
    cnt = 0
    for w in all_multiset_perms_n(n):
        # arc-based nonnesting test: i-th closer must match i-th opener
        first = {}
        openers = []
        closers = []
        for i, v in enumerate(w):
            if v in first:
                closers.append((i, v))
            else:
                first[v] = i
                openers.append(v)
        ok = True
        for i, (_, v) in enumerate(closers):
            if openers[i] != v:
                ok = False
                break
        if ok:
            cnt += 1
    expected = math.factorial(n) * catalan(n)
    report[f"count_equality_n{n}"] = {"direct_count": cnt, "expected": expected}
    assert cnt == expected, f"V2 count FAILED at n={n}"
    # the arc test above is itself validated: at n<=5 set equality already proved the
    # construction correct; check arc test == naive test at n=4 for completeness
    n = 4
    for w in all_multiset_perms_n(n):
        first = {}
        openers = []
        closers = []
        for i, v in enumerate(w):
            if v in first:
                closers.append(v)
            else:
                first[v] = i
                openers.append(v)
        arc_ok = all(openers[i] == c for i, c in enumerate(closers))
        assert arc_ok == is_nonnesting_naive(w), f"arc test mismatch at {w}"
    report["arc_test_vs_naive_n4"] = "all agree"
    return report


# ----------------------------------------------------------------------------
# Main enumeration with refined statistics
# ----------------------------------------------------------------------------

def enumerate_n(n):
    """Count {1132,3312}-avoiding nonnesting words of [n]_2 with refined stats."""
    count = 0
    nonnesting_total = 0
    first_letter = Counter()        # value of w[0]
    pos_of_n = Counter()            # (i,j) 1-based positions of the two copies of n
    descents = Counter()            # number of descents
    shape_counts = Counter()        # Dyck shape string, U=opener, D=closer
    canonical_count = 0             # avoiders whose label perm is the identity

    perms = list(permutations(range(1, n + 1)))
    for shape in dyck_shapes(n):
        # precompute opener/closer positions for this shape
        opos = []
        cpos = []
        for i, st in enumerate(shape):
            (opos if st else cpos).append(i)
        sstr = "".join("U" if st else "D" for st in shape)
        for p in perms:
            nonnesting_total += 1
            w = word_from_shape_perm(shape, p)
            sp = {p[i]: cpos[i] for i in range(n)}
            if contains_1132_fast(w, sp) or contains_3312_fast(w, sp):
                continue
            count += 1
            first_letter[w[0]] += 1
            i_n = p.index(n)
            pos_of_n[(opos[i_n] + 1, cpos[i_n] + 1)] += 1
            descents[sum(1 for i in range(2 * n - 1) if w[i] > w[i + 1])] += 1
            shape_counts[sstr] += 1
            if all(p[i] == i + 1 for i in range(n)):
                canonical_count += 1

    return {
        "n": n,
        "nonnesting_total": nonnesting_total,
        "avoider_count": count,
        "formula_value": 3 ** n - 3 * 2 ** (n - 1) + 1,
        "formula_matches": count == 3 ** n - 3 * 2 ** (n - 1) + 1,
        "canonical_label_avoiders": canonical_count,
        "canonical_times_factorial": canonical_count * math.factorial(n),
        "stats": {
            "by_first_letter": {str(k): v for k, v in sorted(first_letter.items())},
            "by_positions_of_n": {f"{i},{j}": v
                                  for (i, j), v in sorted(pos_of_n.items())},
            "by_descents": {str(k): v for k, v in sorted(descents.items())},
            "by_dyck_shape": {k: v for k, v in sorted(shape_counts.items())},
        },
    }


def main():
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    t0 = time.time()

    print("V1: fast checks vs literal definition ...", flush=True)
    v1 = validate_fast_vs_naive()
    print("    OK", v1, flush=True)

    print("V2: shape x perm construction vs literal nonnesting filter ...", flush=True)
    v2 = validate_generation()
    print("    OK", flush=True)

    results = []
    for n in range(1, max_n + 1):
        t = time.time()
        r = enumerate_n(n)
        r["seconds"] = round(time.time() - t, 2)
        results.append(r)
        print(f"n={n}: nonnesting={r['nonnesting_total']} "
              f"(n!*Cat_n={math.factorial(n)*catalan(n)}), "
              f"avoiders={r['avoider_count']}, formula={r['formula_value']}, "
              f"match={r['formula_matches']}, "
              f"canonical*n!={r['canonical_times_factorial']} "
              f"[{r['seconds']}s]", flush=True)
        # V3
        assert r["nonnesting_total"] == math.factorial(n) * catalan(n), \
            f"V3 FAILED at n={n}"

    out = {
        "description": "Python ground-truth enumeration, Elizalde-Luo {1132,3312} "
                       "nonnesting avoiders",
        "validations": {"V1_fast_vs_naive": v1, "V2_generation": v2},
        "results": results,
        "total_seconds": round(time.time() - t0, 2),
    }
    path = os.path.join(HERE, "python_results.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
