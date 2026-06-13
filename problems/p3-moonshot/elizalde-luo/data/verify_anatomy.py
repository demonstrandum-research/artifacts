#!/usr/bin/env python3
"""
Verify the ANATOMY DECOMPOSITION (Lemma chain 4-6 of the proof draft) numerically.

Objects (after Theorem 1): avoider = (Dyck shape s, eps in {M,m}^{n-1}) such that
every crossing pair (j1,j2), 2<=j1<j2, with o_{j2} > c_1, has eps_{j1} != eps_{j2}.
[Theorem 1 itself was verified separately in verify_theorem1.py]

Claimed anatomy (FIFO queue scan; arc i pushed at o_i, popped at c_i; arc 1
colorless, arcs 2..n colored eps_i):

  A1. a := length of first ascent run = #arcs opened before c_1. If a = n the shape
      is U^n D^n and eps is free: class size 2^{n-1}.
  A2. If a < n: arc a+1 opens after c_1. Let h1 := number of arcs still open just
      before o_{a+1} (queue length = #closers... = a-1 - (#pops after c_1 before
      o_{a+1})), 0 <= h1 <= a-1.  Legality forces: the h1 remnant arcs
      (arcs a-h1+1..a) all share one color x, and eps_{a+1} = opposite of x
      (if h1 >= 1; free if h1 = 0).
  A3. After o_{a+1}, the next h1 steps of the shape are forced pops; then a "walk"
      from height 1 with u = n-a-1 pushes (arcs a+2..n) and u+1 pops, where every
      push occurs at height 0 (color free) or height 1 (color = opposite of the
      unique open arc).
  A4. Encoding pushes of arcs a+2..n by symbols in {(0,M),(0,m),(1)} gives a
      bijection: class (a,h1) <-> {M,m}^{a-h1} x {3 symbols}^{n-a-1},
      so |class(a,h1)| = 2^{a-h1} * 3^{n-a-1}.

Checks here:
  C1. For n <= MAXN: every brute-force avoider (via is_avoider_fast on words) maps
      to valid data (a,h1,bits,symbols) with all claimed properties (mono remnant,
      forced colors, pushes at height <= 1, forced pops), and reconstruction gives
      back exactly (s,p).  [roundtrip injectivity on the avoider side]
  C2. Every data tuple (a,h1,bits,symbols) reconstructs to a word that is an
      avoider (checked by is_avoider_fast), and the map data->word is injective.
      [surjectivity + injectivity on the data side; together: bijection]
  C3. Class sizes match 2^{a-h1} * 3^{n-a-1} (a<n) and 2^{n-1} (a=n), and the
      total matches 3^n - 3*2^{n-1} + 1.
"""
import sys, os, json
from itertools import permutations, product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enumerator import dyck_shapes, word_from_shape_perm, is_avoider_fast

HERE = os.path.dirname(os.path.abspath(__file__))

def eps_of_perm(p):
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
    n = len(eps) + 1
    r = sum(1 for e in eps if e == 'm')
    p = [r + 1]; lo = hi = r + 1
    for e in eps:
        if e == 'M': hi += 1; p.append(hi)
        else:        lo -= 1; p.append(lo)
    return tuple(p)

OPP = {'M': 'm', 'm': 'M'}

def extract_data(shape, eps):
    """Avoider (shape, eps) -> (a, h1, bits, symbols) or raise AssertionError if
    any claimed structural property fails. bits in {M,m}^{a-h1}; symbols list of
    ('0','M'/'m') or ('1',)."""
    n = sum(1 for st in shape if st)
    # scan: queue of arc indices (1-based); arc i has color eps[i-2] for i>=2
    a = 0
    for st in shape:
        if st: a += 1
        else: break
    if a == n:
        return (n, None, tuple(eps), ())
    # find o_{a+1}: position of the (a+1)-th U
    ucount = 0
    pos_oa1 = None
    for t, st in enumerate(shape):
        if st:
            ucount += 1
            if ucount == a + 1:
                pos_oa1 = t
                break
    pops_before = sum(1 for t in range(pos_oa1) if not shape[t])
    assert pops_before >= 1, "first pop must precede o_{a+1}"
    h1 = a - pops_before          # queue length just before o_{a+1}
    assert 0 <= h1 <= a - 1
    # remnant arcs: indices a-h1+1 .. a ; their colors eps[i-2]
    remnant = [eps[i - 2] for i in range(a - h1 + 1, a + 1)]
    assert len(set(remnant)) <= 1, "remnant must be monochromatic"
    if h1 >= 1:
        x = remnant[0]
        assert eps[(a + 1) - 2] == OPP[x], "arc a+1 color must oppose remnant"
        bits = tuple(eps[i - 2] for i in range(2, a - h1 + 1)) + (x,)
    else:
        bits = tuple(eps[i - 2] for i in range(2, a + 1)) + (eps[(a + 1) - 2],)
    assert len(bits) == a - h1
    # after o_{a+1}: next h1 steps must be pops (forced)
    t = pos_oa1 + 1
    for k in range(h1):
        assert t < 2 * n and not shape[t], "h1 forced pops after o_{a+1}"
        t += 1
    # walk: starts at height 1 (open arcs: exactly arc a+1)
    height = 1
    open_arcs = [a + 1]           # FIFO
    symbols = []
    next_arc = a + 2
    while t < 2 * n:
        if shape[t]:  # push
            assert height <= 1, "walk push must be at height <= 1"
            col = eps[next_arc - 2]
            if height == 0:
                symbols.append(('0', col))
            else:
                assert col == OPP[eps[open_arcs[0] - 2]], \
                    "push at height 1 must oppose the open arc"
                symbols.append(('1',))
            open_arcs.append(next_arc)
            next_arc += 1
            height += 1
        else:
            open_arcs.pop(0)
            height -= 1
        t += 1
    assert height == 0 and next_arc == n + 1
    assert len(symbols) == n - a - 1
    return (a, h1, bits, tuple(symbols))

def reconstruct(n, a, h1, bits, symbols):
    """Data -> (shape tuple, eps tuple)."""
    if a == n:
        shape = tuple([True] * n + [False] * n)
        return shape, tuple(bits)
    # colors of arcs 2..a:
    eps = {}
    if h1 >= 1:
        free, x = bits[:-1], bits[-1]
        for i in range(2, a - h1 + 1):
            eps[i] = free[i - 2]
        for i in range(a - h1 + 1, a + 1):
            eps[i] = x
        eps[a + 1] = OPP[x]
    else:
        for i in range(2, a + 1):
            eps[i] = bits[i - 2]
        eps[a + 1] = bits[a - 1]
    shape = [True] * a + [False] * (a - h1) + [True] + [False] * h1
    # walk
    height = 1
    open_cols = [eps[a + 1]]      # FIFO of colors
    arc = a + 2
    for sym in symbols:
        # forced pops to descend to target height
        target = 0 if sym[0] == '0' else 1
        while height > target:
            shape.append(False); open_cols.pop(0); height -= 1
        shape.append(True)
        if sym[0] == '0':
            eps[arc] = sym[1]
        else:
            eps[arc] = OPP[open_cols[0]]
        open_cols.append(eps[arc]); arc += 1; height += 1
    while height > 0:
        shape.append(False); open_cols.pop(0); height -= 1
    assert len(shape) == 2 * n, (len(shape), 2 * n)
    return tuple(shape), tuple(eps[i] for i in range(2, n + 1))

def all_symbols(u):
    return product([('0', 'M'), ('0', 'm'), ('1',)], repeat=u)

def main():
    MAXN = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    report = {}
    for n in range(1, MAXN + 1):
        # brute-force avoiders as (shape, p)
        bf = []
        perms = list(permutations(range(1, n + 1)))
        for shape in dyck_shapes(n):
            for p in perms:
                if is_avoider_fast(word_from_shape_perm(shape, p)):
                    bf.append((shape, p))
        # C1: map each avoider to data, validate, roundtrip
        seen_data = set()
        class_sizes = {}
        for shape, p in bf:
            eps = eps_of_perm(p)
            assert eps is not None, f"avoider with non-max/min label: {p}"
            data = extract_data(shape, eps)
            assert data not in seen_data, f"data collision: {data}"
            seen_data.add(data)
            s2, e2 = reconstruct(n, *data)
            assert s2 == shape and e2 == eps, f"roundtrip fail: {data}"
            a, h1 = data[0], data[1]
            class_sizes[(a, h1)] = class_sizes.get((a, h1), 0) + 1
        # C2: every data tuple reconstructs to an avoider; injectivity data->word
        total_data = 0
        seen_words = set()
        datas = []
        datas.append((n, None))  # a = n class
        for bits in product('Mm', repeat=n - 1):
            d = (n, None, tuple(bits), ())
            s2, e2 = reconstruct(n, *d)
            w = word_from_shape_perm(s2, perm_of_eps(e2)) if n >= 2 else (1, 1)
            assert is_avoider_fast(w), f"reconstructed non-avoider {d}"
            assert w not in seen_words
            seen_words.add(w)
            total_data += 1
        for a in range(1, n):
            for h1 in range(0, a):
                for bits in product('Mm', repeat=a - h1):
                    for syms in all_symbols(n - a - 1):
                        d = (a, h1, tuple(bits), tuple(syms))
                        s2, e2 = reconstruct(n, *d)
                        w = word_from_shape_perm(s2, perm_of_eps(e2))
                        assert is_avoider_fast(w), f"reconstructed non-avoider {d}"
                        assert w not in seen_words, f"word collision {d}"
                        seen_words.add(w)
                        total_data += 1
        # C3: class sizes
        ok_classes = True
        for (a, h1), sz in sorted(class_sizes.items(), key=lambda kv: (kv[0][0], -1 if kv[0][1] is None else kv[0][1])):
            pred = 2 ** (n - 1) if h1 is None else 2 ** (a - h1) * 3 ** (n - a - 1)
            if sz != pred:
                ok_classes = False
                print(f"  n={n} CLASS MISMATCH (a={a},h1={h1}): bf={sz} pred={pred}")
        formula = 3 ** n - 3 * 2 ** (n - 1) + 1
        ok = (len(bf) == total_data == formula) and ok_classes
        print(f"n={n}: bf_avoiders={len(bf)} data_tuples={total_data} "
              f"formula={formula} classes_ok={ok_classes}  {'OK' if ok else 'FAIL'}")
        report[n] = {"bf": len(bf), "data": total_data, "formula": formula,
                     "ok": bool(ok)}
        assert ok
    with open(os.path.join(HERE, "verify_anatomy_results.json"), "w",
              encoding="utf-8") as f:
        json.dump(report, f, indent=1)
    print("wrote verify_anatomy_results.json")

if __name__ == "__main__":
    main()
