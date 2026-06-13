# -*- coding: utf-8 -*-
"""Generate VALID planar triangulations (plantri -a ascii lines) that are NOT
counterexamples to IRIS Conjecture 6.1, for mutation-testing the checkers.

Categories:
  e) valid triangulation with S = sum_{k>=7} pk < 3 (hypothesis fails)
  g) valid triangulation with S >= 3 but 20*p6 >= 39 + 10*p3 - 5*p5 - 20*S
     (inequality satisfied)

The dual polytope's pk equals the number of degree-k vertices of the
triangulation T, so we can steer by vertex degrees; the checkers themselves
re-derive everything via the explicit dual.

Every emitted line is validated here independently: simple, symmetric rotation
system, connected, face tracing closes, V-E+F=2, all faces triangles.
"""
import random
import sys
from collections import Counter

# ---------------- rotation-system utilities ----------------

def trace(rot):
    faces = []
    used = set()
    for v in range(len(rot)):
        for w in rot[v]:
            d = (v, w)
            if d in used:
                continue
            face = []
            cur = d
            while cur not in used:
                used.add(cur)
                face.append(cur)
                a, b = cur
                i = rot[b].index(a)
                cur = (b, rot[b][(i + 1) % len(rot[b])])
            if cur != d:
                return None
            faces.append(face)
    return faces

def validate(rot):
    n = len(rot)
    if n < 4:
        return False
    for v, row in enumerate(rot):
        if len(set(row)) != len(row) or v in row or not row:
            return False
        for w in row:
            if w < 0 or w >= n or v not in rot[w]:
                return False
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in rot[v]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    if len(seen) != n:
        return False
    E = sum(len(r) for r in rot) // 2
    faces = trace(rot)
    if faces is None:
        return False
    if n - E + len(faces) != 2:
        return False
    return all(len(f) == 3 for f in faces)

def to_line(rot):
    return "%d %s" % (len(rot), ",".join("".join(chr(97 + w) for w in row) for row in rot))

def parse(line):
    n_s, lists = line.split()
    return [[ord(c) - 97 for c in part] for part in lists.split(",")]

def pstats(rot):
    pv = Counter(len(r) for r in rot)
    p3, p5, p6 = pv.get(3, 0), pv.get(5, 0), pv.get(6, 0)
    S = sum(c for k, c in pv.items() if k >= 7)
    lhs = 20 * p6
    rhs = 39 + 10 * p3 - 5 * p5 - 20 * S
    return pv, S, lhs, rhs

# ---------------- operations ----------------

def stellate(rot, face):
    """Insert a new vertex inside the triangular face (darts [(u,v),(v,w),(w,u)])."""
    (u, _v), (v, _w), (w, _u) = face
    z = len(rot)
    for conv in (0, 1):
        r2 = [list(r) for r in rot]
        if conv == 0:
            r2[v].insert(r2[v].index(u) + 1, z)
            r2[w].insert(r2[w].index(v) + 1, z)
            r2[u].insert(r2[u].index(w) + 1, z)
            r2.append([w, v, u])
        else:
            r2[v].insert(r2[v].index(u), z)
            r2[w].insert(r2[w].index(v), z)
            r2[u].insert(r2[u].index(w), z)
            r2.append([u, v, w])
        if validate(r2):
            return r2
    return None

def flip(rot, u, v):
    """Flip edge {u,v} shared by triangles (u,v,x) and (v,u,y) -> edge {x,y}."""
    if v not in rot[u]:
        return None
    if len(rot[u]) <= 3 or len(rot[v]) <= 3:
        return None
    i = rot[v].index(u)
    x = rot[v][(i + 1) % len(rot[v])]
    j = rot[u].index(v)
    y = rot[u][(j + 1) % len(rot[u])]
    if x == y or x in rot[y] or y == u or y == v or x == u or x == v:
        return None
    for conv in (0, 1):
        r2 = [list(r) for r in rot]
        r2[u].remove(v)
        r2[v].remove(u)
        if conv == 0:
            r2[x].insert(r2[x].index(v) + 1, y)
            r2[y].insert(r2[y].index(u) + 1, x)
        else:
            r2[x].insert(r2[x].index(v), y)
            r2[y].insert(r2[y].index(u), x)
        if validate(r2):
            return r2
    return None

# ---------------- explicit constructions ----------------

def bipyramid(k):
    """k-gonal bipyramid: apex 0, ring 1..k, apex k+1. n = k+2."""
    n = k + 2
    ring = list(range(1, k + 1))
    B = k + 1
    for ring_conv in (0, 1):
        for b_rev in (False, True):
            rot = [None] * n
            rot[0] = ring[:]
            for idx, r in enumerate(ring):
                nxt = ring[(idx + 1) % k]
                prv = ring[(idx - 1) % k]
                rot[r] = [0, nxt, B, prv] if ring_conv == 0 else [0, prv, B, nxt]
            rot[B] = ring[::-1] if b_rev else ring[:]
            if validate(rot):
                return rot
    raise AssertionError("bipyramid k=%d failed validation" % k)

def tetrahedron():
    for cand in (
        [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]],
        [[1, 2, 3], [0, 2, 3], [0, 3, 1], [0, 1, 2]],
    ):
        if validate(cand):
            return cand
    raise AssertionError("no valid K4 rotation found")

def octahedron():
    rot = parse("6 bcde,aefc,abfd,acfe,adfb,bedc")
    assert validate(rot)
    return rot

def icosahedron():
    """Flip search at n=12 for all degrees = 5: the unique such planar
    triangulation is the icosahedron."""
    rng = random.Random(42)
    for trial in range(50):
        rot, _ = random_triangulation(12, rng.randrange(1 << 30))
        cur = sum(abs(len(r) - 5) for r in rot)
        for it in range(60000):
            u = rng.randrange(len(rot))
            v = rng.choice(rot[u])
            r2 = flip(rot, u, v)
            if r2 is None:
                continue
            sc = sum(abs(len(r) - 5) for r in r2)
            if sc <= cur or rng.random() < 0.05:
                rot, cur = r2, sc
            if cur == 0:
                return rot
    raise AssertionError("no valid icosahedron rotation found")

# ---------------- steered random search for category (g) ----------------

def random_triangulation(n_target, seed):
    rng = random.Random(seed)
    rot = octahedron()
    while len(rot) < n_target:
        faces = trace(rot)
        f = rng.choice(faces)
        r2 = stellate(rot, f)
        if r2 is not None:
            rot = r2
    return rot, rng

def score(rot, want_p3_zero=True):
    degs = sorted((len(r) for r in rot), reverse=True)
    s = 0
    if want_p3_zero:
        s += 6 * sum(1 for d in degs if d == 3)
    s += sum(max(0, 7 - d) for d in degs[:3])  # want top three degrees >= 7
    return s

def search_g(n_target, seed, max_iter=300000, want_p3_zero=True):
    rot, rng = random_triangulation(n_target, seed)
    cur = score(rot, want_p3_zero)
    for it in range(max_iter):
        u = rng.randrange(len(rot))
        if not rot[u]:
            continue
        v = rng.choice(rot[u])
        r2 = flip(rot, u, v)
        if r2 is None:
            continue
        sc = score(r2, want_p3_zero)
        if sc <= cur or rng.random() < 0.02:
            rot, cur = r2, sc
        if cur == 0:
            pv, S, lhs, rhs = pstats(rot)
            if S >= 3 and lhs >= rhs:
                return rot
    return None

def search_small_margin(seed, max_iter=400000):
    """Look for S>=3, lhs>=rhs with the smallest margin lhs-rhs (p3>0 allowed)."""
    best = None
    rng = random.Random(seed)
    for trial in range(40):
        n_target = rng.choice([11, 12, 13, 14])
        rot, _ = random_triangulation(n_target, rng.randrange(1 << 30))
        for it in range(8000):
            u = rng.randrange(len(rot))
            v = rng.choice(rot[u])
            r2 = flip(rot, u, v)
            if r2 is None:
                continue
            rot = r2
            pv, S, lhs, rhs = pstats(rot)
            if S >= 3 and lhs >= rhs:
                margin = lhs - rhs
                if best is None or margin < best[0]:
                    best = (margin, [list(r) for r in rot])
                    if margin <= 1:
                        return best
    return best

def main():
    out = []

    def emit(tag, rot, note):
        assert validate(rot), tag
        pv, S, lhs, rhs = pstats(rot)
        line = to_line(rot)
        print("%s n=%d pvec=%s S=%d lhs=%d rhs=%d  %s" % (
            tag, len(rot), dict(sorted(pv.items())), S, lhs, rhs, note))
        out.append((tag, line))

    emit("e1_tetrahedron", tetrahedron(), "S=0")
    emit("e2_octahedron", octahedron(), "S=0")
    emit("e3_icosahedron", icosahedron(), "S=0")
    emit("e4_bipyramid5", bipyramid(5), "S=0")
    emit("e5_bipyramid6", bipyramid(6), "S=0")
    emit("e6_bipyramid7", bipyramid(7), "S=2 boundary of hypothesis")
    emit("e7_bipyramid8", bipyramid(8), "S=2")

    for tag, n_target, seed in (("g1_n14", 14, 12345), ("g2_n16", 16, 777), ("g3_n18", 18, 2026)):
        rot = search_g(n_target, seed)
        if rot is None:
            print("FAILED to find %s" % tag, file=sys.stderr)
            sys.exit(1)
        emit(tag, rot, "S>=3, inequality satisfied (p3=0 forced)")

    best = search_small_margin(99)
    if best is not None:
        emit("g4_small_margin", best[1], "S>=3, inequality satisfied, margin lhs-rhs=%d" % best[0])
    else:
        print("WARNING: no small-margin g4 found", file=sys.stderr)

    with open(sys.argv[1], "w", encoding="utf-8", newline="\n") as fh:
        for tag, line in out:
            fh.write("%s\t%s\n" % (tag, line))

if __name__ == "__main__":
    main()
