"""Independent certificate checker for IRIS Conjecture 6.1 counterexample.

Input: a plantri -a ascii triangulation (rotation system).
Steps:
 1. Parse rotation system of the triangulation T.
 2. Verify T: simple, all faces triangles via face tracing, Euler V-E+F=2.
 3. Build the DUAL graph G (the simple 3-polytope's graph) with its rotation
    system: vertices of G = faces of T, faces of G = vertices of T.
 4. Certificate checks on G (this is the checker from the candidate record):
    - 3-regular
    - connected, and 3-connected (brute force: delete every pair, check conn.)
    - face tracing on rotation system + Euler formula => genus 0 embedding
    - p-vector from face sizes
    - hypothesis sum_{k>=7} pk >= 3
    - exact integer violation check: 20*p6 < 39 + 10*p3 - 5*p5 - 20*S
"""
import sys
from itertools import combinations

def parse_plantri_ascii(line):
    parts = line.strip().split()
    n = int(parts[0])
    adjs = parts[1].split(',')
    assert len(adjs) == n
    rot = {}
    for i, s in enumerate(adjs):
        v = chr(ord('a') + i)
        rot[v] = [c for c in s]
    return rot

def trace_faces(rot):
    """Faces of embedded graph from rotation system.
    Convention: next edge in face after arriving at w from v is the successor
    (next clockwise) of v in rot[w]."""
    darts = set((v, w) for v in rot for w in rot[v])
    faces = []
    used = set()
    for d in sorted(darts):
        if d in used:
            continue
        face = []
        cur = d
        while cur not in used:
            used.add(cur)
            face.append(cur)
            v, w = cur
            i = rot[w].index(v)
            nxt = rot[w][(i + 1) % len(rot[w])]
            cur = (w, nxt)
        assert cur == d, "face tracing failed to close"
        faces.append(face)
    return faces

def is_connected(adj, removed=()):
    verts = [v for v in adj if v not in removed]
    if not verts:
        return True
    seen = {verts[0]}
    stack = [verts[0]]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in removed and w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == len(verts)

def three_connected(adj):
    if len(adj) <= 3:
        return False
    if not is_connected(adj):
        return False
    for v in adj:
        if not is_connected(adj, removed=(v,)):
            return False
    for u, v in combinations(adj, 2):
        if not is_connected(adj, removed=(u, v)):
            return False
    return True

def main(line):
    rot = parse_plantri_ascii(line)
    n = len(rot)
    E = sum(len(a) for a in rot.values()) // 2
    # symmetry of adjacency, simplicity
    for v in rot:
        assert len(set(rot[v])) == len(rot[v]), "multi-edge"
        assert v not in rot[v], "loop"
        for w in rot[v]:
            assert v in rot[w], "asymmetric adjacency"
    faces = trace_faces(rot)
    F = len(faces)
    assert n - E + F == 2, f"Euler fails for T: {n}-{E}+{F}"
    assert all(len(f) == 3 for f in faces), "not a triangulation"
    print(f"T: n={n} E={E} F={F}, all faces triangles, Euler OK")

    # ---- build dual with rotation system ----
    # face id for each dart
    dart2face = {}
    for fi, f in enumerate(faces):
        for d in f:
            dart2face[d] = fi
    # dual rotation: for face f, walk its darts in order; each dart (v,w) of f
    # is shared with the face containing reversed dart (w,v).
    drot = {}
    for fi, f in enumerate(faces):
        nb = []
        for (v, w) in f:
            nb.append(dart2face[(w, v)])
        drot[fi] = nb
    dadj = {f: list(nbrs) for f, nbrs in drot.items()}

    # certificate checks on dual G
    assert all(len(drot[f]) == 3 for f in drot), "dual not cubic"
    print("G (dual): 3-regular OK,", len(drot), "vertices")
    assert three_connected(dadj), "dual not 3-connected"
    print("G: 3-connected OK (all single and pair deletions)")
    dV = len(drot)
    dE = sum(len(a) for a in drot.values()) // 2
    dfaces = trace_faces(drot)
    dF = len(dfaces)
    assert dV - dE + dF == 2, f"Euler fails for G: {dV}-{dE}+{dF}"
    print(f"G: V={dV} E={dE} F={dF}, Euler OK => genus-0 embedding certified")

    # p-vector
    from collections import Counter
    pvec = Counter(len(f) for f in dfaces)
    print("p-vector of dual polytope:", dict(sorted(pvec.items())))
    p3, p5, p6 = pvec.get(3, 0), pvec.get(5, 0), pvec.get(6, 0)
    S = sum(c for k, c in pvec.items() if k >= 7)
    print(f"p3={p3} p5={p5} p6={p6} S=sum_(k>=7)pk={S}")
    assert S >= 3, "hypothesis sum_{k>=7} pk >= 3 FAILS"
    lhs = 20 * p6
    rhs = 39 + 10 * p3 - 5 * p5 - 20 * S
    print(f"check 20*p6 < 39+10*p3-5*p5-20*S : {lhs} < {rhs} ?")
    if lhs < rhs:
        print("*** COUNTEREXAMPLE CONFIRMED: violates Conjecture 6.1 ***")
        # Also confirm consistency with Barnette (sanity): p6 >= 2+p3/2-p5/2-S
        bl, br = 2 * p6, 4 + p3 - p5 - 2 * S
        print(f"Barnette sanity: 2*p6 >= 4+p3-p5-2*S : {bl} >= {br} : "
              f"{'OK' if bl >= br else 'FAIL -- BUG SOMEWHERE'}")
        # cross-check: sum (6-k) pk = 12
        s = sum((6 - k) * c for k, c in pvec.items())
        print(f"Euler p-vector identity sum(6-k)pk = {s} (must be 12)")
    else:
        print("not a counterexample")

if __name__ == "__main__":
    main(sys.argv[1])
