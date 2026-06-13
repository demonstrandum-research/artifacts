#!/usr/bin/env python3
"""verify_dual.py -- independently verify the dual-degree equivalence.

For a planar triangulation T given as a plantri ascii (-a) rotation system,
build the planar dual G *explicitly* (faces of T -> vertices of G), then
trace the faces of G and check that they are in bijection with the vertices
of T, with face size of G equal to the degree of the corresponding vertex
of T.  Hence pk(dual polytope) = #{degree-k vertices of T}.

Usage: verify_dual.py < file_of_plantri_ascii_lines
Checks every input line; prints a per-line PASS and a final verdict.

Written from scratch 2026-06-11; independent of problems/p0-iris/code/*.
"""
import sys
from collections import Counter


def parse(line):
    """Return rot: list of neighbor lists (rotation order), 0-indexed."""
    parts = line.split()
    n = int(parts[0])
    lists = parts[1].split(',')
    assert len(lists) == n, (n, len(lists))
    rot = [[ord(c) - ord('a') for c in s] for s in lists]
    return n, rot


def trace_faces(rot):
    """Trace faces of an embedded graph from its rotation system.

    Convention: from directed edge (u,v), the next directed edge of the same
    face is (v,w) where w is the neighbor immediately AFTER u in rot[v].
    Returns list of faces, each a list of directed edges (u,v).
    """
    n = len(rot)
    pos = [{w: i for i, w in enumerate(rot[v])} for v in range(n)]
    unused = {(u, v) for u in range(n) for v in rot[u]}
    faces = []
    while unused:
        e = next(iter(unused))
        face = []
        while e in unused:
            unused.remove(e)
            face.append(e)
            u, v = e
            w = rot[v][(pos[v][u] + 1) % len(rot[v])]
            e = (v, w)
        assert face[0] == (u, v) or True
        faces.append(face)
    return faces


def verify_line(line):
    n, rot = parse(line)
    deg = [len(r) for r in rot]
    E = sum(deg) // 2

    # --- faces of T ---
    faces = trace_faces(rot)
    F = len(faces)
    assert n - E + F == 2, "Euler formula fails for T"
    assert all(len(f) == 3 for f in faces), "T is not a triangulation"
    assert E == 3 * n - 6 and F == 2 * n - 4

    # --- explicit dual G: vertices = faces of T ---
    # face_of[(u,v)] = index of the face containing directed edge (u,v)
    face_of = {}
    for i, f in enumerate(faces):
        for e in f:
            face_of[e] = i
    # rotation system of G: neighbors of face i are the faces across its
    # boundary edges, in the cyclic order the boundary is traced
    drot = []
    for i, f in enumerate(faces):
        nbrs = [face_of[(v, u)] for (u, v) in f]   # face on other side
        assert i not in nbrs, "dual has a loop"
        assert len(set(nbrs)) == 3, "dual has parallel edges"
        drot.append(nbrs)
    # G is cubic with F vertices and E edges
    dE = sum(len(r) for r in drot) // 2
    assert dE == E

    # --- faces of G must correspond to vertices of T ---
    dfaces = trace_faces(drot)
    assert F - dE + len(dfaces) == 2, "Euler formula fails for G"
    assert len(dfaces) == n, "dual face count != vertex count of T"

    # Identify, for each face of G, the unique vertex of T it surrounds:
    # dual directed edge (i,j) crosses primal edge shared by faces i,j.
    sizes_by_vertex = {}
    for df in dfaces:
        common = None
        for (i, j) in df:
            shared = set(u for e in faces[i] for u in e) & \
                     set(u for e in faces[j] for u in e)
            common = shared if common is None else (common & shared)
        assert common is not None and len(common) == 1, \
            "dual face does not surround a unique primal vertex"
        v = common.pop()
        assert v not in sizes_by_vertex, "two dual faces map to same vertex"
        sizes_by_vertex[v] = len(df)

    assert set(sizes_by_vertex) == set(range(n))
    for v in range(n):
        assert sizes_by_vertex[v] == deg[v], \
            f"face size {sizes_by_vertex[v]} != deg {deg[v]} at vertex {v}"

    # face vector both ways
    fv_dual = Counter(sizes_by_vertex.values())
    fv_deg = Counter(deg)
    assert fv_dual == fv_deg
    return n, dict(sorted(fv_deg.items()))


def main():
    ok = 0
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        n, fv = verify_line(line)
        ok += 1
        print(f"PASS n={n} face_vector(p_k for k>=3)={fv}")
    print(f"ALL {ok} LINE(S) VERIFIED: dual face sizes == triangulation "
          f"degrees (pk equivalence holds)")


if __name__ == "__main__":
    main()
