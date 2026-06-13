#!/usr/bin/env python3
"""match_certs.py -- match known certificates against rederived violations.

Matching method: CANONICAL FORM of the embedded triangulation.  For each
rotation system we compute, over every choice of starting directed edge
(u,v) and both global orientations (rotation lists as given / all reversed,
i.e. mirror image), a breadth-first canonical relabeling code; the canonical
form is the lexicographic minimum.  Two simple planar triangulations on the
same vertex count have equal canonical forms iff they are isomorphic as
graphs: by Whitney's theorem a 3-connected planar graph has a unique
embedding up to reflection, and both orientations are scanned.

Usage: match_certs.py <certfile> <violationsfile>
"""
import sys


def parse(line):
    parts = line.split()
    n = int(parts[0])
    lists = parts[1].split(',')
    assert len(lists) == n
    return [[ord(c) - ord('a') for c in s] for s in lists]


def code_from(rot, u0, v0):
    """Canonical BFS code starting at directed edge (u0,v0).

    rot must already be in the desired orientation.  Vertices are relabeled
    in order of first appearance while scanning each processed vertex's
    rotation list starting from its reference neighbor.
    """
    label = {u0: 0}
    ref = {u0: v0}
    order = [u0]
    out = []
    i = 0
    while i < len(order):
        x = order[i]
        i += 1
        r = rot[x]
        k = r.index(ref[x])
        seq = r[k:] + r[:k]
        row = []
        for w in seq:
            if w not in label:
                label[w] = len(order)
                ref[w] = x
                order.append(w)
            row.append(label[w])
        out.append(tuple([len(row)] + row))
    return tuple(out)


def canon(rot):
    best = None
    mirror = [list(reversed(r)) for r in rot]
    for system in (rot, mirror):
        for u in range(len(system)):
            for v in system[u]:
                c = code_from(system, u, v)
                if best is None or c < best:
                    best = c
    return best


def main():
    certfile, violfile = sys.argv[1], sys.argv[2]

    certs = []
    with open(certfile) as f:
        for ln, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            certs.append((ln, line, canon(parse(line))))

    viols = []
    with open(violfile) as f:
        for ln, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            viols.append((ln, line, canon(parse(line))))

    vmap = {c: (ln, line) for ln, line, c in viols}
    print(f"certificates: {len(certs)}   rederived violations: {len(viols)}")

    # sanity: no duplicate canonical forms within either set
    assert len({c for _, _, c in certs}) == len(certs), "duplicate certs"
    assert len(vmap) == len(viols), "duplicate violations"

    matched = 0
    for ln, line, c in certs:
        if c in vmap:
            matched += 1
            print(f"cert line {ln}: MATCHES violation line {vmap[c][0]} "
                  f"({vmap[c][1]})")
        else:
            print(f"cert line {ln}: NO MATCH  ({line})")

    extra = [v for v in viols if v[2] not in {c for _, _, c in certs}]
    for ln, line, _ in extra:
        print(f"violation line {ln} not among certificates: {line}")

    print(f"RESULT: {matched}/{len(certs)} certificates matched; "
          f"{len(extra)} extra violation(s) beyond certificates")


if __name__ == "__main__":
    main()
