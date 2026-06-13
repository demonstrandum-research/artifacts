#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Builds certificate_g143.json for the Gate-4 verification of the refutation of
Graffiti Conjecture 143. The checker (checker_g143.py) re-verifies everything
in this file from scratch; values recorded here are claims, not authority.
"""
import json
from fractions import Fraction

from checker_g143 import (adjacency_from_edges, bfs_wiener, dumbbell_edges,
                          route_b)

VERBATIM = ('143. variance of positive eigenvalues ≤ size / average '
            'distance.  [S. Fajtlowicz, "Written on the Wall" (Graffiti), '
            'July 2004 compilation, p.65; ≤ glyph = cmsy 0x14]')

INSTANCES = [
    # (name, t1, p, t2, violates)
    ("dumbbell(20,8,20)  n=48 headline (claim record)", 20, 8, 20, ["n2", "pairs"]),
    ("dumbbell(8,12,20)  n=40 claim-record minimal", 8, 12, 20, ["n2", "pairs"]),
    ("dumbbell(7,12,20)  n=39 NEW smallest, both conventions", 7, 12, 20, ["n2", "pairs"]),
    ("dumbbell(6,12,20)  n=38 pairs-convention violation", 6, 12, 20, ["pairs"]),
    ("dumbbell(6,12,19)  n=37 smallest known, pairs convention", 6, 12, 19, ["pairs"]),
]


def build_instance(name, t1, p, t2, violates):
    n, edges = dumbbell_edges(t1, p, t2)
    A = adjacency_from_edges(n, edges)
    m = len(edges)
    W = bfs_wiener(A)
    rhs_n2 = Fraction(m * n * n, 2 * W)
    rhs_pairs = Fraction(m * n * (n - 1), 2 * W)
    rb = route_b(A, (t1, p, t2))
    inst = {
        "name": name,
        "family": "dumbbell",
        "t1": t1, "p": p, "t2": t2,
        "n": n, "m": m, "W": W, "k": rb["k"],
        "edges": [list(e) for e in edges],
        "rhs_n2": str(rhs_n2),
        "rhs_pairs": str(rhs_pairs),
        "violates": violates,
        "var_pos_certified_interval": [str(rb["var_lo"]), str(rb["var_hi"])],
        "var_pos_float": float((rb["var_lo"] + rb["var_hi"]) / 2),
    }
    for conv, rhs in (("n2", rhs_n2), ("pairs", rhs_pairs)):
        if conv in violates:
            mlo = rb["var_lo"] - rhs
            assert mlo > 0, "instance %s does not certify %s" % (name, conv)
            inst["margin_%s_lower" % conv] = str(mlo)
            inst["margin_%s_lower_float" % conv] = float(mlo)
    return inst


def main():
    cert = {
        "title": "Refutation of Graffiti Conjecture 143 (Gate-4 clean-room rebuild)",
        "slug": "graffiti-143",
        "conjecture_verbatim": VERBATIM,
        "operational_statement": (
            "For every connected graph G: population variance of the strictly "
            "positive adjacency eigenvalues <= m / l(G), where m = |E(G)| and "
            "l(G) = average distance. Reading N2: l = 2W/n^2 (all ordered "
            "pairs incl. diagonal; Roucairol-Cazenave ECAI 2025 code). Reading "
            "PAIRS: l = 2W/(n(n-1)) (distinct pairs; Aouchiche-Hansen)."),
        "provenance": {
            "source_pdf": "https://raw.githubusercontent.com/RoucairolMilo/refutation-COCOON2022/master/wow-july2004.pdf",
            "accessed": "2026-06-11",
            "openness": ("Listed 'O' (open), searched to size 100, in "
                         "Roucairol & Cazenave, 'Refutation of Spectral Graph "
                         "Theory Conjectures with Search Algorithms', ECAI 2025 "
                         "(arXiv:2409.18626), Table of conjectures."),
        },
        "instances": [build_instance(*spec) for spec in INSTANCES],
    }
    with open("certificate_g143.json", "w", encoding="utf-8") as fh:
        json.dump(cert, fh, indent=1)
    print("wrote certificate_g143.json with %d instances" % len(cert["instances"]))


if __name__ == "__main__":
    main()
