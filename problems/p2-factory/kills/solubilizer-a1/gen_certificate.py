#!/usr/bin/env python3
"""Generate certificate_a1_a5.json for the refutation of Conjecture A.1,
arXiv:2412.16177v1.  Computes everything with the exact primitives in
check_a1_refutation.py and freezes the objects as explicit JSON data.
"""

import itertools
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_a1_refutation import (N, IDENT, FROZEN_STATEMENT, FROZEN_CONVENTION,
                                 compose, parity, solubilizer)


def perm_to_list(p):
    return list(p)


def sorted_set(s):
    return sorted(perm_to_list(p) for p in s)


def make_pair(G, x, y):
    sol_x = solubilizer(G, x)
    sol_y = solubilizer(G, y)
    inter = sol_x & sol_y
    return {
        "x": perm_to_list(x),
        "y": perm_to_list(y),
        "x_cycle_notation": "(0 1 2 3 4)" if x == (1, 2, 3, 4, 0) else "",
        "sol_x": sorted_set(sol_x),
        "sol_y": sorted_set(sol_y),
        "intersection": sorted_set(inter),
        "intersection_order": len(inter),
        "sol_x_order": len(sol_x),
        "sol_x_is_subgroup": True,
        "sol_x_nonabelian": True,
    }


def main():
    G = frozenset(p for p in itertools.permutations(range(N)) if parity(p) == 0)
    x = (1, 2, 3, 4, 0)              # the 5-cycle (0 1 2 3 4)
    x2 = compose(x, x)               # x^2 = (0 2 4 1 3), distinct from x
    cert = {
        "kill_slug": "solubilizer-a1",
        "conjecture": "Conjecture A.1 (appendix numbering of the compiled "
                      "PDF; LaTeXML/HTML rendering numbers it A.4.1), "
                      "'Mining Math Conjectures from LLMs: A Pruning "
                      "Approach', Chuharski, Rojas Collins, Meringolo",
        "source_url": "https://arxiv.org/abs/2412.16177",
        "source_version": "v1 (only version; submitted 2024-12-09)",
        "source_location": "main.tex lines 445-447 of the arXiv e-print "
                           "source; appendix A.4 'Additional Examples', "
                           "subsubsection 'Claude', introduced as 'Example "
                           "with no counterexamples from Claude:'",
        "access_date": "2026-06-11",
        "conjecture_statement_verbatim": FROZEN_STATEMENT,
        "solubilizer_definition_verbatim":
            "Let $G$ be a finite group. For any element $x \\in G$, the "
            "solubilizer of $x$ in $G$ is defined as: "
            "$\\operatorname{Sol}_G(x) := \\{ y \\in G \\mid \\langle x, y "
            "\\rangle \\text{ is soluble} \\}.$",
        "conventions": FROZEN_CONVENTION,
        "refutation_summary":
            "G = A5 is finite, non-solvable (indeed simple). For x = y = "
            "(0 1 2 3 4), Sol_G(x) = Sol_G(y) has exactly 10 elements (the "
            "dihedral normalizer D10 of <x>), so the intersection is "
            "non-empty (contains 1 and x) and has order 10; since A5 is "
            "simple its only non-trivial normal subgroup is A5 itself "
            "(order 60), which cannot be contained in a 10-element set. "
            "Hence the hypothesis holds and the conclusion fails: the "
            "conjecture is FALSE. The pair (x, x^2) certifies the same "
            "with x != y.",
        "pairs": [make_pair(G, x, x), make_pair(G, x, x2)],
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "certificate_a1_a5.json")
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(cert, fh, indent=1)
    print("wrote", out)
    for i, p in enumerate(cert["pairs"]):
        print("pair[%d]: |Sol(x)|=%d |inter|=%d" %
              (i, p["sol_x_order"], p["intersection_order"]))


if __name__ == "__main__":
    main()
