#!/usr/bin/env python3
"""Mutation tests for check_a1_refutation.py (Gate-4 doctrine 1.2):
corrupt the certificate in targeted ways; the checker must REJECT every
mutant and ACCEPT the pristine certificate.  Exit 0 iff all outcomes are
as expected.
"""

import copy
import itertools
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKER = os.path.join(HERE, "check_a1_refutation.py")
CERT = os.path.join(HERE, "certificate_a1_a5.json")


def run_checker(cert_obj):
    fd, path = tempfile.mkstemp(suffix=".json")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(cert_obj, fh)
        proc = subprocess.run([sys.executable, CHECKER, path],
                              capture_output=True, text=True, timeout=600)
        return proc.returncode, (proc.stdout + proc.stderr).strip()
    finally:
        os.unlink(path)


# ---- mutation constructors -------------------------------------------------

def m1_statement_typo(c):
    """Alter one character of the frozen verbatim statement."""
    c["conjecture_statement_verbatim"] = (
        c["conjecture_statement_verbatim"].replace("non-trivial", "nontrivial"))
    return c


def m2_x_odd_permutation(c):
    """x replaced by a transposition (odd) -- not an element of A5."""
    c["pairs"][0]["x"] = [1, 0, 2, 3, 4]
    return c


def m3_sol_x_extra_element(c):
    """Smuggle a 3-cycle into the claimed Sol set."""
    c["pairs"][0]["sol_x"].append([1, 2, 0, 3, 4])
    return c


def m4_sol_x_dropped_element(c):
    """Drop a genuine element from the claimed Sol set."""
    c["pairs"][0]["sol_x"] = c["pairs"][0]["sol_x"][:-1]
    return c


def m5_intersection_inflated(c):
    """Claim the intersection is all of A5 (and fix the order field)."""
    a5 = sorted(list(p) for p in itertools.permutations(range(5))
                if sum(1 for i in range(5) for j in range(i + 1, 5)
                       if p[i] > p[j]) % 2 == 0)
    c["pairs"][0]["intersection"] = a5
    c["pairs"][0]["intersection_order"] = 60
    return c


def m6_identity_pair(c):
    """Mathematical-core mutant: x = y = identity.  Then Sol = G and the
    intersection = G DOES contain a non-trivial normal subgroup (G itself):
    bookkeeping is self-consistent, but the refutation must be rejected."""
    a5 = sorted(list(p) for p in itertools.permutations(range(5))
                if sum(1 for i in range(5) for j in range(i + 1, 5)
                       if p[i] > p[j]) % 2 == 0)
    pair = {
        "x": [0, 1, 2, 3, 4],
        "y": [0, 1, 2, 3, 4],
        "sol_x": a5,
        "sol_y": a5,
        "intersection": a5,
        "intersection_order": 60,
        "sol_x_order": 60,
        "sol_x_is_subgroup": True,
        "sol_x_nonabelian": True,
    }
    c["pairs"] = [pair]
    return c


def m7_non_permutation_entry(c):
    """Corrupt one claimed Sol element into a non-permutation."""
    c["pairs"][0]["sol_x"][0] = [0, 0, 2, 3, 4]
    return c


def m8_y_swapped_sol_y_stale(c):
    """Change y to a 3-cycle but leave the claimed Sol_G(y) stale."""
    c["pairs"][0]["y"] = [1, 2, 0, 3, 4]
    return c


def m9_wrong_sol_order_claim(c):
    """Claim |Sol_G(x)| = 12."""
    c["pairs"][0]["sol_x_order"] = 12
    return c


def m10_empty_pairs(c):
    """No certified pairs at all."""
    c["pairs"] = []
    return c


def m11_drop_distinct_pair(c):
    """Remove the x != y pair: distinct-elements reading no longer covered."""
    c["pairs"] = [p for p in c["pairs"] if p["x"] == p["y"]]
    return c


def m12_definition_tampered(c):
    """Alter the frozen verbatim solubilizer definition."""
    c["solubilizer_definition_verbatim"] = (
        c["solubilizer_definition_verbatim"].replace("soluble", "nilpotent"))
    return c


def m13_duplicate_intersection_entry(c):
    """Duplicate an element inside the claimed intersection (Codex's extra
    mutant, kept in the suite)."""
    c["pairs"][0]["intersection"].append(c["pairs"][0]["intersection"][0])
    return c


MUTATIONS = [
    ("m1_statement_typo", m1_statement_typo),
    ("m2_x_odd_permutation", m2_x_odd_permutation),
    ("m3_sol_x_extra_element", m3_sol_x_extra_element),
    ("m4_sol_x_dropped_element", m4_sol_x_dropped_element),
    ("m5_intersection_inflated", m5_intersection_inflated),
    ("m6_identity_pair", m6_identity_pair),
    ("m7_non_permutation_entry", m7_non_permutation_entry),
    ("m8_y_swapped_sol_y_stale", m8_y_swapped_sol_y_stale),
    ("m9_wrong_sol_order_claim", m9_wrong_sol_order_claim),
    ("m10_empty_pairs", m10_empty_pairs),
    ("m11_drop_distinct_pair", m11_drop_distinct_pair),
    ("m12_definition_tampered", m12_definition_tampered),
    ("m13_duplicate_intersection_entry", m13_duplicate_intersection_entry),
]


def main():
    with open(CERT, "r", encoding="utf-8") as fh:
        good = json.load(fh)

    failures = 0

    rc, out = run_checker(good)
    status = "ok" if rc == 0 else "FAIL"
    if rc != 0:
        failures += 1
    print("[%s] pristine certificate -> exit %d (expected 0)" % (status, rc))

    for name, fn in MUTATIONS:
        mutant = fn(copy.deepcopy(good))
        rc, out = run_checker(mutant)
        ok = rc != 0
        if not ok:
            failures += 1
        first = out.splitlines()[0] if out else "(no output)"
        print("[%s] %s -> exit %d (expected nonzero) | %s"
              % ("ok" if ok else "FAIL", name, rc, first))

    if failures:
        print("MUTATION SUITE: %d FAILURE(S)" % failures)
        return 1
    print("MUTATION SUITE: all %d mutants rejected, pristine accepted."
          % len(MUTATIONS))
    return 0


if __name__ == "__main__":
    sys.exit(main())
