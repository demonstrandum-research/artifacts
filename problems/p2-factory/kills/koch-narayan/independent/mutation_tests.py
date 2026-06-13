#!/usr/bin/env python3
"""Mutation tests for the koch-narayan kill (FRAMEWORK.md section 1.2).

Each mutation corrupts the primary n=13 certificate in a targeted way and
must be REJECTED by the clean-room verifier's check_graph() (imported from
cleanroom_check.py, which is the Gate-4 clean-room implementation).  The
pristine certificate must be ACCEPTED.  A checker that never rejects
anything proves nothing.

Run:  python mutation_tests.py     (exit 0 iff all mutations killed)
"""
import io
import sys
import contextlib

import cleanroom_check as cc

# Primary certificate: n=13 counterexample, A = {0..5}, B = {6..12}.
N13 = 13
E13 = [(0, 6), (1, 7), (2, 8), (3, 8), (4, 9), (5, 9),
       (0, 10), (2, 10), (3, 10), (4, 10), (5, 10),
       (1, 11), (2, 11), (3, 11), (4, 11), (5, 11),
       (0, 12), (1, 12), (2, 12), (3, 12), (4, 12), (5, 12)]
MDS13 = [0, 1, 8, 9]


def run_case(name, n, edges, gamma_claimed, expect_accept):
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            verdict = cc.check_graph(name, n, edges, gamma_claimed, MDS13)
    except Exception as exc:                       # malformed cert => reject
        verdict = False
        reason = f"exception {type(exc).__name__}: {exc}"
    else:
        reason = "verdict False" if not verdict else "verdict True"
    ok = (verdict == expect_accept)
    status = "OK  " if ok else "FAIL"
    want = "ACCEPT" if expect_accept else "REJECT"
    got = "ACCEPT" if verdict else f"REJECT ({reason})"
    print(f"[{status}] {name:38s} want {want:6s} got {got}")
    return ok


def main():
    results = []
    # pristine certificate must be accepted
    results.append(run_case("pristine n=13 certificate",
                            N13, E13, 4, True))
    # M1: remove edge (0,12) -> s=21 <= m(13,4)=21, no violation
    results.append(run_case("M1 drop edge (0,12): s=21<=m",
                            N13, [e for e in E13 if e != (0, 12)], 4, False))
    # M2: remove edge (1,7) -> vertex 7 isolated
    results.append(run_case("M2 drop edge (1,7): isolated vertex",
                            N13, [e for e in E13 if e != (1, 7)], 4, False))
    # M3: add within-part edge (2,3) -> odd cycle, not bipartite
    results.append(run_case("M3 add edge (2,3): not bipartite",
                            N13, E13 + [(2, 3)], 4, False))
    # M4: add within-part edge (10,11) -> odd cycle, not bipartite
    results.append(run_case("M4 add edge (10,11): not bipartite",
                            N13, E13 + [(10, 11)], 4, False))
    # M5: add cross edge (0,7) -> minimum dominating set no longer unique
    results.append(run_case("M5 add edge (0,7): MDS not unique",
                            N13, E13 + [(0, 7)], 4, False))
    # M6: misreport gamma as 3
    results.append(run_case("M6 claim gamma=3: gamma mismatch",
                            N13, E13, 3, False))
    # M7: pad with an isolated 14th vertex
    results.append(run_case("M7 n=14 with isolated vertex",
                            14, E13, 4, False))
    # M8: rewire (0,6) to (1,6) -> uniqueness of the MDS breaks
    results.append(run_case("M8 rewire (0,6)->(1,6): MDS not unique",
                            N13, [(1, 6)] + [e for e in E13 if e != (0, 6)],
                            4, False))
    # M9: duplicate edge in the list -> malformed certificate
    results.append(run_case("M9 duplicate edge (0,6): malformed",
                            N13, E13 + [(0, 6)], 4, False))
    # M10: vertex index out of range -> malformed certificate
    results.append(run_case("M10 vertex 13 out of range: malformed",
                            N13, [(0, 13)] + E13[1:], 4, False))

    if all(results):
        print("MUTATION TESTS: ALL KILLED (pristine accepted,"
              f" {len(results)-1}/{len(results)-1} mutations rejected)")
        return 0
    print("MUTATION TESTS: FAILURE — see lines marked FAIL above")
    return 1


if __name__ == "__main__":
    sys.exit(main())
