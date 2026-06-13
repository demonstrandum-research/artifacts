"""Mutation tests for checker_conj9.py (doctrine FRAMEWORK.md section 1.2):
corrupt the certificate / claims in targeted ways; every corruption must be
rejected by the checker's own primitives. A checker that never rejects
anything proves nothing."""

import checker_conj9 as C

n, edges = C.build_g14()
failures = []


def expect_reject(name, fn):
    try:
        fn()
    except AssertionError:
        print(f"  [ok] rejected: {name}")
        return
    failures.append(name)
    print(f"  [!!] ACCEPTED (BUG): {name}")


# 1. drop the bridge -> disconnected and not cubic
def m1():
    e = [x for x in edges if x != (6, 13)]
    nbr = C.neighbor_masks(n, e)
    C.check_hypotheses(n, nbr)
expect_reject("bridge removed (disconnected / degree-2 vertices)", m1)

# 2. add a chord creating a triangle (0-1 inside part {0,1,2}? that's not a
#    triangle; instead add edge (0,4): 0-4 already there. Use (1,2) plus both
#    adjacent to 4 -> triangle 1-2-4? 1-4 and 2-4 are edges, add (1,2).)
def m2():
    e = edges + [(1, 2)]
    nbr = C.neighbor_masks(n, e)
    C.check_hypotheses(n, nbr)
expect_reject("edge (1,2) added (creates triangle 1-2-4, breaks cubicity)", m2)

# 3. false gamma witness: a 3-set must never dominate
def m3():
    nbr = C.neighbor_masks(n, edges)
    full = (1 << n) - 1
    closed = [nbr[v] | (1 << v) for v in range(n)]
    assert C.dominates(closed, (0, 3, 7), full)
expect_reject("claim 3-set {0,3,7} dominates", m3)

# 4. false Z witness: the gamma witness as a forcing set of size 6
def m4():
    nbr = C.neighbor_masks(n, edges)
    full = (1 << n) - 1
    blue = sum(1 << v for v in (0, 1, 3, 4, 6, 7))
    assert C.zf_closure(n, nbr, blue, full) == full
expect_reject("claim 6-set {0,1,3,4,6,7} forces", m4)

# 5. wrong expected values must be caught by verify_graph
def m5():
    C.verify_graph("mutant", n, edges, expect_gamma=3, expect_z=7)
expect_reject("claim gamma = 3", m5)

def m6():
    C.verify_graph("mutant", n, edges, expect_gamma=4, expect_z=6)
expect_reject("claim Z = 6", m6)

# 7. a genuinely different cubic diamond-free graph that SATISFIES the
#    conjecture must NOT be reported as a counterexample: Petersen
#    (gamma=3, Z=5 -> gap 2). The 'refutes' verdict requires gap >= 3.
def m7():
    pet = [(i, (i + 1) % 5) for i in range(5)] + \
          [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + \
          [(i, i + 5) for i in range(5)]
    g, z = C.verify_graph("petersen-as-cx", 10, pet, 3, 5)
    assert z - g >= 3, "gap below 3: not a counterexample (correctly)"
expect_reject("Petersen passed off as a counterexample (gap 2)", m7)

# 8. corrupt closure: forcing with a vertex with two white neighbours must not
#    happen — verify closure from a single vertex of K3,3 stays stuck.
def m8():
    k33 = [(u, v) for u in range(3) for v in range(3, 6)]
    nbr = C.neighbor_masks(6, k33)
    full = (1 << 6) - 1
    assert C.zf_closure(6, nbr, 1 << 0, full) == full
expect_reject("single blue vertex of K3,3 claimed to force everything", m8)

print()
if failures:
    print("MUTATION TESTING FAILED:", failures)
    raise SystemExit(1)
print("MUTATION TESTING PASSED: all 8 corruptions rejected.")
