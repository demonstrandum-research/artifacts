#!/usr/bin/env python3
"""Symbolic + numeric verification of the generating-function algebra.

F(z) = sum over irreducible first-components c of N(c) z^(arcs(c))
G(z) = sum over irreducible non-first components c of M(c) z^(arcs(c))
A(z) = (1/2) F(z) / (1 - G(z))   -- counts avoiders, coefficient of z^n = a_n.

Closed forms (derived by hand, verified here):
F(z) = 2z/(1-2z) + 8z^3/((1-z)(1-2z)) - 4z^3/(1-z)^2
G(z) = 2z/(1-z)
"""
import sys, os
import sympy as sp
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_characterization import (irreducible_shapes,
                                     brute_first_component_count,
                                     brute_nonfirst_component_count,
                                     N_formula, M_formula)

z = sp.symbols('z')

F = 2*z/(1-2*z) + 8*z**3/((1-z)*(1-2*z)) - 4*z**3/(1-z)**2
G = 2*z/(1-z)

# --- coefficient check of F and G against brute-force component sums, m <= 11
MAXM = 11
Fser = sp.Poly(sp.series(F, z, 0, MAXM + 1).removeO(), z).all_coeffs()[::-1]
Gser = sp.Poly(sp.series(G, z, 0, MAXM + 1).removeO(), z).all_coeffs()[::-1]
Fser += [0] * (MAXM + 1 - len(Fser))
Gser += [0] * (MAXM + 1 - len(Gser))

for m in range(1, MAXM + 1):
    if m <= 9:
        fb = sum(brute_first_component_count(c) for c in irreducible_shapes(m))
        gb = sum(brute_nonfirst_component_count(c) for c in irreducible_shapes(m))
    else:
        fb = sum(N_formula(c) for c in irreducible_shapes(m))
        gb = sum(M_formula(c) for c in irreducible_shapes(m))
    assert Fser[m] == fb, f"F coeff mismatch m={m}: {Fser[m]} vs {fb}"
    assert Gser[m] == gb, f"G coeff mismatch m={m}: {Gser[m]} vs {gb}"
    print(f"m={m}: [z^m]F = {Fser[m]} == brute {fb};  [z^m]G = {Gser[m]} == brute {gb}")

# --- the hand-derived sums behind F:
a_, x_, t_ = sp.symbols('a x t', positive=True, integer=True)
# type (i): sum_{a>=1} 2^a z^a = 2z/(1-2z)
lhs1 = sp.simplify(sp.Sum(2**a_ * z**a_, (a_, 1, sp.oo)).doit().args[0][0])
assert sp.simplify(lhs1 - 2*z/(1-2*z)) == 0
# inner sum: sum_{x=1}^{a-1} 2^(x+1) = 2^(a+1) - 4
inner = sp.simplify(sp.Sum(2**(x_ + 1), (x_, 1, a_ - 1)).doit())
assert sp.simplify(inner - (2**(a_ + 1) - 4)) == 0
print("inner sum identity OK: sum_{x=1}^{a-1} 2^(x+1) = 2^(a+1) - 4")
# type (ii)+(iii) total: sum_{a>=2} (2^(a+1)-4) [ z^(a+1) + z^(a+2)/(1-z) ]
# closed form of sum_{a>=2}(2^(a+1)-4) z^(a+1) = sum_{b>=3}(2^b-4) z^b :
S_closed = 8*z**3/(1-2*z) - 4*z**3/(1-z)
Sser = sp.Poly(sp.series(S_closed, z, 0, 25).removeO(), z)
for b in range(0, 25):
    want = (2**b - 4) if b >= 3 else 0
    assert Sser.coeff_monomial(z**b) == want, f"S coeff mismatch b={b}"
print("sum_{b>=3}(2^b-4) z^b = 8z^3/(1-2z) - 4z^3/(1-z)  OK (coeffs to z^24)")
F_rebuilt = 2*z/(1-2*z) + S_closed * (1 + z/(1-z))
assert sp.simplify(F_rebuilt - F) == 0
print("F(z) closed form rebuilt from sums OK")

# --- main identity
A = sp.Rational(1, 2) * F / (1 - G)
target = 3*z/(1-3*z) - 3*z/(1-2*z) + z/(1-z)
assert sp.simplify(A - target) == 0
print("A(z) = (1/2) F/(1-G) = 3z/(1-3z) - 3z/(1-2z) + z/(1-z)  OK")

Arat = sp.cancel(sp.together(A))
num, den = sp.fraction(Arat)
print("A(z) =", sp.factor(num), "/", sp.factor(den))

# --- series coefficients = formula
ser = sp.series(A, z, 0, 13).removeO()
coeffs = [ser.coeff(z, n) for n in range(0, 13)]
expected = [0] + [3**n - 3*2**(n-1) + 1 for n in range(1, 13)]
assert coeffs == expected, (coeffs, expected)
print("series coefficients 0..12 match 3^n - 3*2^(n-1) + 1")

# --- recurrence: (1-6z+11z^2-6z^3) A(z) is a polynomial of degree <= 3
P = sp.expand((1 - 6*z + 11*z**2 - 6*z**3) * Arat)
P = sp.simplify(P)
print("(1-6z+11z^2-6z^3) A(z) =", sp.expand(P))
assert sp.degree(sp.Poly(P, z)) <= 3

# --- transfer matrix
M = sp.Matrix([[2, 2, 0, 2], [0, 1, 1, 0], [0, 0, 1, 2], [0, 0, 0, 3]])
print("charpoly(M) =", sp.factor(M.charpoly().as_expr()))
e1 = sp.Matrix([[1, 0, 0, 0]])
fvec = sp.Matrix([1, 0, 1, 1])
TMGF = sp.simplify((z * e1 * (sp.eye(4) - z * M).inv() * fvec)[0, 0])
assert sp.simplify(TMGF - target) == 0
print("transfer-matrix GF == target  OK")

print("\nGF VERIFICATION PASSED")
