#!/usr/bin/env python3
"""Emit certificate.json for the pandey-parity kill from the clean-room
checker's own computations (then validated back by
`python check_pandey_parity.py --cert certificate.json`, and cross-checked
against the independent Rust brute-forcer bf_gp.rs)."""

import json
from fractions import Fraction

import check_pandey_parity as C


def jsonify_label(lbl):
    return [lbl[0], lbl[1]]


def main():
    rows = []
    violations = []
    for n in range(3, 15):
        for k in range(1, (n - 1) // 2 + 1):
            r = C.analyze(n, k)
            rows.append({
                'n': n, 'k': k, 'coeffs': r['coeffs'],
                'degree': r['degree'], 'squarefree': r['squarefree'],
                'real_distinct': r['real_distinct'],
                'real_rooted': r['real_rooted'],
                'violates_conjecture': r['violates_conjecture'],
                'direction': r['direction'],
            })
            if r['violates_conjecture']:
                violations.append([n, k])

    g92 = C.analyze(9, 2)
    g73 = C.analyze(7, 3)
    g72 = C.analyze(7, 2)
    g31 = C.analyze(3, 1)

    iso = C.classical_iso_map(7, 3)
    ok, why = C.verify_isomorphism(7, 2, 3, iso)
    assert ok, why

    # informational (NOT load-bearing): numeric roots of I(GP(9,2),x)
    numeric = None
    try:
        import numpy as np
        rts = np.roots(list(reversed(g92['coeffs'])))
        numeric = sorted([[float(z.real), float(z.imag)] for z in rts],
                         key=lambda t: (t[0], t[1]))
    except Exception:
        pass

    cert = {
        'slug': 'pandey-parity',
        'claim': 'Conjecture 4.1 (Parity Conjecture) of arXiv:2601.03293 is '
                 'false in both directions, and its predicate is not '
                 'isomorphism-invariant.',
        'provenance': {
            'source': 'arXiv:2601.03293, R. Pandey, "Parity-Dependent '
                      'Real-Rootedness in Independence Polynomials of '
                      'Generalized Petersen Graphs", submitted 2026-01-05',
            'urls': ['https://arxiv.org/abs/2601.03293',
                     'https://arxiv.org/html/2601.03293v1'],
            'accessed': '2026-06-11',
            'conjecture_verbatim': 'For all integers n >= 2k+1, the '
                'independence polynomial I(GP(n,k),x) has only real roots '
                'if and only if k is even.',
            'definition_verbatim': 'Definition 2.1: for integers n >= 3 and '
                '1 <= k < n/2, GP(n,k) has vertices u_0..u_{n-1}, '
                'v_0..v_{n-1}; edges u_i u_{i+1} (outer cycle), v_i v_{i+k} '
                '(inner chords), u_i v_i (spokes), indices mod n.',
            'author_validation_verbatim': 'The computations were carried out '
                'for all k in {1,2,3,4} and for 20 <= n <= 30, with '
                'consistent qualitative behavior observed throughout this '
                'range. ... Roots were obtained using standard polynomial '
                'root-finding routines and verified to numerical precision '
                '10^-10.',
        },
        'gp_9_2': {
            'role': "kills the 'if' direction: k=2 even, n=9 >= 2k+1=5, "
                    "but I(GP(9,2),x) is NOT real-rooted",
            'edges': [[jsonify_label(a), jsonify_label(b)]
                      for a, b in C.gp_edges(9, 2)],
            'coeffs': g92['coeffs'],
            'degree': g92['degree'],
            'squarefree': g92['squarefree'],
            'real_distinct_roots_sturm': g92['real_distinct'],
            'real_rooted': g92['real_rooted'],
            'numeric_roots_informational': numeric,
        },
        'gp_7_3': {
            'role': "kills the 'only if' direction: k=3 odd, n=7 >= 2k+1=7, "
                    "but I(GP(7,3),x) IS real-rooted",
            'edges': [[jsonify_label(a), jsonify_label(b)]
                      for a, b in C.gp_edges(7, 3)],
            'coeffs': g73['coeffs'],
            'degree': g73['degree'],
            'squarefree': g73['squarefree'],
            'real_distinct_roots_sturm': g73['real_distinct'],
            'real_rooted': g73['real_rooted'],
        },
        'gp_3_1': {
            'role': "second 'only if' violation: k=1 odd, n=3 >= 2k+1=3, "
                    "triangular prism, real-rooted (claw-free, so also "
                    "real-rooted by Chudnovsky-Seymour)",
            'coeffs': g31['coeffs'],
            'real_rooted': g31['real_rooted'],
        },
        'isomorphism_gp72_to_gp73': {
            'statement': 'GP(7,2) and GP(7,3) are isomorphic (2*3 == -1 mod '
                         '7), so the parity of k is not an isomorphism '
                         'invariant and the conjecture is not well-posed '
                         'under isomorphism.',
            'map': [[jsonify_label(a), jsonify_label(b)]
                    for a, b in sorted(iso.items())],
            'i_poly_gp72': g72['coeffs'],
            'i_poly_gp73': g73['coeffs'],
        },
        'violations_3_to_14': violations,
        'scan_table': rows,
        'method': 'Independence polynomials by exact integer recursion '
                  'I(G)=I(G-v)+x*I(G-N[v]) memoized on bitmasks; coefficients '
                  'cross-checked by full 2^(2n) subset enumeration (pure '
                  'Python for 2n<=20 inside the checker; independent Rust '
                  'program bf_gp.rs for ALL pairs 3<=n<=14). Real-rootedness '
                  'decided exactly: p real-rooted iff Sturm real-root count '
                  'of the squarefree part p/gcd(p,p\') equals its degree, '
                  'all over Q (fractions). No floating point in any verdict.',
    }
    with open('certificate.json', 'w', encoding='utf-8') as fh:
        json.dump(cert, fh, indent=1)
    print('wrote certificate.json')


if __name__ == '__main__':
    main()
