"""One-minute float sanity check for the sun-46 kill (orientation only;
the exact checkers in ../../attacks/sun-46/ are the authoritative verification).

Reproduces three of Sun's published values (including two negatives, validating
the sign conventions end-to-end) and then the p = 29 kill pair.

Expected output:
    -239 -6 -7094142
    1053859 -4806838304
"""
import math


def per(A):                                   # Ryser permanent, float64
    n = len(A)
    tot = 0.0
    for mask in range(1, 1 << n):
        prod = 1.0
        for row in A:
            s = 0.0
            for k in range(n):
                if mask >> k & 1:
                    s += row[k]
            prod *= s
        tot += (-1) ** bin(mask).count('1') * prod
    return (-1) ** n * tot


def s(p):                                     # Sun's s_p  (Thm 1.6(i))
    m = (p - 1) // 2
    M = [[math.sin(2 * math.pi * j * k / p) for k in range(1, m + 1)]
         for j in range(1, m + 1)]
    return 2 ** m / math.sqrt(p) * per(M)


def sp(p):                                    # Sun's s'_p (Thm 1.6(ii))
    m = (p - 1) // 2
    M = [[1.0 / math.sin(2 * math.pi * j * k / p) for k in range(1, m + 1)]
         for j in range(1, m + 1)]
    return math.sqrt(p) / 2 ** m * per(M)


print(round(s(17)), round(sp(7)), round(sp(23)))   # published: -239, -6, -7094142
print(round(s(29)), round(sp(29)))                 # kill pair:  1053859, -4806838304
assert round(s(29)) == 1053859 and round(sp(29)) == -4806838304
# 29 == 5 (mod 12)  =>  conjecture demands s_29 < 0   : VIOLATED (s_29 > 0)
# 29 == 5 (mod 8)   =>  conjecture demands s'_29 >= 0 : VIOLATED (s'_29 < 0)
