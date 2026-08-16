#!/usr/bin/env python3
"""The width-6 reduction parameter leaves the divisors of every power of N.

At width five thm:t5red gives M | N^2, so the index set of the decomposition is determined
by N. This exhibits a width-6 frieze over (1/2)Z whose reduction parameter is 12, which
divides no power of 2, and reports the whole parameter set at small N.
"""
import sys
from math import gcd
sys.path.insert(0, ".")
from verify_width6_proved import T6, full_check
from fractions import Fraction as F

def params(N, p, q, r):
    A = p * q - N * N
    B = q * r - N * N
    if A <= 0 or B <= 0:
        return None
    g = gcd(A, B)
    U, V = A // g, B // g
    return A, B, g, U, V, g * U * V - N * N * (U + V)

def main():
    N = 2
    S = sorted(T6(N))
    wit = None
    for (p, q, r) in S:
        d = params(N, p, q, r)
        if d and d[5] > 0 and d[5] % 3 == 0:
            wit = (p, q, r) + d
            break
    p, q, r, A, B, g, U, V, M = wit
    e = (p * q * r - N * N * (p + r)) // (N * N)
    quid = [F(p, N), F(q, N), F(r, N), F(p * q, e * N), F(e, N), F(q * r, e * N)]
    print(f"witness N={N}: (p,q,r,e)=({p},{q},{r},{e})  quiddity={quid}")
    print(f"  genuine frieze (all rows positive and in (1/N)Z): {full_check(quid, N, 6)}")
    print(f"  A={A} B={B} g={g} U={U} V={V}  M = gUV - N^2(U+V) = {M}")
    print(f"  M divides N^k for some k <= 20: "
          f"{any((N ** k) % M == 0 for k in range(1, 21))}")
    print("\nparameter sets at small N (width 6):")
    for N in (2, 3, 4, 5):
        Ms = sorted({d[5] for (p, q, r) in sorted(T6(N))
                     if (d := params(N, p, q, r)) and d[5] > 0})
        out = [m for m in Ms if all((N ** k) % m for k in range(1, 21))]
        print(f"  N={N}: {len(Ms)} values; not dividing any N^k (k<=20): {out[:8]}")

if __name__ == "__main__":
    main()
