#!/usr/bin/env python3
"""Certificate for the width-six reduced form (VicoEnum/Width6Reduced.lean).

With A = pq - N^2, B = qr - N^2, g = gcd(A,B), U = A/g, V = B/g, R = q, the
defining relation pqr = N^2(e+p+r) is equivalent to the master identity

    A B = N^4 + N^2 q e,    that is    g^2 U V = N^4 + N^2 R e,

and the frieze conditions become divisibilities in (g,U,V,R) alone.  This script
checks both directions against the proved width-six enumeration.
"""
import sys
from fractions import Fraction as F
from math import gcd
from verify_width6_proved import T6, full_check

def reduced(N, g, U, V, R):
    """Recover (p,q,r,e) from a reduced tuple, or None if the system fails."""
    NN = N * N
    a, b = g * U + NN, g * V + NN
    if (g * U) % N or (g * V) % N:          # row below the quiddity is integral
        return None
    if a % R or b % R:                       # p and r are integers
        return None
    num = g * g * U * V - NN * NN
    if num <= 0 or num % (R * NN):           # the master identity solves for e
        return None
    e = num // (R * NN)
    if e <= 0 or a % e or b % e:             # e | pq and e | qr
        return None
    if (N * (g * (U + V) + 2 * NN)) % (e * R):   # e | N(p+r)
        return None
    return a // R, R, b // R, e

def check(NMAX=8, BOX=70, RBOX=45, SUFF_NMAX=5):
    ok = True
    print("necessity: every width-six frieze satisfies the reduced system")
    for N in range(2, NMAX + 1):
        S = T6(N)
        for (p, q, r) in S:
            A, B = p * q - N * N, q * r - N * N
            g = gcd(A, B)
            got = reduced(N, g, A // g, B // g, q)
            if got is None or got[:3] != (p, q, r):
                print(f"  FAIL N={N} (p,q,r)=({p},{q},{r})"); ok = False
        print(f"  N={N}: |T(N,6)| = {len(S)}  OK")
    print("sufficiency: every solution of the reduced system is a frieze")
    for N in range(2, SUFF_NMAX + 1):
        NN = N * N; total = 0
        for g in range(1, BOX):
            for U in range(1, BOX):
                for V in range(1, BOX):
                    if gcd(U, V) != 1 or g * g * U * V <= NN * NN:
                        continue
                    for R in range(1, RBOX):
                        got = reduced(N, g, U, V, R)
                        if got is None:
                            continue
                        p, q, r, e = got
                        quid = [F(p, N), F(q, N), F(r, N),
                                F(p * q, e * N), F(e, N), F(q * r, e * N)]
                        total += 1
                        if not full_check(quid, N, 6):
                            print(f"  FAIL N={N} (g,U,V,R)=({g},{U},{V},{R})"); ok = False
        print(f"  N={N}: {total} solutions in the box, all friezes  OK")
    return ok

if __name__ == "__main__":
    sys.exit(0 if check() else 1)
