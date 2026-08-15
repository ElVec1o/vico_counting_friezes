#!/usr/bin/env python3
"""The conjectured extremal family: the rational fan.

    F(n,N) = ( (n-4)N^2+2N , 1/N , N+1 , 2,...,2 (n-5 times) , N+1 , 1/N )

At N=1 this is (n-2, 1, 2,...,2, 1), the fan triangulation of the n-gon, which
attains the Conway-Coxeter bound. This script checks that F(n,N) is a genuine
positive frieze over (1/N)Z for every n and N in an explicit range, which makes
the uniform bound sharp.
"""
from fractions import Fraction as F

def fan(n, N):
    return [F((n-4)*N*N + 2*N), F(1, N), F(N+1)] + [F(2)]*(n-5) + [F(N+1), F(1, N)]

def is_frieze(quid, N):
    n = len(quid)
    rows = [[F(0)]*n, [F(1)]*n, list(quid)]
    for r in range(3, n+1):
        prev, prev2 = rows[r-1], rows[r-2]
        cur = []
        for j in range(n):
            d = prev2[(j+1) % n]
            if d == 0: return False, "zero divisor"
            cur.append((prev[j]*prev[(j+1) % n] - 1)/d)
        rows.append(cur)
    if any(x != 1 for x in rows[n-1]): return False, "row n-1 not all ones"
    if any(x != 0 for x in rows[n]):   return False, "row n not all zeros"
    for r in range(2, n-1):
        for x in rows[r]:
            if x <= 0: return False, f"non-positive entry {x} in row {r}"
            if (x*N).denominator != 1: return False, f"entry {x} outside (1/N)Z"
    return True, "ok"

if __name__ == "__main__":
    bad = []
    for n in range(5, 26):
        for N in range(1, 21):
            ok, why = is_frieze(fan(n, N), N)
            if not ok: bad.append((n, N, why))
    print(f"fan family checked for n = 5..25, N = 1..20  ({21*20} cases)")
    print(f"failures: {bad if bad else 'none'}")
    print()
    print("maximum entry equals (n-4)N^2+2N in every case:",
          all(max(fan(n,N)) == F((n-4)*N*N+2*N) for n in range(5,26) for N in range(1,21)))
    print()
    for (n,N) in ((5,3),(7,2),(9,4)):
        print(f"  n={n}, N={N}: {[str(x) for x in fan(n,N)]}")
