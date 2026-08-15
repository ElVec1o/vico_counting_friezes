#!/usr/bin/env python3
"""The uniform gcd condition at widths 5, 6, 7.

For a positive frieze of width n over (1/N)Z with quiddity (a_0,...,a_{n-1}), let
K_k denote the frieze continuant, D = K_{n-3}(a_0,...,a_{n-4}) = E/N^{n-3} with
E = e N^{n-4}, and

    A' := N^{n-4} K_{n-4}(a_0,...,a_{n-5}),   B' := N^{n-4} K_{n-4}(a_1,...,a_{n-4}).

The two outer quiddity entries are (A'+N^{n-4})/(e N^{n-5}) and (B'+N^{n-4})/(e N^{n-5}).
Both lying in (1/N)Z is equivalent to the single condition

    e N^(n-6)  |  gcd(A' + N^(n-4),  B' + N^(n-4)),

read as e | g N^(6-n) when n < 6. This is the mechanism behind the width-5 and
width-6 reductions; here it is tested directly.
"""
from fractions import Fraction as F
from math import gcd
import sys
sys.path.insert(0, ".")
from verify_width5_proved import T5, spf_sieve, factor
from verify_width6_proved import T6
from explore_width7 import width7


def cont(xs):
    """Frieze continuant K_k(x_1..x_k):  K_0 = 1, K_1 = x_1, K_k = x_k K_{k-1} - K_{k-2}."""
    pm2, pm1 = F(0), F(1)
    for x in xs:
        pm2, pm1 = pm1, x * pm1 - pm2
    return pm1


def check(n, N, quids):
    ok = 0
    for a in quids:
        D = cont(a[:n - 3])
        E = D * N ** (n - 3)
        if E.denominator != 1: return None
        E = int(E)
        if E % N ** (n - 4): return None
        e = E // N ** (n - 4)
        Ap = int(cont(a[:n - 4]) * N ** (n - 4))
        Bp = int(cont(a[1:n - 3]) * N ** (n - 4))
        g = gcd(Ap + N ** (n - 4), Bp + N ** (n - 4))
        if n >= 6:
            good = (g % (e * N ** (n - 6)) == 0)
        else:
            good = ((g * N ** (6 - n)) % e == 0)
        ok += good
    return ok, len(quids)


if __name__ == "__main__":
    spf = spf_sieve(9 ** 3 + 2 * 81 + 20)
    print("  n   N   solutions   satisfying the uniform gcd condition")
    allok = True
    for N in range(1, 9):
        q5 = []
        for (p, qq) in T5(N, spf, factor(N * N, spf) if N > 1 else {}):
            e = p * qq - N * N
            q5.append([F(p, N), F(qq, N), F(N * N * (p + N), e * N), F(e, N * N),
                       F(N * N * (qq + N), e * N)])
        r = check(5, N, q5); allok &= (r and r[0] == r[1])
        print(f"  5 {N:3d} {r[1]:11d} {r[0]:38d}")
    for N in range(1, 7):
        q6 = []
        for (p, qq, rr) in T6(N):
            e = (p * qq * rr - N * N * (p + rr)) // (N * N)
            q6.append([F(p, N), F(qq, N), F(rr, N), F(p * qq, e * N), F(e, N), F(qq * rr, e * N)])
        r = check(6, N, q6); allok &= (r and r[0] == r[1])
        print(f"  6 {N:3d} {r[1]:11d} {r[0]:38d}")
    for N in (1, 2, 3):
        q7 = [[F(t, N) for t in tup[4]] for tup in width7(N, 12 * N * N + 12)]
        r = check(7, N, q7); allok &= (r and r[0] == r[1])
        print(f"  7 {N:3d} {r[1]:11d} {r[0]:38d}")
    print()
    print("uniform gcd condition holds everywhere:", allok)
