#!/usr/bin/env python3
"""T(N,5) for general N: the corrected Markov-type count.

With e = Nf, x+N = gu, y+N = gv, gcd(u,v)=1 and M := guv - N(u+v):
    f = gM/N,   f is a positive integer  <=>  M > 0 and N | gM,
    f | Ng                               <=>  M | N^2.
The squarefree case is where N | gM collapses to N | M, so that M = Nw with w | N.
"""
from math import gcd
import sys
sys.path.insert(0, ".")
from verify_width5_proved import T5, spf_sieve, factor


def divisors(n):
    ds, i = [], 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i: ds.append(n // i)
        i += 1
    return sorted(ds)


def T_general(N):
    sols = set()
    for M in divisors(N * N):
        for u in range(1, 2 * N + M + 1):
            for v in divisors(N * u + M):
                if v < u or gcd(u, v) != 1:
                    continue
                num = N * (u + v) + M
                if num % (u * v):
                    continue
                g = num // (u * v)
                if (g * M) % N:
                    continue
                for (a, b) in ((u, v), (v, u)):
                    x, y = g * a - N, g * b - N
                    if x <= 0 or y <= 0:
                        continue
                    if gcd(x + N, y + N) != g:
                        continue
                    sols.add((x, y))
    return len(sols)


if __name__ == "__main__":
    spf = spf_sieve(25 ** 3 + 2 * 625 + 30)
    print("  N   T(N,5) direct   general count   equal   squarefree")
    ok = True
    for N in range(1, 25):
        a = len(T5(N, spf, factor(N * N, spf) if N > 1 else {}))
        b = T_general(N)
        sf = all(N % (q * q) for q in range(2, N + 1))
        ok &= (a == b)
        print(f"{N:3d} {a:14d} {b:15d}   {str(a==b):5s}   {sf}")
    print()
    print("general reduction verified:", ok)
