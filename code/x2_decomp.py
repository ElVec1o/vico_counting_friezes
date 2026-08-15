#!/usr/bin/env python3
"""Divisor-indexed decomposition of T(N,5), and a width-6 probe.

N | gM is equivalent to d_M | g with d_M = N/gcd(N,M). Writing g = d_M h decouples
the two conditions and grades the count by the divisors of N^2:

    T(N,5) = sum over M | N^2 of  #{(h,u,v) : d_M h u v = N(u+v)+M, gcd(u,v)=1, ...}
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


def T_decomp(N, per_M=False):
    total, parts = 0, {}
    for M in divisors(N * N):
        dM = N // gcd(N, M)
        sols = set()
        for u in range(1, 2 * N + M + 1):
            for v in divisors(N * u + M):
                if v < u or gcd(u, v) != 1: continue
                num = N * (u + v) + M
                if num % (u * v): continue
                g = num // (u * v)
                if g % dM: continue            # N | gM  <=>  d_M | g
                for (a, b) in ((u, v), (v, u)):
                    x, y = g * a - N, g * b - N
                    if x > 0 and y > 0: sols.add((x, y))
        parts[M] = len(sols); total += len(sols)
    return (total, parts) if per_M else total


if __name__ == "__main__":
    spf = spf_sieve(21 ** 3 + 2 * 441 + 30)
    print("  N   T(N,5) direct   decomposition   equal")
    ok = True
    for N in range(1, 21):
        a = len(T5(N, spf, factor(N * N, spf) if N > 1 else {}))
        b = T_decomp(N)
        ok &= (a == b); print(f"{N:3d} {a:14d} {b:15d}   {a == b}")
    print()
    print("decomposition verified:", ok)
    print()
    for N in (12, 16, 18):
        t, parts = T_decomp(N, per_M=True)
        nz = {M: c for M, c in parts.items() if c}
        print(f"  N={N}: total {t}, contributions by M | N^2: {nz}")
