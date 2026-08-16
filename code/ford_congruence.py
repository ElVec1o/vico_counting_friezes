#!/usr/bin/env python3
"""The congruence of Corollary cor:fivedvd, and that it is not termwise.

For each N the terms of Theorem thm:fordsum are printed with the count of those divisible
by five. The sum is always divisible by five; the terms generally are not.
"""
from math import gcd

def divisors(n):
    d, i = [], 1
    while i * i <= n:
        if n % i == 0:
            d += [i, n // i]
        i += 1
    return sorted(set(d))

def F(A, B):
    """#{(u,v) > 0 : gcd(u,v)=1, uv | A(u+v)+B}, ordered pairs."""
    tot = 0
    for u in range(1, 2 * A + B + 1):
        S = A * u + B
        for dd in divisors(S):
            if (dd + A) % u:
                continue
            v = S // dd
            if v < u or gcd(u, v) != 1:
                continue
            tot += 1 if u == v else 2
    return tot

def terms(N):
    out = []
    for M in divisors(N * N):
        e = gcd(N, M)
        d = N // e
        if M % d:
            continue
        out.append(F(e, M // d))
    return out

def main(hi=25):
    bad, tot_terms, div_terms = [], 0, 0
    print("  N   sum   sum mod 5   terms divisible by 5   terms")
    for N in range(1, hi + 1):
        ts = terms(N)
        s = sum(ts)
        tot_terms += len(ts)
        div_terms += sum(1 for t in ts if t % 5 == 0)
        if s % 5:
            bad.append(N)
        print(f" {N:3d} {s:6d} {s % 5:9d} {sum(1 for t in ts if t % 5 == 0):15d}/{len(ts):<4d} {ts}")
    print(f"\nsums not divisible by 5: {bad if bad else 'none'}")
    print(f"terms divisible by 5: {div_terms} of {tot_terms}")

if __name__ == "__main__":
    main()
