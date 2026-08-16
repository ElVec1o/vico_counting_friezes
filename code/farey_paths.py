#!/usr/bin/env python3
"""P(R), the number of minimal closed clockwise 5-paths in the Farey graph F_R modulo
SL(2,Z), by Mobius inversion of T(N,5). See Theorem thm:farey.
"""
from math import gcd

def divisors(n):
    d, i = [], 1
    while i * i <= n:
        if n % i == 0:
            d += [i, n // i]
        i += 1
    return sorted(set(d))

def mobius(n):
    if n == 1:
        return 1
    r, m, d = 1, n, 2
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            r = -r
        d += 1
    return -r if m > 1 else r

def F(A, B):
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

def T5(N):
    """Theorem thm:fordsum."""
    return sum(F(gcd(N, M), M * gcd(N, M) // N)
               for M in divisors(N * N) if (M * M) % N == 0)

def P(R):
    return sum(mobius(R // d) * T5(d) for d in divisors(R))

def C(p):
    t = 0
    for a in range(1, p + 3):
        for u in range(1, p + 3):
            dd = a * u - 1
            if dd <= 0 or (p + u) % dd:
                continue
            v = (p + u) // dd
            if a * u * v == p + u + v:
                t += 1
    return t

def main(hi=40):
    print("  R    P(R)   P(R)/5   at primes p>=5: 5C(p)")
    for R in range(1, hi + 1):
        pr = P(R)
        assert pr > 0 and pr % 5 == 0, (R, pr)
        isp = R > 1 and all(R % i for i in range(2, int(R ** 0.5) + 1))
        note = ""
        if isp and R >= 5:
            note = f"   5C({R}) = {5 * C(R)}"
            assert pr == 5 * C(R), (R, pr, 5 * C(R))
        print(f" {R:3d} {pr:7d} {pr // 5:8d}{note}")
    print("\nall P(R) positive and divisible by 5; P(p) = 5C(p) at every prime p >= 5 tested")

if __name__ == "__main__":
    main()
