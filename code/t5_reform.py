#!/usr/bin/env python3
"""T(N,5) with g eliminated, and what the growth actually looks like.

Theorem thm:markov counts quadruples (g,u,v,M) with

    g u v = N(u+v) + M,  M | N^2,  N | gM,  gcd(u,v)=1,  gu > N,  gv > N.

Two simplifications, tested here.

  (1) g is determined: g = (N(u+v)+M)/(uv), so the equation is the divisibility
      uv | N(u+v)+M, and N | gM becomes N uv | M(N(u+v)+M).
  (2) The two positivity conditions are automatic. Multiplying gu > N by v > 0 gives
      guv > Nv, that is N(u+v)+M > Nv, that is Nu + M > 0, true for u, M > 0.

So      T(N,5) = #{(u,v,M) : gcd(u,v)=1, M | N^2, uv | N(u+v)+M, N uv | M(N(u+v)+M)}.

Search bounds, proved: with gcd(u,v)=1 and u <= v,
    uv <= N(u+v)+M <= 2Nv + M  =>  u <= 2N + M/v <= 2N + N^2,
and v | N(u+v)+M with v | Nv gives v | Nu+M, so v <= Nu + M <= N^3 + 3N^2.
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
            if i != n // i:
                ds.append(n // i)
        i += 1
    return sorted(ds)


def T5_reform(N):
    """The count with g eliminated.

    The bound u <= N^2 + 2N holds for min(u,v) only, so the sweep takes u to be the
    smaller of the two and counts the ordered pair twice when u < v. Since gcd(u,v) = 1,
    u = v happens only at u = v = 1.
    """
    NN = N * N
    total = 0
    for M in divisors(NN):
        for u in range(1, NN + 2 * N + 1):
            for v in divisors(N * u + M):
                if v < u or gcd(u, v) != 1:
                    continue
                S = N * (u + v) + M
                if S % (u * v) or (M * S) % (N * u * v):
                    continue
                total += 1 if u == v else 2
    return total


if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    spf = spf_sieve(hi ** 3 + 2 * hi * hi + hi + 10)
    print("  N   T(N,5)   reformulated   equal")
    ok = True
    for N in range(1, hi + 1):
        t = len(T5(N, spf, factor(N * N, spf) if N > 1 else {}))
        r = T5_reform(N)
        ok &= (t == r)
        print(f"  {N:3d} {t:8d} {r:14d}   {t == r}")
    print()
    print("g-free reformulation agrees with T(N,5):", ok)
