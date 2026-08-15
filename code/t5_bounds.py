#!/usr/bin/env python3
"""Sharp bounds for the g-free form of T(N,5), and the observed growth.

From uv | N(u+v)+M and N(u+v)+M > 0 one gets uv <= N(u+v)+M, that is

    (u-N)(v-N) <= N^2 + M <= 2N^2                               (hyperbola bound)

since M | N^2. With u <= v this forces (u-N)^2 <= 2N^2, hence u < 3N: the smaller of
the two parameters is bounded LINEARLY in N, not quadratically. The larger satisfies
v | Nu+M, so v <= Nu+M < 3N^2 + N^2 = 4N^2 and v ranges over divisors, giving

    T(N,5) <= 2 * sum_{M | N^2} sum_{u < 3N} d(Nu + M),

whence T(N,5) = O_eps(N^{1+eps}). This script checks the two bounds on the actual
solution sets and reports the growth.
"""
from math import gcd
import sys
sys.path.insert(0, ".")
from t5_reform import divisors


def solutions(N):
    """All (u,v,M) in the g-free form, via the proved bound min(u,v) < 3N."""
    NN = N * N
    out = []
    for M in divisors(NN):
        for u in range(1, 3 * N):
            for v in divisors(N * u + M):
                if v < u or gcd(u, v) != 1:
                    continue
                S = N * (u + v) + M
                if S % (u * v) or (M * S) % (N * u * v):
                    continue
                out.append((u, v, M))
                if u != v:
                    out.append((v, u, M))
    return out


def upper_bound(N):
    return 2 * sum(len(divisors(N * u + M))
                   for M in divisors(N * N) for u in range(1, 3 * N))


if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    print("  N   T(N,5)  max min(u,v)  3N   max (u-N)(v-N)  2N^2   bound  T/bound")
    ok = True
    for N in range(1, hi + 1):
        sol = solutions(N)
        mn = max(min(u, v) for (u, v, _) in sol)
        hyp = max((u - N) * (v - N) for (u, v, _) in sol)
        ub = upper_bound(N)
        ok &= (mn < 3 * N) and (hyp <= 2 * N * N) and (len(sol) <= ub)
        print(f"  {N:3d} {len(sol):7d} {mn:11d} {3*N:5d} {hyp:14d} {2*N*N:6d} {ub:7d}"
              f"  {len(sol)/ub:7.4f}")
    print()
    print("min(u,v) < 3N, (u-N)(v-N) <= 2N^2, and T <= bound, all N tested:", ok)
