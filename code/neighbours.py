#!/usr/bin/env python3
"""Step 1: do the maximisers always have both neighbours minimal?
   Step 2 setup: verify a_0 = s + x with 0 <= x < N.
"""
from fractions import Fraction as F
import sys
sys.path.insert(0, ".")
from verify_width5_proved import T5, spf_sieve, factor
from verify_width6_proved import T6
from explore_width7 import width7


def cycles5(N, spf):
    out = []
    for (p, q) in T5(N, spf, factor(N * N, spf) if N > 1 else {}):
        e = p * q - N * N
        out.append([F(p, N), F(q, N), F(N * N * (p + N) // e, N),
                    F(e // N, N), F(N * N * (q + N) // e, N)])
    return out


def cycles6(N):
    out = []
    for (p, q, r) in T6(N):
        e = (p * q * r - N * N * (p + r)) // (N * N)
        out.append([F(p, N), F(q, N), F(r, N), F(p * q, e * N), F(e, N), F(q * r, e * N)])
    return out


def check(n, N, cycs):
    """For every frieze, look at every entry that attains the global max, and
    report whether both its neighbours equal 1/N."""
    gmax = max(max(c) for c in cycs)
    total = both = neither = 0
    counter = None
    for c in cycs:
        m = len(c)
        for i in range(m):
            if c[i] == gmax:
                total += 1
                lo, hi = c[(i - 1) % m], c[(i + 1) % m]
                if lo == F(1, N) and hi == F(1, N):
                    both += 1
                else:
                    neither += 1
                    if counter is None:
                        counter = (i, [str(z) for z in c])
    print(f"  n={n} N={N}: global max {gmax}; {total} maximal entries, "
          f"{both} with both neighbours = 1/N, {neither} without")
    if counter:
        print(f"      counterexample at index {counter[0]}: {counter[1]}")


if __name__ == "__main__":
    spf = spf_sieve(6 ** 3 + 2 * 36 + 20)
    print("Step 1: neighbours of the maximal entry")
    for N in (2, 3, 4):
        check(5, N, cycles5(N, spf))
    for N in (2, 3):
        check(6, N, cycles6(N))
    for N in (2, 3):
        check(7, N, [[F(t, N) for t in tup[4]] for tup in width7(N, 12 * N * N + 12)])
