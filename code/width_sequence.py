#!/usr/bin/env python3
"""T(N,n) for fixed N across widths, proved-complete.

The search box is the Cuntz-Holm entry bound a_i <= (n-4)N^2 + 2N, VERIFIED in the
library, so the counts are complete and not merely stable under an increasing cutoff.
A frieze of width n is determined by a_0..a_{n-4} through the continuants, so the sweep
runs over those and closes the cycle by Proposition 3.1.

Validated against T(1,n) = Catalan(n-2) and against the tabulated T(N,5), T(N,6).
"""
import sys
import itertools
from fractions import Fraction as F


def cont(lst):
    km1, k0 = F(0), F(1)
    for x in lst:
        km1, k0 = k0, x * k0 - km1
    return k0


def full_check(quid, N, n):
    rows = [[F(0)] * n, [F(1)] * n, list(quid)]
    for rr in range(3, n + 1):
        prev, prev2 = rows[rr - 1], rows[rr - 2]
        cur = []
        for j in range(n):
            d = prev2[(j + 1) % n]
            if d == 0:
                return False
            cur.append((prev[j] * prev[(j + 1) % n] - 1) / d)
        rows.append(cur)
    if any(x != 1 for x in rows[n - 1]) or any(x != 0 for x in rows[n]):
        return False
    for rr in range(2, n - 1):
        for x in rows[rr]:
            if x <= 0 or (x * N).denominator != 1:
                return False
    return True


def T(N, n):
    P = ((n - 4) * N * N + 2 * N) * N
    found = set()
    for nums in itertools.product(range(1, P + 1), repeat=n - 3):
        a = [F(x, N) for x in nums]
        D = cont(a)
        if D <= 0:
            continue
        q = a + [(cont(a[:-1]) + 1) / D, D, (cont(a[1:]) + 1) / D]
        if any(x <= 0 or (x * N).denominator != 1 for x in q):
            continue
        if full_check(q, N, n):
            found.add(tuple(q))
    return len(found)


def run():
    catalan = {5: 5, 6: 14, 7: 42, 8: 132}
    ok = True
    for n, c in catalan.items():
        v = T(1, n)
        if v != c:
            ok = False
            print(f"  T(1,{n}) = {v}, expected Catalan {c}")
    for n, c in {5: 20, 6: 102, 7: 511}.items():
        v = T(2, n)
        if v != c:
            ok = False
            print(f"  T(2,{n}) = {v}, expected {c}")
    print("width sequence: T(1,n) matches Catalan and T(2,n) matches the table"
          if ok else "width sequence: MISMATCH")
    return ok


if __name__ == "__main__":
    if len(sys.argv) == 3:
        N, n = int(sys.argv[1]), int(sys.argv[2])
        print(f"T({N},{n}) = {T(N, n)}")
    else:
        sys.exit(0 if run() else 1)
