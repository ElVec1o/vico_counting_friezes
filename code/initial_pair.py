#!/usr/bin/env python3
"""Certificate for the canonical initial pair (VicoEnum/Surjectivity.lean).

With [v0,v1] = R every vertex is m_{i,0} v1 - m_{i,1} v0, so realising a prescribed frieze
as a path is the choice of an initial pair.  The choice is canonical: writing g0 for the
gcd of the numerators in column zero and K for the gcd of the frieze,

    v0 = (g0/K, 0),     v1 = (e, N/g0),

which has [v0,v1] = N/K = R.  The second coordinate of every vertex is then integral
automatically, being mu_i / g0 (second_coord_integral, VERIFIED).  What is checked here is
the remaining congruence in the single unknown e.

The weaker choice d = 1 is NOT sufficient: it fails for 15 friezes at N = 12.
"""
import sys
from fractions import Fraction as F
from math import gcd


def quid5(a0, a1):
    D = a0 * a1 - 1
    return None if D == 0 else [a0, a1, (a0 + 1) / D, D, (a1 + 1) / D]


def inlat(x, N):
    return (x * N).denominator == 1


def friezes5(N, LIM):
    out = set()
    for pn in range(1, LIM + 1):
        for qn in range(1, LIM + 1):
            q = quid5(F(pn, N), F(qn, N))
            if q is None or any(x <= 0 or not inlat(x, N) for x in q):
                continue
            r3 = [q[j] * q[(j + 1) % 5] - 1 for j in range(5)]
            if any(x <= 0 or not inlat(x, N) for x in r3):
                continue
            out.add(tuple(q))
    return sorted(out)


def frieze_array(q, n):
    m = {}
    for j in range(n + 2):
        m[(j, j)] = F(0)
        m[(j + 1, j)] = F(1)
        for i in range(j + 2, n + 2):
            m[(i, j)] = q[i % n] * m[(i - 1, j)] - m[(i - 2, j)]
    return m


def try_with_d(q, N, K, n, d):
    R = N // K
    if d == 0 or R % d:
        return None
    b = R // d
    m = frieze_array(q, n)
    col0 = [m[(i, 0)] for i in range(n)]
    col1 = [(-F(1) if i == 0 else m[(i, 1)]) for i in range(n)]
    for e in range(0, N):
        V, ok = [], True
        for i in range(n):
            x = col0[i] * e - col1[i] * d
            y = col0[i] * b
            if x.denominator != 1 or y.denominator != 1:
                ok = False
                break
            V.append((int(x), int(y)))
        if not ok:
            continue
        if any(R % (gcd(abs(a), abs(bb)) or R) for a, bb in V):
            continue
        if any(V[i][0] * V[(i + 1) % n][1] - V[i][1] * V[(i + 1) % n][0] not in (R, -R)
               for i in range(n - 1)):
            continue
        return e
    return None


def run(NMAX=14):
    total, ok = 0, 0
    for N in range(1, NMAX + 1):
        for q in friezes5(N, N ** 3 + 2 * N * N):
            r3 = [q[j] * q[(j + 1) % 5] - 1 for j in range(5)]
            nums = [int(x * N) for x in q] + [int(x * N) for x in r3]
            K = 0
            for t in nums:
                K = gcd(K, t)
            total += 1
            hit = False
            for off in range(5):
                qq = [q[(i + off) % 5] for i in range(5)]
                m = frieze_array(qq, 5)
                g0 = 0
                for i in range(5):
                    g0 = gcd(g0, int(m[(i, 0)] * N))
                if g0 % K or (N // K) % (g0 // K):
                    continue
                if try_with_d(qq, N, K, 5, g0 // K) is not None:
                    hit = True
                    break
            if hit:
                ok += 1
            else:
                print(f"  N={N}: no initial pair with d = g0/K for {[str(x) for x in q]}")
    print(f"canonical initial pair d = g0/K: {ok}/{total} friezes, N <= {NMAX}")
    return ok == total


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
