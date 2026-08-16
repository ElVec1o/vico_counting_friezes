#!/usr/bin/env python3
"""Certificate for VicoEnum/FibreOrbit.lean.

fibre_eq_orbit states that two paths have the same frieze exactly when they differ by an
integer matrix of determinant one.  The forward direction extracts the matrix entries from
the transfer map by linearity; this script checks, on pentagons built from Ford triples and
their SL2(Z) images, that those entries give determinant one and act correctly.
"""
import sys
import random
from math import gcd
from ford_to_pentagon import ford_triples, quiddity_from_pair, pentagon, det


def tm(a, b, p, q, r, s, P, Q, Rt, S):
    return (a * (-p[1]) * Q[0] - a * (-q[1]) * P[0] + b * (-r[1]) * S[0] - b * (-s[1]) * Rt[0],
            a * p[0] * Q[0] - a * q[0] * P[0] + b * r[0] * S[0] - b * s[0] * Rt[0],
            a * (-p[1]) * Q[1] - a * (-q[1]) * P[1] + b * (-r[1]) * S[1] - b * (-s[1]) * Rt[1],
            a * p[0] * Q[1] - a * q[0] * P[1] + b * r[0] * S[1] - b * s[0] * Rt[1])


def bezout(V):
    for i0 in range(5):
        for j0 in range(5):
            d1 = det(V[i0], V[j0])
            for i1 in range(5):
                for j1 in range(5):
                    d2 = det(V[i1], V[j1])
                    if d2 == 0 or gcd(abs(d1), abs(d2)) != 1:
                        continue
                    for a in range(-80, 81):
                        if (1 - a * d1) % d2 == 0:
                            return a, (1 - a * d1) // d2, i0, j0, i1, j1
    return None


def run(primes=(5, 7, 11, 13, 17, 19), seed=5):
    random.seed(seed)
    tot, bad = 0, 0
    for p in primes:
        for (s_, t_, m_) in ford_triples(p):
            u, v = p * s_, s_ * t_ - 1
            if gcd(u, v) != 1:
                continue
            S_ = p * (u + v + 1)
            if S_ % (u * v):
                continue
            g = S_ // (u * v)
            V, err = pentagon(p, quiddity_from_pair(p, g * u - p, g * v - p))
            if err:
                continue
            V = V[:5]
            w = bezout(V)
            if w is None:
                bad += 1
                print(f"  p={p}: path is not minimal")
                continue
            a, b, i0, j0, i1, j1 = w
            for _ in range(2):
                n1, n2 = random.randint(-3, 3), random.randint(-3, 3)
                M = [[1 + n1 * n2, n1], [n2, 1]]
                Vp = [(M[0][0] * x + M[0][1] * y, M[1][0] * x + M[1][1] * y) for (x, y) in V]
                tot += 1
                m11, m12, m21, m22 = tm(a, b, V[i0], V[j0], V[i1], V[j1],
                                        Vp[i0], Vp[j0], Vp[i1], Vp[j1])
                if m11 * m22 - m12 * m21 != 1:
                    bad += 1
                    print(f"  p={p}: determinant {m11*m22-m12*m21} != 1")
                    continue
                if any((m11 * V[k][0] + m12 * V[k][1], m21 * V[k][0] + m22 * V[k][1]) != Vp[k]
                       for k in range(5)):
                    bad += 1
                    print(f"  p={p}: matrix does not carry v to v'")
    print(f"fibre_eq_orbit: {tot} (path, SL2 image) pairs, determinant one and correct "
          f"action; failures {bad}")
    return bad == 0


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
