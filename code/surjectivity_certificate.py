#!/usr/bin/env python3
"""Certificate for VicoEnum/Surjectivity.lean.

Two claims, checked on the pentagons built from Ford triples.

1. The recurrence is forced.  For three consecutive vertices of a path in F_p, where
   det(u,w) = det(w,x) = p, the three-vector Plucker identity gives

       p x = det(u,x) w - p u,

   so the path satisfies the frieze recurrence with coefficient det(u,x)/p, whether or
   not it was built that way.  Checked here by recovering the recurrence from the path
   alone, without consulting the quiddity it came from.

2. Transfer.  Two paths with the same frieze, the first minimal, are related by the
   explicit integral formula of Theorem 12.x.  Checked by applying random SL2(Z)
   matrices and recovering the image from the original plus a Bezout witness.
"""
import sys
import random
from math import gcd
from ford_to_pentagon import ford_triples, quiddity_from_pair, pentagon


def det(u, w):
    return u[0] * w[1] - u[1] * w[0]


def pentagons(primes):
    for p in primes:
        for (s, t, m) in ford_triples(p):
            u, v = p * s, s * t - 1
            if gcd(u, v) != 1:
                continue
            S = p * (u + v + 1)
            if S % (u * v):
                continue
            g = S // (u * v)
            V, err = pentagon(p, quiddity_from_pair(p, g * u - p, g * v - p))
            if err:
                continue
            yield p, V[:5]


def bezout_witness(V):
    """Indices and coefficients realising minimality: a*det+b*det = 1."""
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


def run(primes=(5, 7, 11, 13, 17, 19), seed=11):
    random.seed(seed)
    forced, transfers, bad = 0, 0, 0
    for p, V in pentagons(primes):
        for i in range(1, 4):
            u, w, x = V[i - 1], V[i], V[i + 1]
            if det(u, w) != p or det(w, x) != p:
                continue
            forced += 1
            if (p * x[0], p * x[1]) != (det(u, x) * w[0] - p * u[0],
                                        det(u, x) * w[1] - p * u[1]):
                bad += 1
                print(f"  p={p}: forced recurrence fails at index {i}")
        wit = bezout_witness(V)
        if wit is None:
            bad += 1
            print(f"  p={p}: no Bezout witness, path is not minimal")
            continue
        a, b, i0, j0, i1, j1 = wit
        for _ in range(3):
            n1, n2 = random.randint(-3, 3), random.randint(-3, 3)
            M = [[1 + n1 * n2, n1], [n2, 1]]
            Vp = [(M[0][0] * q + M[0][1] * r, M[1][0] * q + M[1][1] * r) for (q, r) in V]
            transfers += 1
            if any(det(V[i], V[j]) != det(Vp[i], Vp[j]) for i in range(5) for j in range(5)):
                bad += 1
                print(f"  p={p}: SL2 image has a different frieze")
                continue
            for k in range(5):
                exp = tuple(
                    a * det(V[i0], V[k]) * Vp[j0][c] - a * det(V[j0], V[k]) * Vp[i0][c]
                    + b * det(V[i1], V[k]) * Vp[j1][c] - b * det(V[j1], V[k]) * Vp[i1][c]
                    for c in (0, 1))
                if exp != Vp[k]:
                    bad += 1
                    print(f"  p={p}: transfer wrong at k={k}")
                    break
    print(f"forced recurrence: {forced} triples of consecutive vertices")
    print(f"transfer: {transfers} (path, SL2 image) pairs")
    print(f"failures: {bad}")
    return bad == 0


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
