#!/usr/bin/env python3
"""The two terms of T(p,5) at a prime, and the orbit structure behind 3A - 2B = 15.

At a prime, Proposition prop:support leaves M in {p, p^2} (M = 1 is excluded because
N uv | M(N(u+v)+M) would force p | 1), so T(p,5) = A(p) + B(p) with

    A(p) = #{(u,v) coprime : uv | p(u+v+1)},   B(p) = #{(u,v) coprime : uv | p(u+v+p)}.

Two statements are tested.

  IDENTITY   3 A(p) - 2 B(p) = 15  for every prime p.
  ORBITS     every Z/5 rotation orbit holds exactly 2 cycles with M = p and 3 with
             M = p^2, except the single orbit of the five pairs of prop:rigid5, which
             holds 5 and 0. This implies the identity.
"""
from fractions import Fraction as F
from math import gcd
from collections import Counter
import sys
sys.path.insert(0, ".")
from t5_bounds import solutions
from t5_reform import divisors


def AB(p):
    A = B = 0
    for (u, v, M) in solutions(p):
        if M == p: A += 1
        elif M == p * p: B += 1
        else: raise AssertionError(f"unexpected M={M} at p={p}")
    return A, B


def cycles(p):
    """Every width-5 quiddity cycle over (1/p)Z, tagged by its M."""
    N, out = p, {}
    for (u, v, M) in solutions(N):
        S = N * (u + v) + M
        g = S // (u * v)
        x, y = g * u - N, g * v - N
        e = x * y - N * N
        out[(F(x, N), F(y, N), F(N * (x + N), e), F(e, N * N), F(N * (y + N), e))] = M
    return out


def orbit_profiles(p):
    cy = cycles(p)
    seen, prof = set(), Counter()
    for q in cy:
        if q in seen: continue
        orb = [tuple(q[(i + k) % 5] for i in range(5)) for k in range(5)]
        assert all(o in cy for o in orb), f"orbit not closed at p={p}"
        seen.update(orb)
        c = Counter(cy[o] for o in orb)
        prof[(c[p], c[p * p])] += 1
    return len(seen) // 5, prof


if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    primes = [q for q in range(3, hi) if all(q % r for r in range(2, int(q ** .5) + 1))]
    bad_id = bad_orb = 0
    print("   p     A     B   3A-2B    R   orbit profiles")
    for q in primes:
        A, B = AB(q)
        idok = (3 * A - 2 * B == 15)
        bad_id += not idok
        line = f" {q:4d} {A:5d} {B:5d}  {3*A-2*B:6d}"
        if q <= 53:
            R, prof = orbit_profiles(q)
            ok = sorted(prof.items()) == [((2, 3), R - 1), ((5, 0), 1)]
            bad_orb += not ok
            line += f"  {R:4d}   " + "  ".join(
                f"{a}:{b} x{n}" for (a, b), n in sorted(prof.items()))
        print(line)
    print()
    print(f"primes tested: {len(primes)}  (3..{hi})")
    print(f"3A - 2B = 15 violations: {bad_id}")
    print(f"orbit-profile violations (p <= 53): {bad_orb}")

    # T(p,5)/sqrt(p) over the primes p >= 5, the ratio quoted in the paper.
    import math
    rs = [(q, sum(AB(q)) / math.sqrt(q)) for q in primes if q >= 5]
    if rs:
        allm = sum(r for _, r in rs) / len(rs)
        big = [r for q, r in rs if q > 400]
        print(f"\nT(p,5)/sqrt(p) over the {len(rs)} primes 5 <= p <= {hi}: mean {allm:.1f}")
        if big:
            print(f"   over p > 400 ({len(big)} primes): mean {sum(big)/len(big):.1f}")
