#!/usr/bin/env python3
"""Certificate for VicoEnum/Clockwise.lean and VicoEnum/PathFriezeIso.lean.

Checks that the pentagons built from Ford triples satisfy, as integers, the two
conditions of the classification exactly as they are defined in Lean:

  Clockwise v n :  b_i > 0 for 0 < i < n,  and  fdet (v j) (v i) > 0 for j < i < n
  Minimal   v n :  gcd of all fdet (v j) (v i) is 1

The first is positivity of the frieze, cross multiplied; the second is what makes the
correspondence a bijection rather than a surjection.
"""
import sys
from math import gcd
from ford_to_pentagon import ford_triples, quiddity_from_pair, pentagon, det


def run(primes=(5, 7, 11, 13, 17, 19, 23, 29, 31)):
    tot, bad = 0, 0
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
            tot += 1
            msgs = []
            if any(V[i][1] <= 0 for i in range(1, 5)):
                msgs.append("second coordinate not positive")
            for i in range(5):
                for j in range(i):
                    if det(V[j], V[i]) <= 0:
                        msgs.append(f"fdet({j},{i}) = {det(V[j], V[i])} not positive")
            G = 0
            for i in range(5):
                for j in range(5):
                    G = gcd(G, abs(det(V[j], V[i])))
            if G != 1:
                msgs.append(f"not minimal, gcd = {G}")
            if msgs:
                bad += 1
                print(f"  p={p} triple {(s,t,m)}: " + "; ".join(msgs[:3]))
    print(f"Clockwise and Minimal verified on {tot} pentagons, failures {bad}")
    return bad == 0


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
