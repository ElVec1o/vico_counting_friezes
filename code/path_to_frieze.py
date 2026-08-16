#!/usr/bin/env python3
"""Round trip: Ford triple -> pentagon in F_p -> frieze (VicoEnum/PathToFrieze.lean).

Given a vertex sequence with all consecutive determinants equal to R, the array
m_{i,j} = (1/R) det(v_j, v_i) has zero diagonal, ones on the first subdiagonal, and
every adjacent two-by-two minor equal to one.  Those are the defining relations of a
frieze, and the Plucker relation gives them at every width at once.

This script closes the loop on the width-five case: each Ford triple is mapped to a
pentagon and the pentagon is mapped back to a frieze, whose quiddity is checked against
the one the triple came from.
"""
import sys
from fractions import Fraction as Fr
from math import gcd
from ford_to_pentagon import ford_triples, quiddity_from_pair, pentagon, det


def frieze_from_path(V, R, n):
    """m_{i,j} = (1/R) det(v_j, v_i)."""
    return {(i, j): Fr(det(V[j], V[i]), R) for i in range(n + 2) for j in range(n + 2)}


def run(primes=(5, 7, 11, 13, 17, 19, 23)):
    checked, bad = 0, 0
    for p in primes:
        for (s, t, m) in ford_triples(p):
            u, v = p * s, s * t - 1
            if gcd(u, v) != 1:
                continue
            S = p * (u + v + 1)
            if S % (u * v):
                continue
            g = S // (u * v)
            q = quiddity_from_pair(p, g * u - p, g * v - p)
            V, err = pentagon(p, q)
            if err:
                continue
            M = frieze_from_path(V, p, 5)
            checked += 1
            msgs = []
            if any(M[(i, i)] != 0 for i in range(5)):
                msgs.append("diagonal is not zero")
            if any(M[(i + 1, i)] != 1 for i in range(5)):
                msgs.append("first subdiagonal is not one")
            for i in range(5):
                for j in range(5):
                    if M[(i, j)] * M[(i + 1, j + 1)] - M[(i, j + 1)] * M[(i + 1, j)] != 1:
                        msgs.append(f"minor at ({i},{j}) is not one")
                        break
                else:
                    continue
                break
            if sorted(M[(i + 2, i)] for i in range(5)) != sorted(Fr(x, p) for x in q):
                msgs.append("quiddity not recovered")
            if msgs:
                bad += 1
                print(f"  p={p} triple {(s,t,m)}: " + "; ".join(msgs))
    print(f"round trip Ford triple -> pentagon -> frieze: checked {checked}, failures {bad}")
    return bad == 0


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
