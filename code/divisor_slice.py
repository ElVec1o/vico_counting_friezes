#!/usr/bin/env python3
"""Certificate for VicoEnum/DivisorSum.lean.

The cubic auv = n+u+v factors on each a-slice: multiplying by a gives
(au-1)(av-1) = an+1, so the solutions with a given a are the divisors d of an+1 with
d congruent to -1 mod a, and the congruence on the complementary divisor is automatic.
Hence

    C(n) = sum over a = 1..n+2 of #{ d | an+1 : d = -1 mod a }.

Checked against a brute-force count of the cubic, for primes and composites alike; the
identity needs no primality.
"""
import sys
from sympy import divisors


def C_brute(n):
    total = 0
    for a in range(1, n + 3):
        for u in range(1, n + 3):
            d = a * u - 1
            if d <= 0 or (n + u) % d:
                continue
            v = (n + u) // d
            if v >= 1 and a * u * v == n + u + v:
                total += 1
    return total


def C_slice(n):
    return sum(sum(1 for d in divisors(a * n + 1) if (d + 1) % a == 0)
               for a in range(1, n + 3))


def run(values=None):
    if values is None:
        values = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
                  67, 71, 73, 79, 83, 89, 97, 101, 103,
                  4, 6, 8, 9, 10, 12, 15, 20, 21, 25, 27]
    bad = 0
    for n in values:
        b, f = C_brute(n), C_slice(n)
        if b != f:
            bad += 1
            print(f"  n={n}: brute {b} != slice sum {f}")
    print(f"slice formula checked on {len(values)} values, failures {bad}")
    return bad == 0


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
