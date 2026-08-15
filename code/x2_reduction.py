#!/usr/bin/env python3
"""Step 2 of the exhaustion sweep: reduce T(p,5) to a Markov-type Diophantine count.

Claim to test. With e = pf, the width-5 conditions become xy = p(f+p) and
f | p*gcd(x+p, y+p). Writing g = gcd(x+p, y+p), x+p = gu, y+p = gv with gcd(u,v)=1,
one gets f = gw with w | p, hence w in {1,p} for prime p, and

        g u v = p (u + v + w).

If the correspondence (x,y) <-> (g,u,v,w) is a bijection onto the positive solutions
with x,y > 0, then T(p,5) is the number of such solutions.
"""
from math import gcd
import sys
sys.path.insert(0, ".")


def T_direct(p):
    """Reference count, by the proved-complete enumeration."""
    from verify_width5_proved import T5, spf_sieve, factor
    spf = spf_sieve(p ** 3 + 2 * p * p + p + 10)
    return len(T5(p, spf, factor(p * p, spf) if p > 1 else {}))


def divisors(n):
    ds, i = [], 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i: ds.append(n // i)
        i += 1
    return ds


def T_reduced(p):
    """Solutions of g u v = p(u+v+w), w in {1,p}, gcd(u,v)=1, x,y > 0.

    The equation is symmetric in u and v. Taking u <= v gives uv <= p(2v+w), hence
    u <= 2p + pw. For each such u, the equation forces v | p(u+w), so v ranges over
    divisors rather than over a box: with v = 1 the variable u is unbounded by the
    inequality and only the divisibility constrains it.
    """
    sols = set()
    for w in ({1, p} if p > 1 else {1}):
        for u in range(1, 2 * p + p * w + 1):
            for v in divisors(p * (u + w)):
                if v < u:
                    continue
                from math import gcd as _g
                if _g(u, v) != 1:
                    continue
                num = p * (u + v + w)
                if num % (u * v):
                    continue
                g = num // (u * v)
                for (uu, vv) in ((u, v), (v, u)):
                    x, y = g * uu - p, g * vv - p
                    if x <= 0 or y <= 0:
                        continue
                    if _g(x + p, y + p) != g:
                        continue
                    sols.add((x, y))
    return len(sols)


if __name__ == "__main__":
    print("  p   T(p,5) direct   reduced count   equal")
    ok = True
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        a, b = T_direct(p), T_reduced(p)
        ok &= (a == b)
        print(f"{p:3d} {a:14d} {b:15d}   {a == b}")
    print()
    print("reduction verified:" , ok)
