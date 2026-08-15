#!/usr/bin/env python3
"""Test the Karpenkov correspondence on frieze quiddities.

Karpenkov (arXiv:math/0604129) Theorem 2.2a: three ordinary lattice angles are the
angles of a lattice triangle iff  ] ltan a, -1, ltan b, -1, ltan c [ = 0, where the
bracket is the continued-fraction continuant (PLUS convention). Theorem 4.8 is the
n-gon version. If quiddity entries are lattice tangents, then interleaving a frieze
quiddity with -1 and taking that continuant should vanish.

Also: for an ordinary lattice angle larctan(m/n) one has ltan = m/n and lsin = m,
so lsin of the angle is the numerator of the quiddity entry in lowest terms. With
the lattice sine rule lsin <= S, the uniform bound would follow from a bound on the
lattice area S.
"""
from fractions import Fraction as F
import sys
sys.path.insert(0, ".")
from fan_family import fan


def cf_continuant(seq):
    """K() = 1, K(a1) = a1, K(..,an) = an*K(..,a_{n-1}) + K(..,a_{n-2})."""
    pm2, pm1 = F(1), F(0)          # K of empty = 1, K of "nothing before" = 0
    for x in seq:
        pm2, pm1 = x * pm2 + pm1, pm2
    return pm2


def interleave(q):
    out = []
    for i, x in enumerate(q):
        if i: out.append(F(-1))
        out.append(x)
    return out


if __name__ == "__main__":
    print("Karpenkov continuant ] a_0, -1, a_1, -1, ..., a_{n-1} [ on frieze quiddities")
    print("  n   N   continuant   quiddity")
    for (n, N) in ((3,1),(4,1),(5,1),(6,1),(7,1),(8,1),(5,2),(7,2),(7,3),(9,2),(11,3)):
        q = fan(n, N) if n >= 5 else ([F(1)]*3 if n == 3 else [F(2),F(1),F(2),F(1)])
        v = cf_continuant(interleave(q))
        print(f"{n:3d} {N:3d} {str(v):>12}   {[str(x) for x in q]}")
    print()
    print("lsin of each angle = numerator of the quiddity entry in lowest terms;")
    print("max lsin over the fan, vs the conjectured bound (n-4)N^2+2N:")
    print("  n   N   max lsin   (n-4)N^2+2N   equal")
    for (n, N) in ((5,2),(6,3),(7,2),(7,3),(9,2),(11,3),(13,4)):
        q = fan(n, N)
        mx = max(x.numerator for x in q)
        pred = (n-4)*N*N + 2*N
        print(f"{n:3d} {N:3d} {mx:10d} {pred:13d}   {mx == pred}")
