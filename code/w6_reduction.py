#!/usr/bin/env python3
"""Width-6 analogue of the Markov reduction (I21: tool or trick?).

Width 5:  g u v = N(u+v) + M,       M | N^2,   N  | gM
Width 6:  h (s t q) = N^2(s+t) + M', M' | qN^2, N^2 | hM'

with h = gcd(p,r), p = hs, r = ht, gcd(s,t) = 1, and M' := hstq - N^2(s+t).
Derived from e | q gcd(p,r) together with ru = N^2(e+p).

Necessity is tested first: every solution found by the verified width-6 enumerator
must satisfy the derived conditions.
"""
from math import gcd
import sys
sys.path.insert(0, ".")
from verify_width6_proved import T6

if __name__ == "__main__":
    print("necessity: do all verified width-6 solutions satisfy the derived conditions?")
    print("  N   solutions   M'|qN^2 ok   N^2|hM' ok   e = hM'/N^2 ok")
    allok = True
    for N in range(1, 9):
        S = sorted(T6(N))
        n1 = n2 = n3 = 0
        for (p, q, r) in S:
            NN = N * N
            e = (p * q * r - NN * (p + r)) // NN
            h = gcd(p, r); s, t = p // h, r // h
            Mp = h * s * t * q - NN * (s + t)
            if Mp != 0 and (q * NN) % Mp == 0: n1 += 1
            if Mp != 0 and (h * Mp) % NN == 0: n2 += 1
            if Mp != 0 and h * Mp == e * NN: n3 += 1
        ok = (n1 == n2 == n3 == len(S))
        allok &= ok
        print(f"{N:3d} {len(S):11d} {n1:12d} {n2:12d} {n3:15d}   {'OK' if ok else 'FAIL'}")
    print()
    print("necessity verified:", allok)
