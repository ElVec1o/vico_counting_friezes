#!/usr/bin/env python3
"""Two independent checks on the width-6 enumeration.

(1) Small-N exhaustive brute force over (p,q,r) in a generous box, sharing no
    code path with the divisor-based enumerator.
(2) Closure of the solution set under the dihedral action on the quiddity cycle.
    Rotating a genuine frieze gives a genuine frieze, so a COMPLETE solution set
    must be closed. An enumeration that misses solutions will almost always fail
    this, because the missing solutions are rotations of ones it did find.
"""
from fractions import Fraction as F
import sys
sys.path.insert(0, ".")
from verify_width6_proved import T6, full_check


def brute(N, K):
    out = set()
    NN = N * N
    for p in range(1, K + 1):
        for q in range(1, K + 1):
            if p * q <= NN:
                continue
            for r in range(1, K + 1):
                E = p * q * r - NN * (p + r)
                if E <= 0 or E % NN:
                    continue
                e = E // NN
                if (p * q) % e or (q * r) % e:
                    continue
                quid = [F(p, N), F(q, N), F(r, N),
                        F(p * q, e * N), F(e, N), F(q * r, e * N)]
                if full_check(quid, N, 6):
                    out.add((p, q, r))
    return out


def cycle_of(t, N):
    p, q, r = t
    e = (p * q * r - N * N * (p + r)) // (N * N)
    return [F(p, N), F(q, N), F(r, N), F(p * q, e * N), F(e, N), F(q * r, e * N)]


def closure_test(S, N):
    """Every rotation and reversal of every solution must be a solution."""
    missing = []
    for t in S:
        c = cycle_of(t, N)
        for k in range(6):
            for cyc in (c[k:] + c[:k], list(reversed(c))[k:] + list(reversed(c))[:k]):
                key = tuple(int(x * N) for x in cyc[:3])
                if any((x * N).denominator != 1 for x in cyc[:3]):
                    missing.append(("non-integral", t, k))
                elif key not in S:
                    missing.append((t, k, key))
    return missing


if __name__ == "__main__":
    print("(1) exhaustive brute force at small N")
    for N in (4, 5, 6, 7):
        S = T6(N)
        mx = max(max(t) for t in S)
        K = 2 * mx + 4 * N
        B = brute(N, K)
        print(f"    N={N}: divisor method {len(S):5d}   brute force (box {K}) {len(B):5d}   "
              f"identical sets: {S == B}")

    print()
    print("(2) dihedral closure of the solution set")
    sent = {11: 1000, 12: 4959, 13: 912, 15: 5166, 17: 1188, 19: 1294, 20: 9524}
    for N in (11, 12, 13, 15, 17, 19, 20):
        S = T6(N)
        miss = closure_test(S, N)
        print(f"    N={N:3d}: |S|={len(S):6d}  closed under D_6: {not miss}"
              f"   (sent value {sent[N]}, differs by {len(S)-sent[N]:+d})")
