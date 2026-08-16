#!/usr/bin/env python3
"""The initial-pair construction at width six (VicoEnum/InitialPair.lean).

initial_pair_congruence is width-uniform: it uses only the frieze recurrence and the
divisibility of the numerators by K.  It was originally checked at width five only.  This
script checks it at width six, against the proved width-six enumeration.
"""
import sys
from fractions import Fraction as F
from math import gcd
from verify_width6_proved import T6


def frieze_rows(quid, N, n):
    rows = [[F(0)] * n, [F(1)] * n, list(quid)]
    for rr in range(3, n + 1):
        prev, prev2 = rows[rr - 1], rows[rr - 2]
        cur = []
        for j in range(n):
            d = prev2[(j + 1) % n]
            if d == 0:
                return None
            cur.append((prev[j] * prev[(j + 1) % n] - 1) / d)
        rows.append(cur)
    return rows


def cols01(quid, n):
    c0, c1 = [F(0), F(1)], [F(-1), F(0)]
    for i in range(2, n + 1):
        c0.append(quid[i % n] * c0[i - 1] - c0[i - 2])
        c1.append(quid[i % n] * c1[i - 1] - c1[i - 2])
    return c0, c1


def bezout_list(vals):
    g, lam = 0, [0] * len(vals)
    for idx, v in enumerate(vals):
        if v == 0:
            continue
        if g == 0:
            g = abs(v)
            lam = [0] * len(vals)
            lam[idx] = 1 if v > 0 else -1
        else:
            a, b = g, v
            x0, x1 = 1, 0
            while b:
                qq = a // b
                a, b = b, a - qq * b
                x0, x1 = x1, x0 - qq * x1
            lam = [x0 * t for t in lam]
            lam[idx] += (a - x0 * g) // v
            g = a
    return g, lam


def run(NMAX=8):
    tot, ok, bad = 0, 0, []
    for N in range(2, NMAX + 1):
        for (p, q, r) in T6(N):
            NN = N * N
            e6 = (p * q * r - NN * (p + r)) // NN
            quid = [F(p, N), F(q, N), F(r, N), F(p * q, e6 * N), F(e6, N), F(q * r, e6 * N)]
            rows = frieze_rows(quid, N, 6)
            if rows is None:
                continue
            K = 0
            for x in (int(y * N) for rr in rows[2:5] for y in rr):
                K = gcd(K, x)
            c0, c1 = cols01(quid, 6)
            mu = [int(c0[i] * N) for i in range(6)]
            nu = [int(c1[i] * N) for i in range(6)]
            g0 = 0
            for t in mu:
                g0 = gcd(g0, t)
            tot += 1
            if K == 0 or g0 % K or (N // K) % (g0 // K):
                bad.append((N, (p, q, r), "scale"))
                continue
            d = g0 // K
            g, lam = bezout_list(mu)
            if g != g0:
                bad.append((N, (p, q, r), "bezout"))
                continue
            S = sum(l * x for l, x in zip(lam, nu))
            if S % K:
                bad.append((N, (p, q, r), "K nmid S"))
                continue
            e = S // K
            if all((mu[i] * e - nu[i] * d) % N == 0 for i in range(6)):
                ok += 1
            else:
                bad.append((N, (p, q, r), "congruence"))
    for b in bad[:5]:
        print(f"  failure {b}")
    print(f"initial pair at width six: {ok}/{tot} friezes, N <= {NMAX}, failures {len(bad)}")
    return not bad


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
