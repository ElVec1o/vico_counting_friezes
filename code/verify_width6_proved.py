#!/usr/bin/env python3
"""T(N,6) by a PROVED-complete enumeration.

Parameterisation (frieze continuants, K_3 = a_2(a_0 a_1 - 1) - a_0):

    a_3 = a_0 a_1 / D,   a_4 = D = K_3,   a_5 = a_1 a_2 / D.

With a_0 = p/N, a_1 = q/N, a_2 = r/N and e := (pqr - N^2(p+r))/N^2 one gets
a_3 = pq/(eN), a_4 = e/N, a_5 = qr/(eN), and the row-3 entry a_2 a_3 - 1 = (p+r)/e.

LEMMA (search bound, proved).
  (i)  a_2 a_3 - 1 = (p+r)/e lies in (1/N)Z, so e | N(p+r), hence e <= N(p+r).
  (ii) pqr = N^2(e + p + r) <= N^2(N+1)(p+r).
  (iii) Dividing (ii) by pr:  q <= N^2(N+1)(1/p + 1/r).
        Taking p <= r without loss of generality (the frieze reversal swaps them),
        q <= 2N^2(N+1)/p, that is        p*q <= 2N^2(N+1).
  (iv) r = N^2(e + p)/(pq - N^2) is DETERMINED by (p,q,e), and e | pq.

So the sweep runs over pairs with p*q <= 2N^2(N+1) and divisors e of pq, then
solves for r. Complete by (iii) and (iv). Row 3 is fixed by the glide symmetry of
the frieze, so it carries its own lattice condition; rather than rely on the
derivation, every candidate is expanded to the full 7-row array and every entry
is checked for positivity and for membership in (1/N)Z.
"""
from fractions import Fraction as F
import sys, time


def divisors(n):
    ds, i = [], 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n // i:
                ds.append(n // i)
        i += 1
    return ds


def full_check(quid, N, n):
    """Expand the quiddity to the whole frieze and check every entry."""
    rows = [[F(0)] * n, [F(1)] * n, list(quid)]
    for rr in range(3, n + 1):
        prev, prev2 = rows[rr - 1], rows[rr - 2]
        cur = []
        for j in range(n):
            d = prev2[(j + 1) % n]
            if d == 0:
                return False
            cur.append((prev[j] * prev[(j + 1) % n] - 1) / d)
        rows.append(cur)
    if any(x != 1 for x in rows[n - 1]) or any(x != 0 for x in rows[n]):
        return False
    for rr in range(2, n - 1):
        for x in rows[rr]:
            if x <= 0 or (x * N).denominator != 1:
                return False
    return True


def T6(N):
    NN = N * N
    LIM = 2 * NN * (N + 1)
    sols = set()
    for p in range(1, LIM + 1):
        for q in range(1, LIM // p + 1):
            if p * q <= NN:
                continue
            for e in divisors(p * q):
                num = NN * (e + p)
                den = p * q - NN
                if num % den:
                    continue
                r = num // den
                if r < 1:
                    continue
                if (p * q * r - NN * (p + r)) != e * NN:
                    continue
                quid = [F(p, N), F(q, N), F(r, N),
                        F(p * q, e * N), F(e, N), F(q * r, e * N)]
                if full_check(quid, N, 6):
                    sols.add((p, q, r))
                    sols.add((r, q, p))
    return sols


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    sent = [14, 102, 259, 487, 504, 1197, 648, 1799, 1665, 2322,
            1000, 4959, 912, 3274, 5166, 4371, 1188, 7383, 1294, 9524]
    vals, bad, t0 = [], [], time.time()
    for N in range(1, NMAX + 1):
        v = len(T6(N))
        vals.append(v)
        flag = ""
        if N <= len(sent) and v != sent[N - 1]:
            bad.append((N, v, sent[N - 1]))
            flag = f"   <-- SENT VALUE WAS {sent[N-1]}"
        print(f"  N={N:3d}  T(N,6)={v:7d}   [{time.time()-t0:7.1f}s]{flag}", flush=True)
    print()
    print("T(N,6), proved-complete, N=1..%d:" % NMAX)
    print(", ".join(map(str, vals)))
    print()
    print("search bound : p*q <= 2N^2(N+1) (PROVED); e | pq (PROVED); r solved (PROVED)")
    print("vs sequence sent to Ian Short :", "AGREES" if not bad else f"DISAGREES {bad}")
