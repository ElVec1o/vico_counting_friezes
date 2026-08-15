#!/usr/bin/env python3
"""Falsification test for the glide criterion at every width.

CLAIM (frozen before any data is generated).

Let n >= 4, N >= 1, and let (a_0,...,a_{n-1}) be a quiddity cycle whose monodromy is -I,
written a_j = p_j/N.  Let C_k be the homogenised frieze continuant

    C_0 = 1,  C_1(p_j) = p_j,  C_k(p_j..p_{j+k-1}) = p_{j+k-1} C_{k-1} - N^2 C_{k-2},

so that row r of the frieze has entries K_{r-1}(a_j,..) = C_{r-1}(p_j,..)/N^{r-1}.
Then the frieze is positive with all entries in (1/N)Z if and only if, for every r with
2 <= r <= floor(n/2) and every j mod n,

    N^{r-2} | C_{r-1}(p_j,...,p_{j+r-2})      and      C_{r-1}(p_j,...,p_{j+r-2}) > 0.

Rows above floor(n/2) are glide images of rows below and impose nothing further: the
glide reflection is m_{r,j} = m_{n-r,j+r}.

The claim specialises to Remark rem:glide at n = 5 (only r = 2, which is the quiddity
itself, so no extra condition) and to Theorem thm:w6count at n = 6 (r = 2 and r = 3,
with N | p_j p_{j+1}).

TEST.  Sweep tuples (p_0,...,p_{n-4}), build the quiddity by the parameterisation, and
compare
   (A) full expansion of the (n+1)-row array, every entry checked, against
   (B) the criterion above.
Any disagreement falsifies the claim.
"""
from fractions import Fraction as F
import sys


def cont(xs):
    """Frieze continuant K_k over the rationals."""
    pm2, pm1 = F(0), F(1)
    for x in xs:
        pm2, pm1 = pm1, x * pm1 - pm2
    return pm1


def Cint(ps, N):
    """Homogenised continuant C_k."""
    cm2, cm1 = 0, 1
    for p in ps:
        cm2, cm1 = cm1, p * cm1 - N * N * cm2
    return cm1


def quiddity(ps, N, n):
    """Parameterisation of Proposition 2.1 from p_0..p_{n-4}; None if degenerate."""
    a = [F(p, N) for p in ps]
    D = cont(a)
    if D == 0:
        return None
    return a + [(cont(a[:-1]) + 1) / D, D, (cont(a[1:]) + 1) / D]


def full_ok(quid, N, n):
    """Expand the whole array and check every entry: positive and in (1/N)Z."""
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


def criterion_ok(quid, N, n):
    """Rows 2..floor(n/2) only, via the homogenised continuant."""
    p = [x * N for x in quid]
    if any(t.denominator != 1 for t in p):
        return False
    p = [int(t) for t in p]
    if any(t <= 0 for t in p):
        return False
    for r in range(2, n // 2 + 1):
        for j in range(n):
            w = [p[(j + i) % n] for i in range(r - 1)]
            c = Cint(w, N)
            if c <= 0 or c % (N ** (r - 2)):
                return False
    return True


def criterion_rows(quid, N, n, lo, hi):
    """The criterion restricted to rows lo..hi, for the sharpness test."""
    p = [x * N for x in quid]
    if any(t.denominator != 1 for t in p):
        return False
    p = [int(t) for t in p]
    if any(t <= 0 for t in p):
        return False
    for r in range(lo, hi + 1):
        for j in range(n):
            w = [p[(j + i) % n] for i in range(r - 1)]
            c = Cint(w, N)
            if c <= 0 or c % (N ** (r - 2)):
                return False
    return True


def sharpness(B=8, cases=((7, 2), (8, 2), (9, 2))):
    """Is floor(n/2) sharp?  Truncating to floor(n/2)-1 should OVERCOUNT; extending to
    floor(n/2)+1 should change nothing.  All three cases are run in the SAME box B."""
    print(f"  sharpness of the floor(n/2) cutoff, common box B = {B}")
    print("    n   N     full   r<=floor(n/2)   r<=floor(n/2)-1   r<=floor(n/2)+1")
    for n, N in cases:
        k = n - 3
        tot = [0, 0, 0, 0]
        idx = [1] * k
        while True:
            q = quiddity(idx, N, n)
            if q is not None:
                h = n // 2
                tot[0] += full_ok(q, N, n)
                tot[1] += criterion_rows(q, N, n, 2, h)
                tot[2] += criterion_rows(q, N, n, 2, h - 1)
                tot[3] += criterion_rows(q, N, n, 2, h + 1)
            i = k - 1
            while i >= 0:
                idx[i] += 1
                if idx[i] <= B:
                    break
                idx[i] = 1
                i -= 1
            if i < 0:
                break
        print(f"    {n}   {N}  {tot[0]:7d}  {tot[1]:13d}  {tot[2]:16d}  {tot[3]:16d}")


if __name__ == "__main__":
    print("   n   N   box    sweep  friezes  criterion  disagr   box status")
    bad_total = 0
    for n in (5, 6, 7, 8, 9):
        for N in (1, 2, 3):
            # Cuntz-Holm (Theorem thm:uniform): every entry is at most (n-4)N^2+2N,
            # so p_j <= (n-4)N^3 + 2N^2. At N = 1 this box is complete and the counts
            # must be the Catalan numbers C_{n-2}. For N >= 2 it is truncated to keep
            # the sweep finite, so those rows are consistency counts, not enumerations.
            k = n - 3
            CH = (n - 4) * N ** 3 + 2 * N * N
            B = CH
            if B ** k > 600000:
                B = max(2, int(600000 ** (1.0 / k)))
            tot = nA = nB = bad = 0
            idx = [1] * k
            while True:
                q = quiddity(idx, N, n)
                tot += 1
                if q is not None:
                    A, Bc = full_ok(q, N, n), criterion_ok(q, N, n)
                    nA += A; nB += Bc
                    if A != Bc:
                        bad += 1
                        if bad <= 2:
                            print("    DISAGREE", n, N, idx, "full:", A, "crit:", Bc)
                # odometer
                i = k - 1
                while i >= 0:
                    idx[i] += 1
                    if idx[i] <= B:
                        break
                    idx[i] = 1
                    i -= 1
                if i < 0:
                    break
            bad_total += bad
            comp = "complete" if B >= CH else f"truncated (CH={CH})"
            print(f"   {n}  {N}  {B:3d} {tot:8d} {nA:9d} {nB:10d} {bad:6d}   {comp}")
    print()
    print("glide criterion agrees with the full array everywhere:", bad_total == 0)
    print()
    sharpness()
