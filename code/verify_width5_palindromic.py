#!/usr/bin/env python3
"""Verification of the width-4 and palindromic width-5 closed forms.

Both statements are PROVED in the paper; this script attacks them numerically
over an explicitly stated range and reports the ground covered exactly.
"""
from fractions import Fraction as F


def frieze_rows(quid):
    """Full frieze array from a quiddity cycle, or None if it is not a frieze.

    Convention (Karpenkov-Short-van Son-Zabolotskii, section 6): width n means
    rows 0..n, row 0 zeros, row 1 ones, row 2 the quiddity, row n-1 ones,
    row n zeros, and the diamond rule throughout.
    """
    n = len(quid)
    rows = [[F(0)] * n, [F(1)] * n, [F(q) for q in quid]]
    for r in range(3, n + 1):
        prev, prev2 = rows[r - 1], rows[r - 2]
        cur = []
        for j in range(n):
            d = prev2[(j + 1) % n]
            if d == 0:
                return None
            cur.append((prev[j] * prev[(j + 1) % n] - 1) / d)
        rows.append(cur)
    if any(x != 1 for x in rows[n - 1]):
        return None
    if any(x != 0 for x in rows[n]):
        return None
    if any(x <= 0 for r in rows[2:n - 1] for x in r):
        return None
    return rows


def in_lattice(x, N):
    """x lies in (1/N)Z."""
    return (x * N).denominator == 1


# ------------------------------------------------------------------ width 4
def check_width4(NMAX):
    """THEOREM. T(N,4) = d(2N^2), via the bijection p <-> (p/N, 2N/p, p/N, 2N/p)
    between positive divisors p of 2N^2 and width-4 friezes over (1/N)Z."""
    def d(n):
        c, m, p = 1, n, 2
        while p * p <= m:
            e = 0
            while m % p == 0:
                e += 1
                m //= p
            c *= e + 1
            p += 1
        return c * (2 if m > 1 else 1)

    bad = []
    for N in range(1, NMAX + 1):
        divisors = [p for p in range(1, 2 * N * N + 1) if (2 * N * N) % p == 0]
        built = 0
        for p in divisors:
            a, b = F(p, N), F(2 * N, p)
            if not (in_lattice(a, N) and in_lattice(b, N)):
                bad.append(("lattice", N, p))
                continue
            if frieze_rows([a, b, a, b]) is None:
                bad.append(("not a frieze", N, p))
                continue
            built += 1
        if built != d(2 * N * N):
            bad.append(("count", N, built, d(2 * N * N)))
    print("T(N,4) = d(2N^2)")
    print(f"    ground covered : N = 1..{NMAX}; every divisor of 2N^2 built and checked")
    print(f"    counterexamples: {bad if bad else 'none'}")
    return not bad


# ------------------------------------------------------------------ width 5
def check_width5_family(TS):
    """THEOREM. The width-5 quiddities fixed by the reflection through index 0
    are exactly (t(t+2), 1/t, t+1, t+1, 1/t) for rational t > 0."""
    bad = []
    for t in TS:
        quid = [t * (t + 2), 1 / t, t + 1, t + 1, 1 / t]
        if frieze_rows(quid) is None:
            bad.append(t)
    print("family (t(t+2), 1/t, t+1, t+1, 1/t) is a positive width-5 frieze")
    print(f"    ground covered : {len(TS)} rational values of t")
    print(f"    counterexamples: {bad if bad else 'none'}")
    return not bad


def check_width5_count(NMAX):
    """THEOREM. #{palindromic width-5 friezes over (1/N)Z fixed by r_0}
             = #{k >= 1 : k^2 | N^3} = A092520(N),
    via t = N/k."""
    def A092520(N):
        r, m, p = 1, N, 2
        while p * p <= m:
            e = 0
            while m % p == 0:
                e += 1
                m //= p
            r *= (3 * e) // 2 + 1
            p += 1
        if m > 1:
            r *= 2
        return r

    bad = []
    for N in range(1, NMAX + 1):
        # every k with k^2 | N^3 must give a frieze in the lattice, and
        # conversely every lattice member of the family must arise this way
        ks = [k for k in range(1, N * N + 1) if (N ** 3) % (k * k) == 0]
        good = 0
        for k in ks:
            t = F(N, k)
            quid = [t * (t + 2), 1 / t, t + 1, t + 1, 1 / t]
            if frieze_rows(quid) is None:
                bad.append(("not a frieze", N, k))
                continue
            if not all(in_lattice(x, N) for x in quid):
                bad.append(("not in lattice", N, k))
                continue
            good += 1
        # converse sweep: any t = N/k' with k' outside the divisor condition must fail
        for kp in range(1, N * N + 1):
            if (N ** 3) % (kp * kp) == 0:
                continue
            t = F(N, kp)
            quid = [t * (t + 2), 1 / t, t + 1, t + 1, 1 / t]
            if all(in_lattice(x, N) for x in quid):
                bad.append(("false positive", N, kp))
        if good != A092520(N):
            bad.append(("count", N, good, A092520(N)))
    print("palindromic width-5 count = #{k : k^2 | N^3} = A092520(N)")
    print(f"    ground covered : N = 1..{NMAX}, both directions (k^2|N^3 and its complement)")
    print(f"    counterexamples: {bad if bad else 'none'}")
    return not bad


if __name__ == "__main__":
    ok = []
    ok.append(check_width4(30))
    ok.append(check_width5_family([F(a, b) for a in range(1, 13) for b in range(1, 13)]))
    ok.append(check_width5_count(40))
    print()
    print("ALL PASS" if all(ok) else "FAILURES PRESENT")
    raise SystemExit(0 if all(ok) else 1)
