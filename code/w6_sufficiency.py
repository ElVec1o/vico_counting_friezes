#!/usr/bin/env python3
"""Width-6 sufficiency: is the quiddity condition plus row 3 the whole story?

A width-6 frieze has interior rows 2, 3, 4. The glide symmetry exchanges rows 2 and 4
and fixes row 3, so beyond the quiddity there is exactly one more row to control. Its
entries are a_j a_{j+1} - 1 = (p_j p_{j+1} - N^2)/N^2, which lie in (1/N)Z iff
N | p_j p_{j+1}, and are positive iff p_j p_{j+1} > N^2.

The frieze relations force p_0p_1 = p_3p_4, p_1p_2 = p_4p_5 and p_2p_3 = p_5p_0, so
row 3 contributes three conditions, not six.

CLAIM. (p_0,p_1,p_2) in Z^3_{>0} is the leading segment of the quiddity cycle of a
positive width-6 frieze over (1/N)Z if and only if, with
e := (p_0p_1p_2 - N^2(p_0+p_2))/N^2 and p_3 := p_0p_1/e,

  (a) N^2 | p_0p_1p_2 - N^2(p_0+p_2)  and  e > 0        [a_4 = e/N in (1/N)Z]
  (b) e | p_0p_1  and  e | p_1p_2                       [a_3, a_5 in (1/N)Z]
  (c) N | p_0p_1,  N | p_1p_2,  N | p_2p_3              [row 3 in (1/N)Z]
  (d) p_0p_1 > N^2,  p_1p_2 > N^2,  p_2p_3 > N^2        [row 3 positive]

Conditions (a)-(d) are necessary and sufficient (Theorem thm:w6count): rows 2, 3 and 4
are the only interior rows, row 4 is row 2 permuted, and row 3 contributes exactly (c)
and (d). This script is independent confirmation, not the proof: it enumerates every
triple satisfying (a)-(d) inside the Cuntz-Holm box p_j <= 2N^3 + 2N^2 (Theorem
thm:uniform at n = 6) and compares with the triples that pass a full expansion of the
seven-row array. It also reports any candidate whose p_2 escapes the box, which would
be a spurious solution.
"""
from fractions import Fraction as F
import sys
sys.path.insert(0, ".")
from verify_width6_proved import full_check, divisors


def by_conditions(N):
    """All (p_0,p_1,p_2) satisfying (a)-(d), enumerated via e | p_0p_1 and p_2 solved."""
    NN = N * N
    bound = 2 * N ** 3 + 2 * NN
    out, escaped = set(), []
    for p0 in range(1, bound + 1):
        for p1 in range(1, bound + 1):
            if p0 * p1 <= NN:                    # (d) for row-3 entry p_0p_1
                continue
            if (p0 * p1) % N:                    # (c)
                continue
            u = p0 * p1 - NN                     # p_2 * u = N^2 (e + p_0)
            for e in divisors(p0 * p1):          # (b), first half
                num = NN * (e + p0)
                if num % u:
                    continue
                p2 = num // u                    # p_2 determined by (p_0,p_1,e)
                if p2 <= 0 or (p1 * p2) % e or (p1 * p2) % N:
                    continue                     # (b) second half, (c)
                if p1 * p2 <= NN:
                    continue                     # (d)
                if (p0 * p1) % e:
                    continue
                p3 = p0 * p1 // e
                if (p2 * p3) % N or p2 * p3 <= NN:
                    continue                     # (c), (d)
                if max(p0, p1, p2) > bound:
                    escaped.append((p0, p1, p2))
                    continue
                out.add((p0, p1, p2))
    return out, escaped


def by_full_check(N, cands):
    """Which of the candidate triples really give a positive width-6 frieze over (1/N)Z."""
    NN = N * N
    ok = set()
    for (p0, p1, p2) in cands:
        e = (p0 * p1 * p2 - NN * (p0 + p2))
        if e <= 0 or e % NN:
            continue
        e //= NN
        quid = [F(p0, N), F(p1, N), F(p2, N), F(p0 * p1, e * N), F(e, N), F(p1 * p2, e * N)]
        if full_check(quid, N, 6):
            ok.add((p0, p1, p2))
    return ok


def truth(N):
    """All true (p_0,p_1,p_2) by brute force over the Cuntz-Holm box, e | p_0p_1."""
    NN, bound = N * N, 2 * N ** 3 + 2 * N * N
    ok = set()
    for p0 in range(1, bound + 1):
        for p1 in range(1, bound + 1):
            u = p0 * p1 - NN
            if u <= 0:
                continue
            for e in divisors(p0 * p1):
                num = NN * (e + p0)
                if num % u:
                    continue
                p2 = num // u
                if p2 <= 0 or p2 > bound:
                    continue
                quid = [F(p0, N), F(p1, N), F(p2, N), F(p0 * p1, e * N), F(e, N),
                        F(p1 * p2, e * N)]
                if full_check(quid, N, 6):
                    ok.add((p0, p1, p2))
    return ok


if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    print("  N   by (a)-(d)   true friezes   equal   escaped box")
    allok = True
    for N in range(1, hi + 1):
        cond, escaped = by_conditions(N)
        true = truth(N)
        eq = (cond == true)
        allok &= eq and not escaped
        print(f"  {N}  {len(cond):10d} {len(true):14d}   {str(eq):5s}   {len(escaped)}")
        if not eq:
            print("    only in (a)-(d):", sorted(cond - true)[:6])
            print("    only true      :", sorted(true - cond)[:6])
    print()
    print("conditions (a)-(d) characterise width-6 friezes:", allok)
