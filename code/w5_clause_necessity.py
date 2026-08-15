"""Each of the three arithmetic clauses of W5 is necessary.

The predicate W5(N,p,q) of Proposition prop:w5cond is

    p > 0,  q > 0,  N^2 < pq,          (positivity and nondegeneracy)
    N | pq,                            (clause A: makes D = (pq-N^2)/N integral)
    (pq-N^2) | N^2 (p+N),              (clause B: makes a_4 lie in the lattice)
    (pq-N^2) | N^2 (q+N),              (clause C: makes a_2 lie in the lattice)

over the box p, q <= N^3 + 2N^2 of Theorem thm:box. This script recomputes T(N,5)
with each of A, B, C removed in turn. Every one of the three changes the count at
every N >= 2, so none is implied by the other two.

Usage: python3 w5_clause_necessity.py [NMAX]     (default NMAX = 8)
"""

import sys


def count(N, drop=None):
    """Number of W5 pairs at N, with clause `drop` in {None,'A','B','C'} removed."""
    bound = N ** 3 + 2 * N ** 2
    N2 = N * N
    total = 0
    for p in range(1, bound + 1):
        for q in range(1, bound + 1):
            e = p * q - N2
            if e <= 0:
                continue
            if drop != 'A' and (p * q) % N != 0:
                continue
            if drop != 'B' and (N2 * (p + N)) % e != 0:
                continue
            if drop != 'C' and (N2 * (q + N)) % e != 0:
                continue
            total += 1
    return total


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    print(f"{'N':>3}  {'T(N,5)':>7}  {'no A':>7}  {'no B':>7}  {'no C':>7}   all differ")
    for N in range(1, nmax + 1):
        full = count(N)
        a, b, c = count(N, 'A'), count(N, 'B'), count(N, 'C')
        differ = (a != full) and (b != full) and (c != full)
        flag = "yes" if differ else "NO"
        print(f"{N:>3}  {full:>7}  {a:>7}  {b:>7}  {c:>7}   {flag}")


if __name__ == "__main__":
    main()
