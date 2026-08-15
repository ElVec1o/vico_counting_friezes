"""The rational fan F(n,N): are all entries outside columns 0 and 1 positive integers?

The quiddity of the fan is (a, 1/N, N+1, 2, ..., 2, N+1, 1/N) with a = N^2(m+1) + 2N and
m = n - 5. Columns 1 and 0 have proved closed forms (fan_col_one, fan_col_zero). This
script checks the remaining entries, which the paper labels HEURISTIC.
"""
from fractions import Fraction as F

def fan_quiddity(n, N):
    m = n - 5
    return [F(N * N * (m + 1) + 2 * N), F(1, N), F(N + 1)] + [F(2)] * m + [F(N + 1), F(1, N)]

def build(quid, n):
    rows = {0: [F(0)] * n, 1: [F(1)] * n}
    for r in range(2, n + 1):
        row = []
        for j in range(n):
            if r == 2:
                row.append(quid[j % n])
            else:
                den = rows[r - 2][(j + 1) % n]
                if den == 0:
                    return None
                row.append((rows[r - 1][j % n] * rows[r - 1][(j + 1) % n] - 1) / den)
        rows[r] = row
    return rows

def run(nmax=12, Nmax=8):
    checked = bad = 0
    for n in range(5, nmax + 1):
        for N in range(1, Nmax + 1):
            q = fan_quiddity(n, N)
            if len(q) != n:
                continue
            rows = build(q, n)
            if rows is None:
                continue
            for r in range(2, n - 1):
                for j in range(n):
                    e = rows[r][j]; checked += 1
                    if e <= 0 or (e != F(1, N) and e.denominator != 1):
                        bad += 1
    print(f"fans 5 <= n <= {nmax}, 1 <= N <= {Nmax}")
    print(f"entries checked: {checked}")
    print(f"entries neither 1/N nor a positive integer: {bad}")

if __name__ == "__main__":
    run()
