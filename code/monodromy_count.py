#!/usr/bin/env python3
"""T(N,n) as a count of integral matrix factorisations.

With W(N,p) = [[p,-N],[N,0]] = N*M(p/N), the frieze condition M(a_0)...M(a_{n-1}) = -1
on a quiddity a_i = p_i/N is the integral identity W(p_0)...W(p_{n-1}) = -N^n I.
This checks that count against the tabulated T(N,n).
"""

def matmul(A, B):
    return ((A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]),
            (A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]))

def W(N, p):
    return ((p, -N), (N, 0))

def count(N, n, cap):
    target = ((-N ** n, 0), (0, -N ** n))
    total = 0
    def rec(i, A):
        nonlocal total
        if i == n:
            if A == target:
                total += 1
            return
        for p in range(1, cap + 1):
            rec(i + 1, matmul(A, W(N, p)))
    rec(0, ((1, 0), (0, 1)))
    return total

# search bounds: 2N^2 at width 4 (thm:w4), N^3+2N^2 at width 5 (lem:w5bound)
CASES = {(1, 4): 2, (2, 4): 4, (3, 4): 6, (4, 4): 6,
         (1, 5): 5, (2, 5): 20, (3, 5): 40, (1, 6): 14}

def main():
    print("  N  n    cap   factorisations   T(N,n)")
    bad = []
    for (N, n), t in sorted(CASES.items()):
        cap = 2 * N * N + 2 if n == 4 else (N ** 3 + 2 * N * N + 2 if n == 5 else 14)
        c = count(N, n, cap)
        if c != t:
            bad.append((N, n, c, t))
        print(f" {N:2d} {n:2d} {cap:6d} {c:16d} {t:8d}")
    print("\nmismatches:", bad if bad else "none")

if __name__ == "__main__":
    main()
