"""Regenerates the numerical claims in the paper that have no script of their own.

    python3 paper_numbers.py [block]

Blocks: artin_schreier, drift, overshoot, single_M.  With no argument all four run.
Each prints the recomputed value beside the value stated in the paper.
"""
import sys
import math
from math import gcd, isqrt


def divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i * i != n:
                ds.append(n // i)
        i += 1
    return ds


def d(n):
    return len(divisors(n))


def artin_schreier():
    """Section 10. P = t^q - t - 1 is irreducible and P+1 splits completely, so
    C(P) >= (q-1)2^q. Against the typical size q(q-1)n^2/2 at n = q."""
    print("== Artin-Schreier violation of the n^2 form ==")
    for q in (11, 19):
        low = (q - 1) * 2 ** q
        model = q * (q - 1) // 2 * q * q
        print(f"  q = n = {q:>2}: ratio {low/model:.2f}")
    print("  paper: 3.08 at q=11, 152.9 at q=19")


def drift():
    """Section 9. Proposition prop:twofam forces d(2p+1) << d(p+1) + log^2 p;
    the maximum of that ratio over four windows of p."""
    print("== drift of d(2p+1)/(d(p+1)+log^2 p) ==")
    L = 400000
    sieve = bytearray([1]) * (L + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(L ** .5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    out = []
    for lo, hi in [(10**3, 10**4), (10**4, 5*10**4),
                   (5*10**4, 15*10**4), (15*10**4, 4*10**5)]:
        best = 0.0
        for p in range(lo, hi):
            if sieve[p]:
                best = max(best, d(2*p+1) / (d(p+1) + math.log(p) ** 2))
        out.append(best)
    print("  " + ", ".join(f"{x:.3f}" for x in out))
    print("  paper: 0.394, 0.413, 0.449, 0.565")


def overshoot(Nmax=25):
    """Section 9. Proposition prop:residue counts divisors in residue classes.
    Dropping the gcd condition overshoots T(N,5) by this factor."""
    sys.path.insert(0, '.')
    from verify_width5_proved import spf_sieve, factor, T5 as _T5
    print("== overshoot from dropping the gcd condition ==")
    lim = Nmax ** 3 + 2 * Nmax ** 2 + Nmax + 10
    spf = spf_sieve(lim)
    ratios = []
    for N in range(2, Nmax + 1):
        T = len(_T5(N, spf, factor(N * N, spf)))
        loose = 0
        for M in divisors(N * N):
            for g in range(1, N * N + 2 * N + 1):
                loose += sum(1 for D in divisors(N * N + g * M) if (D + N) % g == 0)
        ratios.append(loose / T)
    print(f"  range over 2 <= N <= {Nmax}: {min(ratios):.2f} to {max(ratios):.2f}")
    print("  paper: 1.95 to 7.33")


def largest_g(Nmax=25):
    """Section 9. The bound g <= N^2+2N of prop:residue is attained, and is exactly the
    largest g occurring, for every 6 <= N <= Nmax."""
    print("== largest g occurring ==")
    from math import gcd
    ok = True
    for N in range(6, Nmax + 1):
        gmax = 0
        for M in divisors(N * N):
            for u in range(1, 3 * N + 3):
                for v in range(1, 3 * N + 3):
                    t = N * (u + v) + M
                    if t % (u * v) == 0 and gcd(u, v) == 1:
                        gmax = max(gmax, t // (u * v))
        if gmax != N * N + 2 * N:
            ok = False
            print(f"  N = {N}: largest g is {gmax}, not {N*N+2*N}")
    print(f"  g = N^2+2N is the largest g for every 6 <= N <= {Nmax}: {ok}")
    print("  paper: attained, and exactly the largest, on that range")


def single_M(N=420):
    """Section 9. The per-M counts are not of size N^{o(1)}: the largest single-M
    contribution at N = 420. Pairs are ordered; the condition is symmetric in u,v,
    and prop:hyp gives min(u,v) < N + sqrt(N^2+M), which bounds the loop."""
    print("== largest single-M contribution ==")
    best = (0, 0)
    for M in divisors(N * N):
        S = set()
        for u in range(1, N + isqrt(N * N + M) + 2):
            for v in divisors(N * u + M):
                if gcd(u, v) == 1 and (N * (u + v) + M) % (u * v) == 0:
                    S.add((u, v)); S.add((v, u))
        if len(S) > best[0]:
            best = (len(S), M)
    print(f"  N = {N}: {best[0]} ordered pairs at M = {best[1]}")
    print("  paper: 765")


BLOCKS = {"artin_schreier": artin_schreier, "drift": drift,
          "overshoot": overshoot, "single_M": single_M, "largest_g": largest_g}

if __name__ == "__main__":
    which = sys.argv[1:] or list(BLOCKS)
    for name in which:
        BLOCKS[name]()
        print()
