#!/usr/bin/env python3
"""T(N,5) by a PROVED-complete enumeration. No saturation heuristic anywhere.

A positive rational frieze of width 5 is determined by a_0, a_1 via the frieze
continuants:  a_2 = (a_0+1)/D,  a_3 = D,  a_4 = (a_1+1)/D,  D = a_0 a_1 - 1.
With a_0 = p/N, a_1 = q/N and e = pq - N^2, membership in (1/N)Z is exactly

    e > 0,   N | e,   e | N^2(p+N),   e | N^2(q+N).                          (C)

LEMMA (search bound, proved).  e | N^2(q+N) and e > 0 give e <= N^2(q+N); with
e = pq - N^2 this is q(p - N^2) <= N^3 + N^2, and q >= 1 forces p <= N^3 + 2N^2.
By symmetry q <= N^3 + 2N^2.  Since also e | N^2(p+N) and q = (e + N^2)/p, the
sweep below visits every solution exactly once.
"""
import sys
import time


def spf_sieve(n):
    s = list(range(n + 1))
    i = 2
    while i * i <= n:
        if s[i] == i:
            for j in range(i * i, n + 1, i):
                if s[j] == j:
                    s[j] = i
        i += 1
    return s


def factor(n, spf):
    f = {}
    while n > 1:
        p = spf[n]
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    return f


def divisors_from(f):
    ds = [1]
    for p, e in f.items():
        ds = [d * p ** i for d in ds for i in range(e + 1)]
    return ds


def T5(N, spf, fN2):
    NN = N * N
    P = N ** 3 + 2 * NN
    sols = set()
    for p in range(1, P + 1):
        f = dict(fN2)
        for q_, e_ in factor(p + N, spf).items():
            f[q_] = f.get(q_, 0) + e_
        for e in divisors_from(f):
            if e % N or (e + NN) % p:
                continue
            q = (e + NN) // p
            if q <= 0 or q > P or p * q - NN != e:
                continue
            if (NN * (q + N)) % e:
                continue
            sols.add((p, q))
    return sols


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    sent = [5, 20, 40, 60, 60, 110, 70, 145, 140, 170, 90, 310,
            80, 210, 320, 255, 100, 380, 110, 480, 370, 230, 130, 680,
            230, 260, 365, 540, 130, 810, 120, 480, 430, 300, 600, 970,
            100, 290, 510, 1000]
    LIM = NMAX ** 3 + 2 * NMAX ** 2 + NMAX + 10
    print(f"sieving smallest prime factors up to {LIM} ...", flush=True)
    spf = spf_sieve(LIM)
    vals, bad = [], []
    t0 = time.time()
    for N in range(1, NMAX + 1):
        fN2 = factor(N * N, spf) if N > 1 else {}
        v = len(T5(N, spf, fN2))
        vals.append(v)
        flag = ""
        if N <= len(sent):
            if v != sent[N - 1]:
                bad.append((N, v, sent[N - 1]))
                flag = f"  <-- SENT VALUE WAS {sent[N-1]}"
        print(f"  N={N:3d}  T(N,5)={v:6d}   [{time.time()-t0:6.1f}s]{flag}", flush=True)
    print()
    print("T(N,5), proved-complete, N=1..%d:" % NMAX)
    print(", ".join(map(str, vals)))
    print()
    print("search bound : p,q <= N^3+2N^2 (PROVED);  e | N^2(p+N) (PROVED)")
    print("vs sequence sent to Ian Short :", "AGREES" if not bad else f"DISAGREES {bad}")
