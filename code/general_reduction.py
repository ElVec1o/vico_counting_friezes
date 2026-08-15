#!/usr/bin/env python3
"""The Markov-type reduction at general width n.

Write a_i = p_i/N and let C_k be the N-homogenised frieze continuant

    C_0 = 1,   C_1(p) = p,   C_k(p_1..p_k) = p_k C_{k-1} - N^2 C_{k-2},

so that K_k(a_i,..) = C_k(p_i,..)/N^k.  Put

    A = C_{n-4}(p_0..p_{n-5}) + N^{n-4},   B = C_{n-4}(p_1..p_{n-4}) + N^{n-4},
    R = C_{n-5}(p_1..p_{n-5}),             g = gcd(A,B),  U = A/g,  V = B/g,
    M = g U V - N^{n-4} (U + V).

Claims tested here, for every positive frieze of width n over (1/N)Z:

  (I1)  gcd(U,V) = 1
  (I2)  g M = A B - N^{n-4}(A+B)                       [ring identity]
  (I3)  g M = N^{n-4} e R                             [Desnanot-Jacobi]
  (C1)  N^{n-4} R | g M   and   e = g M / (N^{n-4} R) [integrality of a_{n-2}]
  (C2)  M | N^2 R                                     [lattice condition on a_{n-3}, a_{n-1}]

(C1) and (C2) together are the reduction.  At n = 5, R = 1 and they read
N | gM and M | N^2: the width-5 theorem.  At n = 6, R = p_1 and they read
N^2 | gM and M | N^2 p_1: the width-6 observation.
"""
from fractions import Fraction as F
from math import gcd
import sys
sys.path.insert(0, ".")
from verify_width5_proved import T5, spf_sieve, factor
from verify_width6_proved import T6
from explore_width7 import width7


def Cint(ps, N):
    """N-homogenised frieze continuant C_k(p_1..p_k)."""
    cm2, cm1 = 0, 1
    for p in ps:
        cm2, cm1 = cm1, p * cm1 - N * N * cm2
    return cm1


def analyse(n, N, a):
    """a is the full quiddity as Fractions; returns the reduction data, or None."""
    p = [x * N for x in a]
    if any(t.denominator != 1 for t in p): return None
    p = [int(t) for t in p]
    E = Cint(p[:n - 3], N)
    if E % N ** (n - 4): return None
    e = E // N ** (n - 4)
    A = Cint(p[:n - 4], N) + N ** (n - 4)
    B = Cint(p[1:n - 3], N) + N ** (n - 4)
    R = Cint(p[1:n - 4], N)
    g = gcd(A, B)
    U, V = A // g, B // g
    M = g * U * V - N ** (n - 4) * (U + V)
    return dict(e=e, A=A, B=B, R=R, g=g, U=U, V=V, M=M, N=N, n=n)


def audit(n, N, quids):
    tot = dict(I1=0, I2=0, I3=0, C1=0, C2=0, all=0)
    for a in quids:
        d = analyse(n, N, a)
        if d is None: continue
        N4 = N ** (n - 4)
        i1 = gcd(d["U"], d["V"]) == 1
        i2 = d["g"] * d["M"] == d["A"] * d["B"] - N4 * (d["A"] + d["B"])
        i3 = d["g"] * d["M"] == N4 * d["e"] * d["R"]
        c1 = (N4 * d["R"] != 0 and d["g"] * d["M"] % (N4 * d["R"]) == 0
              and d["g"] * d["M"] // (N4 * d["R"]) == d["e"])
        c2 = d["M"] != 0 and (N * N * d["R"]) % d["M"] == 0
        for k, v in (("I1", i1), ("I2", i2), ("I3", i3), ("C1", c1), ("C2", c2)):
            tot[k] += v
        tot["all"] += 1
    return tot


def quid5(N, spf):
    out = []
    for (p, q) in T5(N, spf, factor(N * N, spf) if N > 1 else {}):
        e = p * q - N * N
        out.append([F(p, N), F(q, N), F(N * N * (p + N), e * N), F(e, N * N), F(N * N * (q + N), e * N)])
    return out


def quid6(N):
    out = []
    for (p, q, r) in T6(N):
        e = (p * q * r - N * N * (p + r)) // (N * N)
        out.append([F(p, N), F(q, N), F(r, N), F(p * q, e * N), F(e, N), F(q * r, e * N)])
    return out


if __name__ == "__main__":
    spf = spf_sieve(9 ** 3 + 2 * 81 + 20)
    print("  n    N   friezes    I1     I2     I3     C1     C2")
    bad = []
    cases = ([(5, N, quid5(N, spf)) for N in range(1, 9)]
             + [(6, N, quid6(N)) for N in range(1, 7)]
             + [(7, N, [[F(t, N) for t in tup[4]] for tup in width7(N, 12 * N * N + 12)])
                for N in (1, 2, 3)])
    for (n, N, qs) in cases:
        t = audit(n, N, qs)
        print(f"  {n}  {N:3d} {t['all']:9d} " + " ".join(f"{t[k]:6d}" for k in ("I1", "I2", "I3", "C1", "C2")))
        if any(t[k] != t["all"] for k in ("I1", "I2", "I3", "C1", "C2")): bad.append((n, N, t))
    print()
    print("all five claims hold on every frieze tested:", not bad)
    if bad: print("FAILURES:", bad)
