#!/usr/bin/env python3
"""Width-8 enumeration, to test the uniform bound at (n-4) = 4.

Parameterisation: free a_0..a_4, with
  K_2 = u/N^2,  K_3 = G/N^3,  K_4 = E/N^4,  K_5 = F/N^5
  u = p0p1 - N^2,  G = p2*u - p0*N^2,  E = p3*G - N^2*u,  F = p4*E - N^2*G
a_6 = K_5 = F/N^5 lies in (1/N)Z iff N^4 | F, so F = f*N^4.
a_5 = (K_4+1)/K_5 = (E+N^4)/(f*N^3) lies in (1/N)Z iff f*N^2 | E+N^4.
So f runs over the divisors of (E+N^4)/N^2 and p4 = (f*N^4 + N^2*G)/E is solved for.
"""
from fractions import Fraction as F_
import sys, time

def divisors(n):
    ds, i = [], 1
    while i*i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n//i: ds.append(n//i)
        i += 1
    return ds

def frieze(quid, n, N):
    rows = [[F_(0)]*n, [F_(1)]*n, list(quid)]
    for r in range(3, n+1):
        prev, prev2 = rows[r-1], rows[r-2]
        cur = []
        for j in range(n):
            d = prev2[(j+1) % n]
            if d == 0: return None
            cur.append((prev[j]*prev[(j+1) % n] - 1)/d)
        rows.append(cur)
    if any(x != 1 for x in rows[n-1]) or any(x != 0 for x in rows[n]): return None
    for r in range(2, n-1):
        for x in rows[r]:
            if x <= 0 or (x*N).denominator != 1: return None
    return rows

def width8(N, P):
    NN, N4 = N*N, N**4
    out = []
    for p0 in range(1, P+1):
        for p1 in range(1, P+1):
            u = p0*p1 - NN
            if u <= 0: continue
            for p2 in range(1, P+1):
                G = p2*u - p0*NN
                if G <= 0: continue
                for p3 in range(1, P+1):
                    E = p3*G - NN*u
                    if E <= 0: continue
                    if (E + N4) % NN: continue
                    for f in divisors((E + N4)//NN):
                        num = f*N4 + NN*G
                        if num % E: continue
                        p4 = num // E
                        if p4 < 1: continue
                        if p4*E - NN*G != f*N4: continue
                        a = [F_(p0,N), F_(p1,N), F_(p2,N), F_(p3,N), F_(p4,N),
                             F_(E + N4, f*N**3), F_(f, N), None]
                        # a_7 = (K_4(a_1..a_4)+1)/K_5
                        w = p1*p2 - NN
                        if w <= 0: continue
                        G2 = p3*w - p1*NN
                        if G2 <= 0: continue
                        E2 = p4*G2 - NN*w
                        if E2 <= 0: continue
                        a[7] = F_(E2 + N4, f*N**3)
                        if frieze(a, 8, N) is not None:
                            out.append(tuple(int(x*N) for x in a))
    return out

if __name__ == "__main__":
    print("  n   N   #friezes   max numerator   4N^3+2N^2   match   [time]")
    t0 = time.time()
    for N in (1, 2):
        P = 8*N*N + 10
        S = width8(N, P)
        if not S:
            print(f"  8 {N:3d}          0"); continue
        mx = max(max(t) for t in S)
        pred = 4*N**3 + 2*N*N
        print(f"  8 {N:3d} {len(S):10d} {mx:15d} {pred:11d}   {mx==pred}"
              f"   [{time.time()-t0:.0f}s]  (P={P}, ceiling {'not ' if mx<P else ''}touched)", flush=True)
    print()
    print("N=1 should be C_6 = 132")
