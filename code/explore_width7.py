#!/usr/bin/env python3
"""Width-7 exploration: verify the derived relations and test candidate bounds.

Nothing here is claimed as proved. This measures what is true on an explicitly
bounded box so that a bound can be conjectured honestly and proved afterwards.
"""
from fractions import Fraction as F
import sys

def frieze(quid, n, N):
    rows = [[F(0)]*n, [F(1)]*n, list(quid)]
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

def divisors(n):
    ds, i = [], 1
    while i*i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n//i: ds.append(n//i)
        i += 1
    return ds

def width7(N, P):
    """All width-7 friezes over (1/N)Z with p_0,p_1,p_2 <= P.

    p_3 is not swept: e*N divides G+N^3, so e runs over the divisors of
    (G+N^3)/N, and p_3 = (e*N^3 + N^2*u)/G is then determined.
    """
    out = []
    NN = N*N
    for p0 in range(1, P+1):
        for p1 in range(1, P+1):
            u = p0*p1 - NN
            if u <= 0: continue
            for p2 in range(1, P+1):
                G = p2*u - p0*NN
                if G <= 0 or (p1*p2 - NN) <= 0: continue
                if (G + N**3) % N: continue
                for e in divisors((G + N**3)//N):
                    num = e*N**3 + NN*u
                    if num % G: continue
                    p3 = num // G
                    if p3 < 1: continue
                    E = p3*G - NN*u
                    if E <= 0 or E % (N**3) or E//(N**3) != e: continue
                    H = p3*(p1*p2 - NN) - p1*NN
                    if H <= 0 or (H + N**3) % (e*N): continue
                    a = [F(p0,N), F(p1,N), F(p2,N), F(p3,N),
                         F(G + N**3, e*NN), F(e,N), F(H + N**3, e*NN)]
                    if frieze(a, 7, N) is not None:
                        out.append((p0,p1,p2,p3,tuple(int(x*N) for x in a)))
    return out

if __name__ == "__main__":
    print(" N   P   #friezes   max numerator   N^3+2N^2   N^2(N^3+1)   bound p3<=N^2(N^3+u-N^2+1) holds")
    for N in (1,2,3):
        for P in (12*N*N + 12,):
            S = width7(N, P)
            if not S:
                print(f"{N:2d} {P:4d}      0"); continue
            mx = max(max(t[4]) for t in S)
            saturated = mx < P
            ok = all(t[3] <= N*N*(N**3 + t[0]*t[1] - N*N + 1) for t in S)
            print(f"{N:2d} {P:4d} {len(S):8d} {mx:14d} {N**3+2*N*N:11d} {N*N*(N**3+1):12d}   {ok}"
                  f"   (max param {max(max(t[:4]) for t in S)}, ceiling {'not ' if saturated else ''}touched)")
    # Catalan check at N=1
    print()
    print("N=1 count should be C_5 = 42:", len(width7(1, 60)))
