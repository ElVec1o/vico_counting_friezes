#!/usr/bin/env python3
"""Measure the largest quiddity numerator at widths 4, 5, 6, 7.

Purpose: test the conjecture  max_i (N*a_i) = (n-4)*N^3 + 2*N^2.
"""
import sys
sys.path.insert(0, ".")
from fractions import Fraction as F
from verify_width5_proved import T5, spf_sieve, factor
from verify_width6_proved import T6
from explore_width7 import width7

def w4_max(N):
    return max(p for p in range(1, 2*N*N+1) if (2*N*N) % p == 0)

def w5_max(N, spf):
    S = T5(N, spf, factor(N*N, spf) if N > 1 else {})
    best = 0
    NN = N*N
    for (p, q) in S:
        e = p*q - NN
        # quiddity numerators: p, q, N^2(p+N)/e, e/N*N = e... in units of 1/N
        a2 = N*N*(p+N)//e
        a3 = e//N
        a4 = N*N*(q+N)//e
        best = max(best, p, q, a2, a3, a4)
    return best

def w6_max(N):
    S = T6(N)
    best = 0
    NN = N*N
    for (p, q, r) in S:
        e = (p*q*r - NN*(p+r))//NN
        nums = [p, q, r, p*q//e, e, q*r//e]
        best = max(best, max(nums))
    return best

def w7_max(N):
    S = width7(N, 12*N*N + 12)
    return max(max(t[4]) for t in S)

if __name__ == "__main__":
    spf = spf_sieve(6**3 + 2*36 + 20)
    print("  n   N   max numerator   (n-4)N^3+2N^2   match")
    for N in (1,2,3,4,5):
        v, pred = w4_max(N), 0*N**3 + 2*N*N
        print(f"  4 {N:3d} {v:15d} {pred:15d}   {v==pred}")
    for N in (1,2,3,4,5):
        v, pred = w5_max(N, spf), 1*N**3 + 2*N*N
        print(f"  5 {N:3d} {v:15d} {pred:15d}   {v==pred}")
    for N in (1,2,3,4):
        v, pred = w6_max(N), 2*N**3 + 2*N*N
        print(f"  6 {N:3d} {v:15d} {pred:15d}   {v==pred}")
    for N in (1,2,3):
        v, pred = w7_max(N), 3*N**3 + 2*N*N
        print(f"  7 {N:3d} {v:15d} {pred:15d}   {v==pred}")
