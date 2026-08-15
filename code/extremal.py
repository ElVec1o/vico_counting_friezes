#!/usr/bin/env python3
"""Find the friezes attaining the maximum quiddity numerator, at each (n,N)."""
import sys
sys.path.insert(0, ".")
from fractions import Fraction as F
from verify_width5_proved import T5, spf_sieve, factor
from verify_width6_proved import T6
from explore_width7 import width7

def rot_norm(t):
    """Canonical form under rotation, so the big entry is first."""
    n = len(t)
    return max(tuple(t[(i+k) % n] for i in range(n)) for k in range(n))

def show(n, N, cycles):
    mx = max(max(c) for c in cycles)
    ext = sorted({rot_norm(c) for c in cycles if max(c) == mx})
    print(f"  n={n} N={N}: max numerator {mx} = {(n-4)*N**3+2*N*N}, "
          f"{len(ext)} extremal cycle(s) up to rotation")
    for c in ext[:3]:
        print(f"      numerators {c}   entries {[str(F(x,N)) for x in c]}")

spf = spf_sieve(6**3 + 2*36 + 20)
for N in (1,2,3,4):
    S = T5(N, spf, factor(N*N,spf) if N>1 else {})
    cyc = []
    for (p,q) in S:
        e = p*q - N*N
        cyc.append((p, q, N*N*(p+N)//e, e//N, N*N*(q+N)//e))
    show(5, N, cyc)
print()
for N in (1,2,3):
    cyc = []
    for (p,q,r) in T6(N):
        e = (p*q*r - N*N*(p+r))//(N*N)
        cyc.append((p,q,r,p*q//e,e,q*r//e))
    show(6, N, cyc)
print()
for N in (1,2,3):
    show(7, N, [t[4] for t in width7(N, 12*N*N+12)])
