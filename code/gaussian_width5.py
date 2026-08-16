#!/usr/bin/env python3
"""Width-five friezes over the Gaussian integers (VicoEnum/Width5AnyRing.lean).

The reduction to W5 uses no order.  Over (1/N)Z[i] the same divisibility system
describes the friezes, with the two nondegeneracy conditions p != -N, q != -N
that positivity hides over R.  The counts stabilise as the search box grows,
so the solution set is finite.
"""
from fractions import Fraction as F
def mul(z,w): return (z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0])
def sub(z,w): return (z[0]-w[0], z[1]-w[1])
def norm(z): return z[0]*z[0]+z[1]*z[1]
def dvd(z,w):
    n=norm(z)
    if n==0: return False
    return (w[0]*z[0]+w[1]*z[1])%n==0 and (w[1]*z[0]-w[0]*z[1])%n==0
def qmul(z,w): return (z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0])
def qdiv(z,w):
    d=w[0]*w[0]+w[1]*w[1]
    return ((z[0]*w[0]+z[1]*w[1])/d, (z[1]*w[0]-z[0]*w[1])/d)
def qz(z): return z[0]==0 and z[1]==0
def inlat(z,N): return (z[0]*N).denominator==1 and (z[1]*N).denominator==1
ONE=(F(1),F(0))
def quiddity5(N,p,q):
    a=[(F(p[0],N),F(p[1],N)),(F(q[0],N),F(q[1],N))]
    for _ in range(3):
        x,y=a[-2],a[-1]
        d=(qmul(x,y)[0]-1, qmul(x,y)[1])
        if qz(d): return None
        a.append(qdiv((x[0]+1,x[1]),d))
    x,y=a[3],a[4]
    d=(qmul(x,y)[0]-1, qmul(x,y)[1])
    if qz(d) or qdiv((x[0]+1,x[1]),d)!=a[0]: return None
    if any(qz(t) or not inlat(t,N) for t in a): return None
    for j in range(5):
        m=qmul(a[j],a[(j+1)%5]); e=(m[0]-1,m[1])
        if qz(e) or not inlat(e,N): return None
    return tuple(a)
def W5(N,p,q):
    NN=(N*N,0); pq=mul(p,q); D=sub(pq,NN)
    if D==(0,0) or not dvd((N,0),pq): return False
    if not dvd(D, mul(NN,(p[0]+N,p[1]))): return False
    if not dvd(D, mul(NN,(q[0]+N,q[1]))): return False
    return True
import sys
for N in (1,2,3):
    row=[]
    for C in (4,9,16,25,36):
        L=int((C*N**4)**0.5)+1
        pts=[(a,b) for a in range(-L,L+1) for b in range(-L,L+1)
             if (a,b)!=(0,0) and norm((a,b))<=C*N**4]
        S=set()
        for p in pts:
            for q in pts:
                if W5(N,p,q):
                    r=quiddity5(N,p,q)
                    if r: S.add(r)
        row.append(len(S))
    print(f"N={N}: boxes C=4,9,16,25,36 -> {row}", flush=True)
