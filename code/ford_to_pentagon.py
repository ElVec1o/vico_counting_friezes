#!/usr/bin/env python3
"""Explicit map: Ford triple (s,t,m) with stm = p+t+m  ->  closed 5-path in F_p.

F_p has vertices the integer pairs (a,b) with gcd(a,b) a factor of p, and a directed
edge (a,b) -> (c,d) when ad - bc = p.

Chain: (s,t,m) -> (u,v) = (ps, st-1) -> g = p(u+v+1)/uv -> W5 pair (gu-p, gv-p)
-> quiddity cycle -> vertices by v_{i+1} = (q_i/p) v_i - v_{i-1}.

The path closes ANTIPODALLY, v_5 = -v_0 and v_6 = -v_1, because the frieze monodromy
is -I and not I.  That is the antipodal identification used to view F_p in the plane;
testing v_5 == v_0 instead reports a genuine pentagon as a failure.

Verified here: every Ford triple yields five vertices with gcd dividing p, all five
edge determinants equal to p, and antipodal closure.  Formalised in
VicoEnum/FareyPentagon.lean (fdet_step, fpath_det, pentagon_closes).
"""
import sys
from math import gcd
from fractions import Fraction as Fr


def ford_triples(p):
    out = []
    for s in range(1, p + 3):
        for t in range(1, p + 3):
            d = s * t - 1
            if d <= 0 or (p + t) % d:
                continue
            m = (p + t) // d
            if s * t * m == p + t + m:
                out.append((s, t, m))
    return out


def rot(N, x):
    P, Q = x
    e = P * Q - N * N
    return (Q, N * N * (P + N) // e)


def quiddity_from_pair(p, P, Q):
    """The five numerators q_0..q_4 of the W5 pair (P,Q)."""
    q, x = [], (P, Q)
    for _ in range(5):
        q.append(x[0])
        x = rot(p, x)
    return q


def pentagon(p, q):
    """v_{i+1} = (q_i/p) v_i - v_{i-1}, started at v_0 = (1,0), v_1 = (0,p)."""
    V = [(1, 0), (0, p)]
    for i in range(1, 7):
        a = Fr(q[i % 5], p)
        nx = a * V[i][0] - V[i - 1][0]
        ny = a * V[i][1] - V[i - 1][1]
        if nx.denominator != 1 or ny.denominator != 1:
            return None, "non-integral vertex"
        V.append((int(nx), int(ny)))
    return V, None


def det(u, w):
    return u[0] * w[1] - u[1] * w[0]


def check(p, V):
    """Every vertex lies in F_p, every edge has determinant p, closure is antipodal."""
    msgs = []
    for (a, b) in V[:5]:
        g = gcd(abs(a), abs(b))
        if g and p % g:
            msgs.append(f"vertex {(a,b)}: gcd {g} does not divide {p}")
    for i in range(4):
        if det(V[i], V[i + 1]) != p:
            msgs.append(f"edge {i}: determinant {det(V[i], V[i+1])} != {p}")
    close = (-V[0][0], -V[0][1])
    if det(V[4], close) != p:
        msgs.append(f"closing edge: determinant {det(V[4], close)} != {p}")
    if V[5] != close:
        msgs.append(f"closure: v5 = {V[5]}, expected {close}")
    if V[6] != (-V[1][0], -V[1][1]):
        msgs.append(f"closure: v6 = {V[6]}, expected {(-V[1][0], -V[1][1])}")
    return msgs


def run(primes=(5, 7, 11, 13, 17, 19, 23, 29, 31)):
    ok = True
    for p in primes:
        tri = ford_triples(p)
        pentagons, bad = set(), 0
        for (s, t, m) in tri:
            u, v = p * s, s * t - 1
            if gcd(u, v) != 1:
                bad += 1
                continue
            S = p * (u + v + 1)
            if S % (u * v):
                bad += 1
                continue
            g = S // (u * v)
            q = quiddity_from_pair(p, g * u - p, g * v - p)
            V, err = pentagon(p, q)
            if err:
                print(f"  p={p} triple {(s,t,m)}: {err}")
                bad += 1
                continue
            msgs = check(p, V)
            if msgs:
                print(f"  p={p} triple {(s,t,m)}: " + "; ".join(msgs))
                bad += 1
                continue
            pentagons.add(min(tuple(V[i:5] + V[:i]) for i in range(5)))
        status = "OK" if bad == 0 else f"FAIL ({bad})"
        if bad:
            ok = False
        print(f"p={p}: C(p) = {len(tri)}, pentagons built = {len(tri)-bad}, "
              f"distinct up to rotation = {len(pentagons)}, 5C(p) = {5*len(tri)}   {status}")
    return ok


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
