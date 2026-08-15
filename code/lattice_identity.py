#!/usr/bin/env python3
"""Check the cotangent identity underlying the lattice-geometry route to U2.

With u_i the KSSZ path vectors, det(u_i,u_{i+1}) = R and theta_i the angle from
u_i to u_{i+1}, eliminating the lengths from |u_i||u_{i+1}| sin theta_i = R gives

    a_i = (R / |u_i|^2) * ( cot theta_{i-1} + cot theta_i ),      sum theta_i = pi.

That turns the uniform bound into a constrained optimisation over the angles and
the lattice lengths |u_i|, which is the route that replaces the divisibility grind.
"""
import math, sys
sys.path.insert(0, ".")
from fractions import Fraction as F
from fan_family import fan


def vectors(quid):
    n = len(quid)
    u = [(F(0), F(1)), (F(-1), F(0))]        # det(u_0,u_1) = 1
    for i in range(1, n + 2):
        a = quid[i % n]
        u.append((a * u[-1][0] - u[-2][0], a * u[-1][1] - u[-2][1]))
    return u


def det(p, q): return float(p[0] * q[1] - p[1] * q[0])
def dot(p, q): return float(p[0] * q[0] + p[1] * q[1])
def nrm(p):    return math.hypot(float(p[0]), float(p[1]))
def ang(p, q): return math.atan2(det(p, q), dot(p, q))


if __name__ == "__main__":
    R = 1.0
    for (n, N) in ((7, 3), (9, 2), (11, 2)):
        q = fan(n, N)
        u = vectors(q)
        th = [ang(u[i], u[i + 1]) for i in range(n + 1)]
        print(f"n={n} N={N}:  sum(theta_i, i=0..n-1)/pi = {sum(th[:n])/math.pi:.9f}")
        worst = 0.0
        for i in range(1, n):
            pred = (R / nrm(u[i]) ** 2) * (1 / math.tan(th[i - 1]) + 1 / math.tan(th[i]))
            worst = max(worst, abs(pred - float(q[i % n])))
        print(f"          max |formula - a_i| over i = 1..{n-1}:  {worst:.3e}")
        i = 1
        print(f"          at the small entry i=1: a={float(q[1]):.4f}, "
              f"|u_1|={nrm(u[1]):.4f}, theta_0={th[0]:.4f}, theta_1={th[1]:.4f}")
        print()
