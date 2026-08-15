"""Lemma lem:acount, A(p) = 5 + 2C(p), checked by direct enumeration.

  A(p) = #{(u,v) : gcd(u,v) = 1, uv | p(u+v+1)}
  C(p) = #{(s,t,m) in Z_{>0}^3 : s t m = p + t + m}

The condition defining A is symmetric in u and v, and uv <= p(u+v+1) forces
min(u,v) <= 3p; for fixed u, v | p(u+v+1) together with v | pv gives v | p(u+1), so v
runs over the divisors of p(u+1). Both loops are therefore bounded.
"""
from math import gcd

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

def A(p):
    S = set()
    for u in range(1, 3 * p + 1):
        for v in divisors(p * (u + 1)):
            if gcd(u, v) == 1 and (p * (u + v + 1)) % (u * v) == 0:
                S.add((u, v)); S.add((v, u))
    return len(S)

def C(p):
    c = 0
    for s in range(1, p + 3):
        for t in range(1, p + 3):
            m = s * t - 1
            if m >= 1 and (p + t) % m == 0 and (p + t) // m >= 1:
                c += 1
    return c

if __name__ == "__main__":
    primes = [q for q in range(5, 60) if all(q % i for i in range(2, int(q**.5) + 1))]
    print("     p    A(p)   C(p)   5+2C(p)")
    bad = 0
    for p in primes:
        a, c = A(p), C(p)
        if a != 5 + 2 * c:
            bad += 1
        print(f"  {p:>4}  {a:>6} {c:>6}  {5+2*c:>8}")
    print(f"\n{len(primes)} primes, {bad} discrepancies")
