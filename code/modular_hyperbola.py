"""Verification of Proposition prop:modhyp and of identity eq:hyp.

  C(p) = #{(d,e) : de = 1 mod p, ((de-1)/p) | gcd(d+1,e+1)}
  sum_{a<=A} d(ap+1) = #{(d,e) : de = 1 mod p, 1 < de <= Ap+1}

Both are exact bijections, checked by direct enumeration. Every loop is capped by p+2,
which is the largest possible leading coefficient (attained at u = v = 1).
"""
import math

def C(n):
    """#{(a,u,v) in Z_{>0}^3 : a u v = n + u + v}."""
    c = 0
    for a in range(1, n + 3):
        for u in range(1, n + 3):
            m = a * u - 1
            if m >= 1 and (n + u) % m == 0 and (n + u) // m >= 1:
                c += 1
    return c

def C_hyperbola(p):
    """The same count read on the modular hyperbola de = 1 mod p."""
    tot = 0
    for a in range(1, p + 3):
        n = a * p + 1
        x = 1
        while x * x <= n:
            if n % x == 0:
                for xx in {x, n // x}:
                    y = n // xx
                    if (xx + 1) % a == 0 and (y + 1) % a == 0:
                        tot += 1
            x += 1
    return tot

def divisor_sum(p, A):
    return sum(len([x for x in range(1, a * p + 2) if (a * p + 1) % x == 0])
               for a in range(1, A + 1))

def hyperbola_count(p, A):
    return len([(d, e) for a in range(1, A + 1)
                for d in range(1, a * p + 2) if (a * p + 1) % d == 0
                for e in [(a * p + 1) // d]])

if __name__ == "__main__":
    primes = [q for q in range(5, 120) if all(q % i for i in range(2, int(q**.5) + 1))]
    bad1 = sum(1 for p in primes if C(p) != C_hyperbola(p))
    A = 4
    bad2 = sum(1 for p in primes[:15] if divisor_sum(p, A) != hyperbola_count(p, A))
    print(f"prop:modhyp : {len(primes)} primes, {bad1} failures")
    print(f"eq:hyp      : {len(primes[:15])} primes at A={A}, {bad2} failures")
