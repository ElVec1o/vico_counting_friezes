"""Where the exponent 1/3 is lost in C(p) << p^{1/3+eps}.

Compares, for A = (2p)^{1/3}:
    sum_{a<=A} d(ap+1)      the quantity thm:primecube bounds
    A log p                 its predicted size
    sum_{a<=A} R_a(p)       the truth, R_a(p) = #{D | ap+1 : D = -1 mod a}
The ratio of the last two is the factor discarded by R_a(p) <= d(ap+1), namely phi(a) on
average. Also checks the spacing claim of prop:spacing: divisors of ap+1 in the class
-1 mod a are pairwise at least a apart.
"""
import math

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

def run(primes=(10007, 100003, 1000003, 10000019)):
    print("        p       A     sum d(ap+1)   A log p    sum R_a   log^2 p    loss")
    violations = 0
    for p in primes:
        A = int((2 * p) ** (1 / 3))
        S = R = 0
        for a in range(1, A + 1):
            ds = divisors(a * p + 1)
            S += len(ds)
            cls = sorted(x for x in ds if (x + 1) % a == 0)
            R += len(cls)
            violations += sum(1 for i in range(1, len(cls)) if cls[i] - cls[i-1] < a)
        print(f"  {p:>9}   {A:>5}      {S:>8}   {A*math.log(p):8.0f}   {R:>7}   "
              f"{math.log(p)**2:7.1f}  {S/max(R,1):6.2f}")
    print(f"\nspacing violations (prop:spacing): {violations}")

if __name__ == "__main__":
    run()
