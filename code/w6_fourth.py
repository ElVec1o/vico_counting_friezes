"""The fourth W6 condition is independent of the other three.

W6 N p q r e requires  p q r = N^2(e+p+r),  e | pq,  e | qr,  e | N(p+r).
The first three do not imply the fourth: this enumerates triples satisfying them and
counts the failures. That is why width6_from_frieze proves only three of the four, and
why the fourth carries its own row in the paper.
"""

def run(Nmax=8):
    tot = bad = 0
    examples = []
    for N in range(1, Nmax + 1):
        B = 2 * N ** 3 + 2 * N * N
        for p in range(1, B + 1):
            for q in range(1, B + 1):
                for r in range(1, B + 1):
                    s = p * q * r
                    if s % (N * N):
                        continue
                    e = s // (N * N) - p - r
                    if e <= 0 or (p * q) % e or (q * r) % e:
                        continue
                    tot += 1
                    if (N * (p + r)) % e:
                        bad += 1
                        if len(examples) < 4:
                            examples.append((N, p, q, r, e))
    print(f"triples with pqr = N^2(e+p+r), e|pq, e|qr, over N <= {Nmax}: {tot}")
    print(f"of which e does not divide N(p+r): {bad}")
    print(f"first counterexamples (N,p,q,r,e): {examples}")

if __name__ == "__main__":
    run()
