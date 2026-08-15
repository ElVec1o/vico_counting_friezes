#!/usr/bin/env python3
"""Block statistics for Atom B, the count  #{t >= 1 : p+t has a divisor = -1 mod t}.

Reads data/atomB.csv, produced by code/atom_b.rs (which writes the per-prime rows and
computes no statistics of its own). Reports the mean of that count against log^2 p and
against p^{1/3}, over five blocks of equal size.

Conjecture conj:order at a prime is equivalent to this count being p^{o(1)}, so the
question is whether the log^2 p column stabilises and the p^{1/3} column decays.
"""
import math, sys, os

def main(path=None):
    path = path or os.path.join(os.path.dirname(__file__), "..", "data", "atomB.csv")
    rows = []
    with open(path) as f:
        next(f)
        for line in f:
            if line.strip():
                p, contrib, C, mx = (int(x) for x in line.split(","))
                rows.append((p, contrib))
    n = len(rows)
    k = 5
    sz = n // k
    print(f"{n} primes, {rows[0][0]} <= p <= {rows[-1][0]}, {k} blocks of {sz}")
    print("  block          p-range      mean/log^2 p   mean/p^(1/3)")
    for i in range(k):
        seg = rows[i * sz:(i + 1) * sz] if i < k - 1 else rows[i * sz:]
        a = sum(c / math.log(p) ** 2 for p, c in seg) / len(seg)
        b = sum(c / p ** (1 / 3) for p, c in seg) / len(seg)
        print(f"    {i+1}      {seg[0][0]:6d}..{seg[-1][0]:6d}        {a:.3f}          {b:.2f}")

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else None)
