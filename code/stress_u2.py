#!/usr/bin/env python3
"""Stress-test U2 far beyond the conjectured maximum.

The width-7 evidence so far used a sweep bound of 12N^2+12, which was chosen, not
proved. Here the sweep runs to a multiple of the conjectured maximum, so that a
counterexample with entries several times larger would be found if one existed.
"""
import sys, time
sys.path.insert(0, ".")
from explore_width7 import width7

if __name__ == "__main__":
    print("width 7: conjectured max is 3N^3+2N^2")
    for N, P in ((1, 120), (2, 160), (3, 260)):
        t0 = time.time()
        S = width7(N, P)
        mx = max(max(t[4]) for t in S)
        pred = 3*N**3 + 2*N*N
        mxparam = max(max(t[:4]) for t in S)
        print(f"  N={N}  sweep P={P} (= {P/pred:.1f}x the conjectured max {pred})")
        print(f"        friezes {len(S)},  max entry {mx},  predicted {pred},  "
              f"{'HOLDS' if mx == pred else 'VIOLATED'}")
        print(f"        largest swept parameter used: {mxparam}   [{time.time()-t0:.0f}s]",
              flush=True)
