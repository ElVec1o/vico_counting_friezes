#!/usr/bin/env python3
"""Width-7: search for the missing bound on p0, p1, p2  (Rule 3, falsify first).

The proved width-7 bound is p3 <= N^2(N^3 + u + 1) with u = p0p1 - N^2, which still
carries u. To extend the proved region from n <= 6 to n <= 7 we need bounds on
p0, p1, p2 in terms of N alone. This script enumerates every width-7 frieze for a
range of N and tests candidate bounds against the data, reporting the exact ground
covered rather than a verdict.

Progress, ETA and atomic checkpoints per Rule 8. Python is used because the job is
minutes, not hours; if it exceeds the budget it is rewritten in Rust.
"""
import json, os, sys, time
sys.path.insert(0, ".")
from explore_width7 import width7

CKPT = "w7_bound_search.ckpt.json"

def save(d):
    tmp = CKPT + ".tmp"
    with open(tmp, "w") as f:
        json.dump(d, f)
    os.replace(tmp, CKPT)

def main(Nmax):
    state = json.load(open(CKPT)) if os.path.exists(CKPT) else {"rows": {}}
    t0 = time.time()
    for N in range(1, Nmax + 1):
        if str(N) in state["rows"]:
            continue
        S = width7(N, 12 * N * N + 12)
        # parameters are (p0,p1,p2,p3); entries are tup[4]
        mx = {k: max(t[k] for t in S) for k in range(4)}
        mxe = max(max(t[4]) for t in S)
        state["rows"][str(N)] = {"count": len(S), "maxp": mx, "maxentry": mxe}
        save(state)
        done, tot = N, Nmax
        el = time.time() - t0
        eta = el / done * (tot - done)
        print(f"  N={N:2d}  friezes {len(S):6d}  max p0..p3 "
              f"{[mx[k] for k in range(4)]}  max entry {mxe:6d}   "
              f"[{el:5.0f}s, ETA {eta:5.0f}s]", flush=True)

    print()
    print("candidate bounds on the individual parameters, vs the data:")
    print("  N   max p0   max p1   max p2   max p3   3N^3+2N^2   N^3+2N^2   2N^2")
    for N in sorted(map(int, state["rows"])):
        r = state["rows"][str(N)]
        m = r["maxp"]
        print(f"{N:3d} {m['0']:8d} {m['1']:8d} {m['2']:8d} {m['3']:8d}"
              f" {3*N**3+2*N*N:11d} {N**3+2*N*N:10d} {2*N*N:7d}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
