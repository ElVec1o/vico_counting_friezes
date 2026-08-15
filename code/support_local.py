"""The local count of Proposition prop:support, by direct enumeration.

At a prime with p^a || N and p^b || M, the M-th term of eq:decomp contributes
exactly when d_M | M and M | N^2, which read a <= 2b and b <= 2a. This script
enumerates the admissible b and compares with the closed form 2a - ceil(a/2) + 1
proved as `local_count` in lean/VicoEnum/SupportCount.lean.

Usage: python3 support_local.py [AMAX]      (default AMAX = 40)
"""

import sys


def main():
    amax = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    bad = 0
    for a in range(amax + 1):
        bs = [b for b in range(0, 2 * a + 1) if a <= 2 * b]
        closed = 2 * a - -(-a // 2) + 1
        if len(bs) != closed:
            print(f"MISMATCH at a={a}: enumerated {len(bs)}, formula {closed}")
            bad += 1
        elif a <= 5:
            print(f"a={a}: admissible b = {bs}, count {len(bs)}")
    print(f"checked a = 0..{amax}: {'all agree' if bad == 0 else f'{bad} mismatches'}")


if __name__ == "__main__":
    main()
