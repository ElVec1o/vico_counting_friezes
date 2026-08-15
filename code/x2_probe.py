#!/usr/bin/env python3
"""Step 1 of the exhaustion sweep (I2): is T(p,5) a standard arithmetic function of p?

Tests T(p,5)/10 against a library of candidates before any machinery is designed.
A hit here closes the crux with no invention at all.
"""
from math import gcd

def d(n):
    c, m, q = 1, n, 2
    while q * q <= m:
        e = 0
        while m % q == 0: e += 1; m //= q
        c *= e + 1; q += 1
    return c * (2 if m > 1 else 1)

def sig(n):
    s, i = 0, 1
    while i * i <= n:
        if n % i == 0:
            s += i
            if i != n // i: s += n // i
        i += 1
    return s

def omega(n):
    c, m, q = 0, n, 2
    while q * q <= m:
        if m % q == 0:
            c += 1
            while m % q == 0: m //= q
        q += 1
    return c + (1 if m > 1 else 0)

rows = [l.split(',') for l in open('t5_primes.csv').read().splitlines()[1:] if l.strip()]
data = [(int(a), int(b)) for a, b in rows]

cands = {
    'd(p-1)':        lambda p: d(p - 1),
    'd(p+1)':        lambda p: d(p + 1),
    'd(p^2-1)':      lambda p: d(p * p - 1),
    'd(p-1)+d(p+1)': lambda p: d(p - 1) + d(p + 1),
    'd(2(p-1))':     lambda p: d(2 * (p - 1)),
    'd(2(p+1))':     lambda p: d(2 * (p + 1)),
    'd((p^2-1)/2)':  lambda p: d((p * p - 1) // 2) if p > 2 else 0,
    'd((p^2-1)/4)':  lambda p: d((p * p - 1) // 4) if p > 2 else 0,
    'd((p^2-1)/8)':  lambda p: d((p * p - 1) // 8) if p > 2 and (p*p-1) % 8 == 0 else 0,
    'sigma(p-1)':    lambda p: sig(p - 1),
    'omega(p^2-1)':  lambda p: omega(p * p - 1),
}

print("exact matches against T(p,5)/10:")
T = {p: v // 10 for p, v in data}
any_hit = False
for name, f in cands.items():
    ok = all(f(p) == T[p] for p, _ in data if p > 2)
    n_match = sum(1 for p, _ in data if p > 2 and f(p) == T[p])
    print(f"  {name:16s} exact on {n_match:2d}/{len(data)-1} primes   {'MATCH' if ok else ''}")
    any_hit |= ok

print()
print("affine fits  T/10 = a*f(p) + b  (exact on all primes p>2)?")
for name, f in cands.items():
    pts = [(f(p), T[p]) for p, _ in data if p > 2]
    xs = sorted({x for x, _ in pts})
    if len(xs) < 2: continue
    (x1, y1), (x2, y2) = pts[0], next(q for q in pts if q[0] != pts[0][0])
    if x2 == x1: continue
    a = (y2 - y1) / (x2 - x1)
    b = y1 - a * x1
    if all(abs(a * x + b - y) < 1e-9 for x, y in pts):
        print(f"  {name}: a={a}, b={b}  EXACT AFFINE FIT")

print()
print("dependence on residue class of p:")
for m in (3, 4, 5, 6, 8, 12, 24):
    groups = {}
    for p, _ in data:
        if p > 2: groups.setdefault(p % m, []).append(T[p])
    spread = {r: (min(v), max(v)) for r, v in groups.items()}
    print(f"  p mod {m:2d}: " + "  ".join(f"{r}:{lo}-{hi}" for r, (lo, hi) in sorted(spread.items())))

if not any_hit:
    print()
    print("no exact match among the standard candidates.")
