#!/usr/bin/env python3
"""Audit lean/PAPER_MAP.md against the paper and the library.

Checks, in order:

  1. every numbered statement of the paper appears exactly once in the map,
  2. every map row corresponds to a statement of the paper,
  3. the totals recorded in the map match the rows,
  4. every declaration named in the map exists in the Lean sources.

The axiom check is not run here because it needs a Lean toolchain; continuous integration
runs `#print axioms` on the declarations and rejects anything outside `propext`,
`Classical.choice`, `Quot.sound`.
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEX = ROOT / "paper" / "rational_friezes.tex"
MAP = ROOT / "lean" / "PAPER_MAP.md"
LEAN = ROOT / "lean" / "VicoEnum"

STATEMENT = re.compile(
    r"\\begin\{(theorem|proposition|lemma|corollary|conjecture)\}"
    r"(\[[^\]]*\])?\s*\\label\{([^}]*)\}")
ROW = re.compile(r"^\|[^|]*\|\s*`([^`]+)`\s*\|\s*(VERIFIED|PROVED|CONJECTURE)\s*\|([^|]*)\|",
                 re.M)
DECL = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")


def lean_declarations():
    out = subprocess.run(
        ["grep", "-rhoE", r"^(theorem|lemma|def|noncomputable def) [A-Za-z_][A-Za-z0-9_']*",
         str(LEAN)],
        capture_output=True, text=True).stdout
    return {line.split()[-1] for line in out.splitlines() if line.strip()}


def run():
    tex, mp = TEX.read_text(), MAP.read_text()
    paper = [m.group(3) for m in STATEMENT.finditer(tex)]
    rows = ROW.findall(mp)
    mapped = [r[0] for r in rows]
    ok = True

    missing = [l for l in paper if l not in mapped]
    extra = [l for l in mapped if l not in paper]
    dups = {l for l in mapped if mapped.count(l) > 1}
    if missing:
        ok = False
        print(f"  statements not in the map: {missing}")
    if extra:
        ok = False
        print(f"  map rows with no statement: {extra}")
    if dups:
        ok = False
        print(f"  duplicate map rows: {sorted(dups)}")

    counts = {}
    for _, status, _ in rows:
        counts[status] = counts.get(status, 0) + 1
    claimed = re.search(
        r"\*\*(\d+) VERIFIED\*\*, \*\*(\d+) PROVED\*\*, \*\*(\d+) CONJECTURE\*\*", mp)
    if claimed:
        want = tuple(int(x) for x in claimed.groups())
        have = (counts.get("VERIFIED", 0), counts.get("PROVED", 0),
                counts.get("CONJECTURE", 0))
        if want != have:
            ok = False
            print(f"  totals claim {want} but the rows give {have}")

    decls = lean_declarations()
    named = {d for _, _, cell in rows for d in DECL.findall(cell)}
    absent = sorted(d for d in named if d not in decls)
    if absent:
        ok = False
        print(f"  declarations named but absent from the library: {absent}")

    print(f"paper statements {len(paper)}, map rows {len(mapped)}, "
          f"declarations named {len(named)}")
    print(f"VERIFIED {counts.get('VERIFIED', 0)}, PROVED {counts.get('PROVED', 0)}, "
          f"CONJECTURE {counts.get('CONJECTURE', 0)}")
    print("paper map audit: OK" if ok else "paper map audit: FAILED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
