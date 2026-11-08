#!/usr/bin/env python3
"""S-USABLE S2: the front end's kernel cost against text length.

From the pinned verify.c excerpt that CSrc.verify16C holds (lines 60-75 and 79-83), it builds texts whose loop body
repeats `d |= x[i] ^ y[i];` m times, and one variant the parser must refuse (an `if` in the body). For each it writes a
Lean file that proves `(read16 codes).isSome = true` (or `= false` for the refused one) by `decide +kernel`, under the
profiler. The m = 1 text is verify16C itself, so the vacuity check is that it reads and takes about what CFront does.

Usage, from the repo root: python3 research/2026-11/usable/s2_gen.py OUT m1 m2 ...
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def excerpt():
    ls = (ROOT / "third_party/libsodium-1.0.20/verify.c").read_text().split("\n")
    return ls[59:75], ls[78:83]


def text(m, refused=False):
    a, b = excerpt()
    body = [l for l in a]
    k = body.index("        d |= x[i] ^ y[i];")
    stmt = "        if (x[i] != y[i]) return -1;" if refused else "        d |= x[i] ^ y[i];"
    body = body[:k] + [stmt] * m + body[k + 1:]
    return "\n".join(body + [""] + b) + "\n"


HEAD = """import LCore.Slice2.CFront
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler.threshold 0
open LCore.Slice2.CFront
"""


def main():
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    specs = [(int(m), False) for m in sys.argv[2:]] + [(1, True)]
    for m, refused in specs:
        t = text(m, refused)
        codes = ", ".join(str(ord(c)) for c in t)
        name = f"read_m{m}" + ("_refused" if refused else "")
        want = "false" if refused else "true"
        (out / f"{name}.lean").write_text(
            HEAD + f"def T : List Nat := [{codes}]\n\n"
            f'#eval IO.println "== {name} chars {len(t)}"\n'
            f"set_option profiler true in\ntheorem t_read : (read16 T).isSome = {want} := by decide +kernel\n"
            '#eval IO.println "== end"\n')
        print(name, len(t))


if __name__ == "__main__":
    main()
