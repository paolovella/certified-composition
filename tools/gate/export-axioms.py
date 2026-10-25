#!/usr/bin/env python3
"""List every axiom an NDJSON export (lean4export 3.x) declares, and fail on any outside an allow
list. Declared, not used: the repo admits no new axioms at all (CLAUDE.md), so an unused one is a
violation too, and nanoda (run by tools/gate/export-check.sh) separately refuses any declaration
that uses an axiom outside the list.

usage: tools/gate/export-axioms.py EXPORT.ndjson [ALLOWED ...]
       (default allow list: propext Classical.choice Quot.sound)
"""
import json
import sys

STD = ["propext", "Classical.choice", "Quot.sound"]
# Declared by Lean's prelude in every export. Only its declaration is exempt here: a use is refused
# by nanoda's allow list (tools/gate/export-check.sh) and by `lake check`.
DECLARED_ONLY = {"sorryAx"}


def main():
    path = sys.argv[1]
    allowed = set(sys.argv[2:] or STD)
    names = {0: ""}
    axioms = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.startswith('{"in":'):
                r = json.loads(line)
                if "str" in r:
                    pre, s = names[r["str"]["pre"]], r["str"]["str"]
                else:                                   # numeric name component
                    pre, s = names[r["num"]["pre"]], str(r["num"]["i"])
                names[r["in"]] = f"{pre}.{s}" if pre else s
            elif line.startswith('{"axiom":'):
                axioms.append(json.loads(line)["axiom"]["name"])
    declared = sorted({names[n] for n in axioms})
    bad = [a for a in declared if a not in allowed and a not in DECLARED_ONLY]
    print(f"export-axioms: {len(declared)} declared: {', '.join(declared)}")
    if bad:
        print(f"export-axioms: NOT ALLOWED: {', '.join(bad)}")
        sys.exit(1)
    print("export-axioms: ok")


if __name__ == "__main__":
    main()
