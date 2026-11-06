#!/usr/bin/env python3
"""VS-1 step 9: what the checker refuses, compiled anyway, is seen to leak under QEMU; what it accepts is not.

For each program, two binaries that differ only in the secret word. The observation is the PC trace, the instruction count and a0
at the exit, read from QEMU's log. A refused program must differ, and `clean` must not.

Usage, from l-core/: python3 test/refused_diff.py <scratch directory>
"""
import os
import re
import subprocess
import sys

def observe(p, log):
    if os.path.exists(log):
        os.remove(log)
    subprocess.run(["qemu-riscv64", "-one-insn-per-tb", "-d", "cpu,nochain", "-D", log, p], capture_output=True)
    pcs, a0 = [], None
    for line in open(log, errors="replace"):
        m = re.match(r"\s*pc\s+([0-9a-f]+)", line)
        if m:
            pcs.append(int(m.group(1), 16))
        m = re.search(r"x10/a0\s+([0-9a-f]+)", line)
        if m:
            a0 = int(m.group(1), 16)
    return pcs, a0

def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    g = subprocess.run(["lake", "env", "lean", "--run", "test/RefusedGen.lean", d], capture_output=True, text=True)
    if g.returncode != 0:
        print(g.stdout[-2000:], g.stderr[-800:])
        return 2
    bad = 0
    for line in g.stdout.splitlines():
        name, verdict = line.split()[0], line.split()[1]
        x, ax = observe(f"{d}/{name}_x", f"{d}/{name}_x.log")
        y, ay = observe(f"{d}/{name}_y", f"{d}/{name}_y.log")
        channels = []
        if x != y:
            channels.append(f"PC trace ({len(x)} vs {len(y)} instructions)")
        if ax != ay:
            channels.append(f"result ({ax} vs {ay})")
        leaks = bool(channels)
        good = leaks == (verdict == "refused")
        bad += not good
        print(f"{'ok  ' if good else 'FAIL'} {name:14} {verdict:9} {'leaks through ' + ', '.join(channels) if leaks else 'no difference'}")
    print(f"refused-diff: {bad} failed")
    return 1 if bad else 0

sys.exit(main())
