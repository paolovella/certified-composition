#!/usr/bin/env python3
"""AI-01's witness: through `lake build`, which reads the lakefile (`lake env lean` does not), a planted unknown name is refused,
and the same module without it is accepted. Restores each file, and fails if a refusal is for any other reason.

Usage, from the repo root: python3 research/2026-11/autoimplicit_witness.py
"""
import subprocess, sys

PLANT = '\n\ntheorem plantedAutoImplicitName : plantedName = plantedName := rfl\n'
CASES = [('.', 'workspace/CertifiedComposition.lean', 'CertifiedComposition'),
         ('conf-typing', 'ConfTyping/Imp.lean', 'ConfTyping.Imp'),
         ('transport-calculus', 'TransportCalculus.lean', 'TransportCalculus'),
         ('transport-kernel', 'TransportKernel/LipschitzReceive.lean', 'TransportKernel.LipschitzReceive')]


def build(pkg, mod):
    return subprocess.run(['lake', 'build', mod], cwd=pkg, capture_output=True, text=True, timeout=1500)


bad = 0
for pkg, f, mod in CASES:
    path = f'{pkg}/{f}'
    src = open(path).read()
    accepted = build(pkg, mod).returncode == 0
    try:
        open(path, 'w').write(src + PLANT)
        r = build(pkg, mod)
    finally:
        open(path, 'w').write(src)
    refused = r.returncode != 0 and 'Unknown identifier `plantedName`' in r.stdout + r.stderr
    restored = build(pkg, mod).returncode == 0
    print(pkg, '| accepted without it:', accepted, '| refused with it, for that reason:', refused, '| restored:', restored, flush=True)
    bad += not (accepted and refused and restored)
sys.exit(1 if bad else 0)
