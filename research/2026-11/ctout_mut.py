#!/usr/bin/env python3
"""RC-02 step 4: hand-written mutants of ctOutCheck, its eraser and its observer. Each must fail to build.

Usage, from l-core/: python3 ../research/2026-11/ctout_mut.py <scratch directory>
"""
import subprocess, sys
src = open('LCore/Slice2/CTOut.lean').read()
M = [
 ("eraseC keeps the output", "  | .emitB _ => .skip\n  | .seq a b", "  | .emitB ns => .emitB ns\n  | .seq a b"),
 ("noOut reads the output", "decide (c ≠ .ext \"ret\" ∧ c ≠ .emit \"out\")", "decide (c ≠ .ext \"ret\")"),
 ("noOut reads the result", "decide (c ≠ .ext \"ret\" ∧ c ≠ .emit \"out\")", "decide (c ≠ .emit \"out\")"),
 ("ctOutCheck checks the program unerased", "def ctOutCheck (P : Nat → Bool) (p : Prog) : Bool := ctCheck P (eraseP p)", "def ctOutCheck (P : Nat → Bool) (p : Prog) : Bool := ctCheck P p"),
]
# Vacuity: the unmutated copy, built the same way, must have no errors, or every mutant is "killed" for nothing.
p0 = sys.argv[1] + '/MutO.lean'
open(p0, 'w').write(src)
r0 = subprocess.run(['lake', 'env', 'lean', '-D', 'autoImplicit=false', p0], capture_output=True, text=True)
base = [l for l in r0.stdout.splitlines() if 'error' in l]
print('baseline:', 'builds' if not base else 'FAILS: ' + base[0][:150])
if base:
    sys.exit(2)
bad = 0
for name, old, new in M:
    assert src.count(old) == 1, name
    p = sys.argv[1] + '/MutO.lean'
    open(p, 'w').write(src.replace(old, new))
    r = subprocess.run(['lake', 'env', 'lean', '-D', 'autoImplicit=false', p], capture_output=True, text=True)
    errs = [l for l in r.stdout.splitlines() if 'error' in l]
    print(('killed  ' if errs else 'SURVIVED'), name, '|', len(errs), 'errors')
    bad += not errs
print('survivors:', bad, 'of', len(M))
sys.exit(1 if bad else 0)
