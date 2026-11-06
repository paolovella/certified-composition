#!/usr/bin/env python3
"""AI-01: a fingerprint of every declaration in a package, so that "the statements did not change" is checked and not hoped.

One line per non-internal declaration: its name, its kind, a hash of its full type as `repr` prints it, and, unless it is a
theorem, a hash of its value. `repr` is used because `Expr.hash` ignores binder names and binder kinds, and a binder made
explicit in the wrong place, or with the wrong kind, is what this has to catch. Proofs are left out: their terms may
change without changing what is proved. Hygiene suffixes on binder names are erased, and only those (see `norm`).

Usage, from the repo root: python3 research/2026-11/decl_fingerprint.py <package> <library root> <output file>
"""
import os, subprocess, sys, tempfile

pkg, root, out = sys.argv[1:4]
mods = []
for d, _, files in os.walk(os.path.join(pkg, root)):
    for n in files:
        if n.endswith('.lean'):
            mods.append(os.path.relpath(os.path.join(d, n), pkg)[:-5].replace(os.sep, '.'))
if os.path.exists(os.path.join(pkg, root + '.lean')):
    mods.append(root)
mods.sort()
assert mods, 'no modules found'

src = ''.join(f'import {m}\n' for m in mods) + 'import Lean\nopen Lean\n' + r'''
/-- Hygiene suffixes off binder names, and nothing else. Lean's generated `.below` and `.brecOn` name their binders with a counter
    (`ih._@.ConfTyping.Imp.2519133743._hygCtx._hyg.182`) that moves when a file's text does. -/
partial def norm : Expr → Expr
  | .forallE n t b i => .forallE n.eraseMacroScopes (norm t) (norm b) i
  | .lam n t b i => .lam n.eraseMacroScopes (norm t) (norm b) i
  | .letE n t v b d => .letE n.eraseMacroScopes (norm t) (norm v) (norm b) d
  | .app f a => .app (norm f) (norm a)
  | .mdata m e => .mdata m (norm e)
  | .proj s i e => .proj s i (norm e)
  | e => e
def fp (e : Expr) : UInt64 := hash (toString (repr (norm e)))
def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

run_cmd do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless (`ROOT).isPrefixOf m do continue
    let v := match ci with
      | .thmInfo _ => "-"
      | _ => match ci.value? with
        | some e => toString (fp e)
        | none => "-"
    lines := lines.push s!"{n}\t{kind ci}\t{fp ci.type}\t{v}"
  logInfo ("\n".intercalate (lines.qsort (· < ·)).toList)
'''.replace('ROOT', root)

with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
    f.write(src)
r = subprocess.run(['lake', 'env', 'lean', f.name], cwd=pkg, capture_output=True, text=True)
os.unlink(f.name)
if r.returncode != 0:
    sys.exit('the fingerprint did not run:\n' + r.stdout[-1500:] + r.stderr[-500:])
lines = [l for l in r.stdout.splitlines() if l.count('\t') == 3]
lines = [l.split(': ', 1)[-1] if '.lean:' in l.split('\t')[0] else l for l in lines]
if len(lines) < 10:
    sys.exit('the fingerprint printed almost nothing:\n' + r.stdout[:800])
open(out, 'w').write('\n'.join(lines) + '\n')
print(pkg, 'modules', len(mods), 'declarations', len(lines))
