#!/usr/bin/env python3
"""VS-2 step 4: hand-written mutants of the second slice's checker, since tools/mutants.py does not scan l-core.

Each mutant must fail to build. Usage, from l-core/: python3 ../research/2026-11/slice2_mut.py <scratch directory>
"""
import subprocess, sys
src = open('LCore/Slice2/Source.lean').read()
M = [
 ("assign: a secret source marks nothing", "if highE st.1 e then some (x :: st.1, st.2) else some (st.1.filter (· ≠ x), st.2)\n  | .seq", "if highE st.1 e then some st else some (st.1.filter (· ≠ x), st.2)\n  | .seq"),
 ("assign: never clears its target", "if highE st.1 e then some (x :: st.1, st.2) else some (st.1.filter (· ≠ x), st.2)\n  | .seq", "if highE st.1 e then some (x :: st.1, st.2) else some st\n  | .seq"),
 ("ite: accepts a secret guard", "  | .ite e a b =>\n    if highE st.1 e then none", "  | .ite e a b =>\n    if false then none"),
 ("ite: forgets the second arm's variables", "(sa.1 ++ sb.1, sa.2 || sb.2)", "(sa.1, sa.2 || sb.2)"),
 ("ite: forgets the first arm's variables", "(sa.1 ++ sb.1, sa.2 || sb.2)", "(sb.1, sa.2 || sb.2)"),
 ("ite: forgets the second arm's array bit", "(sa.1 ++ sb.1, sa.2 || sb.2)", "(sa.1 ++ sb.1, sa.2)"),
 ("ite: forgets the first arm's array bit", "(sa.1 ++ sb.1, sa.2 || sb.2)", "(sa.1 ++ sb.1, sb.2)"),
 ("loop: accepts a secret guard", "  | .loop e b =>\n    if highE st.1 e then none", "  | .loop e b =>\n    if false then none"),
 ("loop: no fixed point", "if sub s₁ st then some st\n", "if true then some st\n"),
 ("loop: returns the body's state, unchecked", "if sub s₁ st then some st\n", "if true then some s₁\n"),
 ("loop: the widened guard is not checked", "if highE (s₁.1 ++ st.1) e then none", "if false then none"),
 ("loop: the widened state is not checked", "if sub s₂ (s₁.1 ++ st.1, st.2 || s₁.2) then", "if true then"),
 ("sub: ignores variables", "a.1.all (fun x => decide (x ∈ b.1)) && (!a.2 || b.2)", "(!a.2 || b.2)"),
 ("sub: ignores the array bit", "a.1.all (fun x => decide (x ∈ b.1)) && (!a.2 || b.2)", "a.1.all (fun x => decide (x ∈ b.1))"),
 ("load: accepts a secret index", "  | .load x e =>\n    if highE st.1 e then none", "  | .load x e =>\n    if false then none"),
 ("load: ignores the array bit", "else if st.2 then some (x :: st.1, st.2) else some (st.1.filter (· ≠ x), st.2)", "else some (st.1.filter (· ≠ x), st.2)"),
 ("store: accepts a secret index", "  | .store e v =>\n    if highE st.1 e then none", "  | .store e v =>\n    if false then none"),
 ("store: a secret value leaves the bit low", "some (st.1, st.2 || highE st.1 v)", "some (st.1, st.2)"),
 ("result: accepts a secret", "| some st => !highE st.1 p.ret", "| some _ => true"),
 ("semantics: an access leaks nothing, load", "| .load x e => tick [addrLk (idx (eval e s))] p", "| .load x e => tick [] p"),
 ("semantics: an access leaks nothing, store", "| .store e v => tick [addrLk (idx (eval e s))] p", "| .store e v => tick [] p"),
 # RC-02 step 3: byte stores and outputs
 ("storeB: accepts a secret index", "  | .storeB ns e v =>\n    if highE st.1 e || ns.isEmpty then none", "  | .storeB ns e v =>\n    if false || ns.isEmpty then none"),
 ("storeB: a secret value leaves the words low", "else if highE st.1 v then some (ns ++ st.1, st.2) else some st", "else some st"),
 ("emitB: accepts a secret word", "| .emitB ns => if ns.any (fun y => decide (y ∈ st.1)) then none else some st", "| .emitB ns => some st"),
 ("semantics: a byte store leaks nothing", "| .storeB ns e v => tick [addrLk (bidx ns (eval e s))] p", "| .storeB ns e v => tick [] p"),
 ("semantics: an output emits nothing", "| .emitB ns => etick (.emit \"out\" (outBytes s ns)) p", "| .emitB ns => tick [] p"),
]
bad = 0
for name, old, new in M:
    assert src.count(old) == 1, name
    p = sys.argv[1] + '/Mut2.lean'
    open(p, 'w').write(src.replace(old, new))
    r = subprocess.run(['lake', 'env', 'lean', p], capture_output=True, text=True)
    errs = [l for l in r.stdout.splitlines() if 'error' in l]
    first = next((l.split('error')[0].split(':')[-3] for l in errs), '')
    print(('killed  ' if errs else 'SURVIVED'), name, '|', len(errs), 'errors')
    bad += not errs
print('survivors:', bad, 'of', len(M))
sys.exit(1 if bad else 0)
