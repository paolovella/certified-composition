#!/usr/bin/env python3
"""RC-01 step 5: hand-written mutants of the front end's rules. Each must fail to build.

Usage, from l-core/ after `lake build LCore.Slice2.CSrc LCore.Slice2.CT`: python3 ../research/2026-11/cfront_mut.py <scratch directory>
"""
import subprocess, sys
src = open('LCore/Slice2/CFront.lean').read()
M = [
 ("an index at the loop counter may pass the end", "| some (i, N) => x == i && N ≤ len", "| some (i, N) => x == i"),
 ("a masked index may pass the end", "| .bin .and _ (.num m) => m < len", "| .bin .and _ (.num m) => true"),
 ("any index is in range", "def inRange (loop : Option (List Nat × Nat)) (len : Nat) : CE → Bool\n", "def inRange (loop : Option (List Nat × Nat)) (len : Nat) (_ : CE) : Bool := true\ndef inRange' (loop : Option (List Nat × Nat)) (len : Nat) : CE → Bool\n"),
 ("an array may be read twice in a statement", "if u.contains base || !inRange loop len i then none", "if !inRange loop len i then none"),
 ("any local name is allowed", "def okLocal (x : List Nat) : Bool := !x.any isDigit && x.head? != some 116 && x != [99] && x != [114]", "def okLocal (_ : List Nat) : Bool := true"),
 ("a loop may start anywhere", "if k == 0 && i2 == i && i3 == i", "if i2 == i && i3 == i"),
 ("the loop's update may name another variable", "if k == 0 && i2 == i && i3 == i", "if k == 0 && i2 == i"),
 ("a missing define reads as 0", "    | none => none\n  | (.int, x) :: ps, .n k", "    | none => (bindArgs outer len defs ps as).map ((x, .lit 0) :: ·)\n  | (.int, x) :: ps, .n k"),
 ("the array length is not checked", "if F.inline || !(len == 8 || len == 16 || len == 32 || len == 64) ||", "if F.inline ||"),
 ("the inlined function need not be inline", "if !G.inline || G.name == F.name then none", "if G.name == F.name then none"),
 ("a shift may be 64 or more", "    if k < 64 then (rdE env loop a u).map", "    if true then (rdE env loop a u).map"),
 ("the loop bound need not fit an int", "  | .num k => if k < 2 ^ 31 then some k else none\n  | .var x => match look env x with\n    | some (.lit k) => if k < 2 ^ 31", "  | .num k => some k\n  | .var x => match look env x with\n    | some (.lit k) => if true"),
 ("|= forgets the old value", "[.assign (str x) (.bin .or (.var (str x)) q.2.1)] ++ cs\n    | _ => none\n  | _ => none", "[.assign (str x) q.2.1] ++ cs\n    | _ => none\n  | _ => none"),
 ("the index is i + c, not N - c", "(.bin .sub (lit N) (.var \"c\"))", "(.add (lit N) (.var \"c\"))"),
 ("^ reads as |", "        | .xor => some (.bin .xor qa.2.1 qb.2.1)", "        | .xor => some (.bin .or qa.2.1 qb.2.1)"),
 ("the operands of - are swapped", "        | .sub => some (.bin .sub qa.2.1 qb.2.1)", "        | .sub => some (.bin .sub qb.2.1 qa.2.1)"),
 ("& binds looser than ^", "  | .sym .caret => if lvl == 1 then some .xor else none\n  | .sym .amp => if lvl == 2", "  | .sym .caret => if lvl == 2 then some .xor else none\n  | .sym .amp => if lvl == 1"),
 ("a U suffix is not read", "  | 85 :: t => t\n", ""),
]
bad = 0
for name, old, new in M:
    assert src.count(old) == 1, name
    p = sys.argv[1] + '/MutF.lean'
    open(p, 'w').write(src.replace(old, new))
    r = subprocess.run(['lake', 'env', 'lean', '-D', 'autoImplicit=false', p], capture_output=True, text=True)
    errs = [l for l in r.stdout.splitlines() if 'error' in l]
    print(('killed  ' if errs else 'SURVIVED'), name, '|', len(errs), 'errors')
    bad += not errs
print('survivors:', bad, 'of', len(M))
sys.exit(1 if bad else 0)
