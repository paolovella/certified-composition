import subprocess, sys
src = open('LCore/Slice/Source.lean').read()
M = [
 ("assign: secret source marks nothing", "if highE H e then some (x :: H) else", "if highE H e then some H else"),
 ("assign: never clears the target", "else some (H.filter (· ≠ x))", "else some H"),
 ("assign: clears when reading a secret", "if highE H e then some (x :: H) else", "if false then some (x :: H) else"),
 ("ite: accepts a secret guard", "    if highE H e then none\n", "    if false then none\n"),
 ("ite: drops the second arm", "fun Hb => Ha ++ Hb", "fun _ => Ha"),
 ("ite: drops the first arm", "fun Hb => Ha ++ Hb", "fun Hb => Hb"),
 ("ret: accepts a secret result", "if highE H p.ret then none else", "if false then none else"),
 ("init: marks no secret", "if P k then x :: highInit P xs (k + 1) else", "if false then x :: highInit P xs (k + 1) else"),
 ("var: never high", "| .var x   => decide (x ∈ H)", "| .var _   => false"),
 ("add: reads only the left", "| .add a b => highE H a || highE H b", "| .add a _ => highE H a"),
 ("budget: ite ignores the arms' max", "| .ite _ a b => 1 + max (costOf a) (costOf b)", "| .ite _ a _ => 1 + costOf a"),
]
bad = 0
for name, old, new in M:
    assert src.count(old) == 1, name
    p = sys.argv[1] + '/Mut.lean'
    open(p, 'w').write(src.replace(old, new))
    r = subprocess.run(['lake', 'env', 'lean', p], capture_output=True, text=True)
    errs = [l for l in r.stdout.splitlines() if ': error' in l or 'error:' in l]
    print(('killed  ' if errs else 'SURVIVED'), name, '|', len(errs), 'errors')
    bad += not errs
print('survivors:', bad, 'of', len(M))
