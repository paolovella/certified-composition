#!/usr/bin/env python3
"""VS-2 steps 6, 7 and 9, and BOUND-01 steps 2 to 4: hand-written mutants of the second slice's lowering, since tools/mutants.py does not scan l-core.

Each mutant must fail to build as far as the machine witnesses. It runs on a copy of the package, never on the working
tree, with each build in its own process group, killed as a group on timeout or above 12 GB resident. A kill counts only with a Lean error at a line of a `.lean` file.

Usage, from the repo root: python3 research/2026-11/slice2_low_mut.py <scratch directory>
"""
import os, re, shutil, signal, subprocess, sys, tempfile, time

WORK = os.path.join(sys.argv[1], 'l-core')
LOW, CHK, PAS, OLD, IMG, TTH, FOR, BUD, BYT = ('LCore/Slice2/Lower.lean', 'LCore/Slice2/Chunk.lean', 'LCore/Slice2/Pass.lean', 'LCore/Slice/Lower.lean', 'LCore/Slice2/Image.lean', 'LCore/Slice2/Teeth.lean', 'LCore/Slice2/For.lean', 'LCore/Slice2/Budget.lean', 'LCore/Slice2/BoundBytes.lean')
CAP_KB = 12 * 2 ** 20
TIMEOUT = 1500

M = [
 ("load reads the wrong word", LOW, "| .load x e => genIdx e ++ [.ld 8 8 (Int.ofNat 512), .sd 8 7", "| .load x e => genIdx e ++ [.ld 8 8 (Int.ofNat 504), .sd 8 7"),
 ("store writes the wrong word", LOW, "| .store e v => genIdx e ++ genE v 1 ++ [.sd 9 8 (Int.ofNat 512)]", "| .store e v => genIdx e ++ genE v 1 ++ [.sd 9 8 (Int.ofNat 504)]"),
 ("store stores the wrong register", LOW, "| .store e v => genIdx e ++ genE v 1 ++ [.sd 9 8 (Int.ofNat 512)]", "| .store e v => genIdx e ++ genE v 1 ++ [.sd 8 8 (Int.ofNat 512)]"),
 ("the index mask misses the array's size", LOW, "genE e 0 ++ [.andi 8 8 (Int.ofNat 63)", "genE e 0 ++ [.andi 8 8 (Int.ofNat 127)"),
 ("the loop's exit lands one short", LOW, ".loop e b =>\n    genE e 0 ++ [.beq 8 0 (Int.ofNat (4 * (sC b + 2)))]", ".loop e b =>\n    genE e 0 ++ [.beq 8 0 (Int.ofNat (4 * (sC b + 1)))]"),
 ("the loop's back edge lands one short", LOW, "(-(Int.ofNat (4 * (sE e + 1 + sC b))))", "(-(Int.ofNat (4 * (sE e + sC b))))"),
 ("a body too big for the exit branch is accepted", LOW, "okC b && decide (sC b + 2 < 1024) && decide (sE e + 1 + sC b < 1024)", "okC b && decide (sE e + 1 + sC b < 1024)"),
 ("a body too big for the back edge is accepted", LOW, "okC b && decide (sC b + 2 < 1024) && decide (sE e + 1 + sC b < 1024)", "okC b && decide (sC b + 2 < 1024)"),
 ("an array load's address does not show", CHK, "(pc + 4 * (sE e + 5), [.addr (Int.ofNat (arrAddr (idx (evalS e t))))])", "(pc + 4 * (sE e + 5), [])"),
 ("a loop forgets to run again", CHK, "(.jmp (pc + 4 * (sE e + 1 + sC b)) pc :: .cmd (.loop e b) pc :: k)", "(.jmp (pc + 4 * (sE e + 1 + sC b)) pc :: k)"),
 ("the budget loses its constant", PAS, "cost c := codeLen p * c + codeLen p", "cost c := codeLen p * c"),
 ("the budget does not grow with the source", PAS, "cost c := codeLen p * c + codeLen p", "cost _ := codeLen p"),
 ("the pass compiles what does not fit", PAS, "if okP p then .ok (code (genP p), xf p)", "if true then .ok (code (genP p), xf p)"),
 ("no fuel for the source", PAS, "  fuel m := m\n", "  fuel _ := 0\n"),
 ("the exit is the wrong syscall", PAS, ".addi 17 0 (Int.ofNat 93), .ecall]\n\ndef okP", ".addi 17 0 (Int.ofNat 94), .ecall]\n\ndef okP"),
 ("the data pointer is wrong", PAS, "[.lui 7 0x20] ++ genC p.body", "[.lui 7 0x21] ++ genC p.body"),
 ("a literal's immediate is off by one", OLD, "else -(Int.ofNat (18446744073709551616 - w.val))", "else -(Int.ofNat (18446744073709551617 - w.val))"),
 ("any literal is accepted", OLD, "(decide (w.val < 2048) || decide (18446744073709549568 ≤ w.val)) && decide (d < 24)", "decide (d < 24)"),
 ("the negative immediate reaches one too far", OLD, "theorem good_addi_neg {rd rs i : Nat} (hd : rd < 32) (hs : rs < 32) (h0 : 0 < i) (hi : i ≤ 2048) :", "theorem good_addi_neg {rd rs i : Nat} (hd : rd < 32) (hs : rs < 32) (h0 : 0 < i) (hi : i ≤ 2049) :"),
 ("one byte of scan's literal is wrong", IMG, "[183, 3, 2, 0, 3, 180, 131, 0,", "[183, 3, 2, 0, 3, 180, 3, 0,"),
 ("one byte of spin's literal is wrong", IMG, "[183, 3, 2, 0, 19, 4, 16, 0,", "[183, 3, 2, 0, 19, 4, 17, 0,"),
 ("the listed instructions are not the image's", IMG, ".addi 9 0 (-1), .add 8 8 9, .sd 8 7 1024, .beq 0 0 (-104),", ".addi 9 0 (-2), .add 8 8 9, .sd 8 7 1024, .beq 0 0 (-104),"),
 ("the index tamper changes nothing", IMG, "(scanNats.take 23 ++ [0] ++ scanNats.drop 24)", "(scanNats.take 23 ++ [64] ++ scanNats.drop 24)"),
 ("the guard tamper changes nothing", IMG, "(scanNats.take 6 ++ [3] ++ scanNats.drop 7)", "(scanNats.take 6 ++ [131] ++ scanNats.drop 7)"),
 ("scan's result is misstated", IMG, "(go scanImage env0 200 5 3).ev = [Slice.Rv.retEv (W64.ofNat 9)]", "(go scanImage env0 200 5 3).ev = [Slice.Rv.retEv (W64.ofNat 8)]"),
 ("scan's cost is misstated", IMG, "(go scanImage env0 200 5 3).cost = 90", "(go scanImage env0 200 5 3).cost = 91"),
 ("spin is said to finish", IMG, "(go spinImage env0 40 5 1).out = .fuel", "(go spinImage env0 40 5 1).out = .done"),
 ("leakage coded without PCs again", IMG, "  | .step [p] => 2 * p\n", "  | .step [_] => 0\n"),
 ("a secret-index leak claimed for equal secrets", TTH, "exact leak_by_lk (n := 8) (a := 1) (a' := 2) (b := 1)", "exact leak_by_lk (n := 8) (a := 1) (a' := 1) (b := 1)"),
 ("the second iteration's branch looked for too early", TTH, "exact leak_by_lk (n := 22) (a := 0) (a' := 5) (b := 1)", "exact leak_by_lk (n := 21) (a := 0) (a' := 5) (b := 1)"),
 ("one byte of a refused literal is wrong", TTH, "[183, 3, 2, 0, 3, 180, 3, 0, 99, 12, 4, 0,", "[183, 3, 2, 0, 3, 180, 3, 0, 99, 13, 4, 0,"),
 ("the secret loop is said to finish at high fuel", TTH, "(encBytes (inp (2 ^ 63) 1), env0)).out = .fuel := by", "(encBytes (inp (2 ^ 63) 1), env0)).out = .done := by"),
 ("forN forgets to count down", FOR, "  .seq (.assign c e) (.loop (.var c) (.seq b (.assign c (.add (.var c) minusOne))))", "  .seq (.assign c e) (.loop (.var c) (.seq b (.assign c (.add (.var c) (num 0)))))"),
 ("forMax runs the body every round", FOR, "(.ite (.var d) (.seq b (.assign d (.add (.var d) minusOne))) .skip)", "(.ite (.var d) (.seq b (.assign d (.add (.var d) (num 0)))) .skip)"),
 ("forMax's rounds never end", FOR, ".skip) (.assign c (.add (.var c) minusOne)))))", ".skip) (.assign c (.add (.var c) (num 0))))))"),
 ("forMax caps at one more", FOR, "(src capped 100 5 10).ev.map Teeth.evCode = [5]", "(src capped 100 5 10).ev.map Teeth.evCode = [6]"),
 ("a loop round is charged one less", BUD, "(s c).val * (costOf B + 2) + 1 + pot cs k s", "(s c).val * (costOf B + 1) + 1 + pot cs k s"),
 ("setting a counter is not followed", BUD, "1 + pot cs k (if cs.contains x then upd s x (eval e s) else s)", "1 + pot cs k s"),
 ("a counted loop's body need not be plain", BUD, "c' == c && cs.contains c && isDec c d && plainC cs S B", "c' == c && cs.contains c && isDec c d"),
 ("a counter may be an input", BUD, "topC (counters p.body) p.inputs p.body && (counters p.body).all (fun c => !p.inputs.contains c)", "topC (counters p.body) p.inputs p.body"),
 ("a decrement by two counts as one", BUD, "  | .add (.var y) (.lit w) => y == c && w.val == 2 ^ 64 - 1", "  | .add (.var y) (.lit w) => y == c && decide (2 ^ 64 - 2 ≤ w.val)"),
 ("countUp's budget is said to be one less", BUD, "budget countUp (inp 5 3) = 14 ∧", "budget countUp (inp 5 3) = 13 ∧"),
 ("the bytes' budget formula is one less per round", BYT, "≤ 26 * (4 * (wordAt u.1 1).val + 2) + 26 := by", "≤ 26 * (3 * (wordAt u.1 1).val + 2) + 26 := by"),
 ("the source budget is said to be 4n + 1", BYT, "budget countUp i = 4 * (i 1).val + 2 := by", "budget countUp i = 4 * (i 1).val + 1 := by"),
 ("the capped budget on the bytes is one less", BYT, "theorem capped_bound_bytes : Cert.bound (rvLang sec0) 672 cappedImage := by", "theorem capped_bound_bytes : Cert.bound (rvLang sec0) 671 cappedImage := by"),
 ("one byte of countUp's literal is wrong", BYT, "[183, 3, 2, 0, 3, 180, 131, 0, 35, 176, 131, 64, 3, 180, 3, 64, 99, 4, 4, 4,", "[183, 3, 2, 0, 3, 180, 131, 0, 35, 176, 131, 64, 3, 180, 3, 64, 99, 4, 4, 5,"),
]


def group_rss_kb(pgid):
    r = subprocess.run(['ps', '-o', 'rss=', '-g', str(pgid)], capture_output=True, text=True)
    return sum(int(x) for x in r.stdout.split())


def build():
    """A resident-memory watchdog, not RLIMIT_AS: an address-space cap stops Lean creating threads, and every build then
    aborts with code 134 before checking a proof. That made the first run of this harness report 19 of 19 killed."""
    with tempfile.TemporaryFile('w+') as log:
        p = subprocess.Popen(['lake', 'build', 'LCore.Slice2.BoundBytes'], cwd=WORK, stdout=log, stderr=subprocess.STDOUT,
                             text=True, start_new_session=True)
        t0 = time.time()
        while p.poll() is None:
            time.sleep(2)
            if time.time() - t0 > TIMEOUT or group_rss_kb(p.pid) > CAP_KB:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                return None, ''
        log.seek(0)
        return p.returncode, log.read()


if os.path.exists(WORK):
    shutil.rmtree(WORK)
shutil.copytree('l-core', WORK, symlinks=True)

# The baseline must really compile, under the same limits: with everything already built, a build that cannot start a compiler would pass here.
base = os.path.join(WORK, OLD)
src = open(base).read()
open(base, 'w').write(src + '\n-- force a rebuild\n')
rc, out = build()
open(base, 'w').write(src)
if rc != 0:
    print('the unmutated copy does not build:', rc, out[-800:])
    sys.exit(2)
print('baseline really compiled', flush=True)
ERR = re.compile(r'^error: \S+\.lean:\d+')

bad = 0
for name, fn, old, new in M:
    path = os.path.join(WORK, fn)
    src = open(path).read()
    assert src.count(old) == 1, name
    open(path, 'w').write(src.replace(old, new))
    rc, out = build()
    open(path, 'w').write(src)
    errs = [l for l in out.splitlines() if ERR.match(l)]
    if rc == 0:
        print('SURVIVED  ', name, flush=True)
        bad += 1
    elif errs:
        print('killed    ', name, '|', len(errs), 'errors |', errs[0][7:90], flush=True)
    else:
        # No Lean error is not a kill: timeout, memory, or a build that never reached a proof.
        print('NO VERDICT', name, '| rc', rc, flush=True)
        bad += 1
print('not killed:', bad, 'of', len(M))
sys.exit(1 if bad else 0)
