#!/usr/bin/env python3
"""VS-2 steps 6, 7 and 9, and BOUND-01 steps 2 to 5a, and RC-01 steps 2b and 3: hand-written mutants of the second slice's lowering, since tools/mutants.py does not scan l-core.

Each mutant must fail to build as far as the machine witnesses. It runs on a copy of the package, never on the working
tree, with each build in its own process group, killed as a group on timeout or above 12 GB resident. A kill counts only with a Lean error at a line of a `.lean` file.

Usage, from the repo root: python3 research/2026-11/slice2_low_mut.py <scratch directory>
"""
import os, re, shutil, signal, subprocess, sys, tempfile, time

WORK = os.path.join(sys.argv[1], 'l-core')
LOW, CHK, PAS, OLD, IMG, TTH, FOR, BUD, BYT, OPS, WRD, SRC, RVM, S2S, BTS = ('LCore/Slice2/Lower.lean', 'LCore/Slice2/Chunk.lean', 'LCore/Slice2/Pass.lean', 'LCore/Slice/Lower.lean', 'LCore/Slice2/Image.lean', 'LCore/Slice2/Teeth.lean', 'LCore/Slice2/For.lean', 'LCore/Slice2/Budget.lean', 'LCore/Slice2/BoundBytes.lean', 'LCore/Slice2/Ops.lean', 'LCore/Slice/Word.lean', 'LCore/Slice/Source.lean', 'LCore/Slice/Rv.lean', 'LCore/Slice2/Source.lean', 'LCore/Slice2/Bytes.lean')
CAP_KB = 12 * 2 ** 20
TIMEOUT = 1500

M = [
 # CAP-01 part 3: literals past 12 bits
 ("a literal's split is not checked", OLD, "  else if pairVal (pairOf (sint w)).1 (pairOf (sint w)).2 = w then some", "  else if true then some"),
 ("the addi of a pair reads x0", OLD, "  | some (.two hi lo) => [.lui r hi, .addi r r lo]", "  | some (.two hi lo) => [.lui r hi, .addi r 0 lo]"),
 ("the srli of a shifted literal is one short", OLD, "  | some (.three hi lo k) => [.lui r hi, .addi r r lo, .srli r r k]", "  | some (.three hi lo k) => [.lui r hi, .addi r r lo, .srli r r (k - 1)]"),
 # CAP-01: the caps lifted, each at its new edge (Slice2/Caps.lean)
 ("fits allows one more local", 'LCore/Slice2/Slots.lean', "decide (128 + (uniq (allVars p)).length ≤ 256)", "decide (128 + (uniq (allVars p)).length ≤ 257)"),
 ("uniq keeps duplicates", 'LCore/Slice2/Slots.lean', "  | x :: xs => x :: (uniq xs).filter (· ≠ x)", "  | x :: xs => x :: uniq xs"),
 ("the image may be four bytes longer", 'LCore/Slice2/Pass.lean', "okC p.body && okE p.ret 0 && decide (4 * (genP p).length ≤ 65360)", "okC p.body && okE p.ret 0 && decide (4 * (genP p).length ≤ 65364)"),
 # RC-02 step 6: the budget's inputs, and byte stores
 ("a counter may be set from a written input", BUD, "def readIn (p : Prog) : List String := p.inputs.filter fun x => !(writtenB p.body).contains x",
  "def readIn (p : Prog) : List String := p.inputs"),
 ("a byte store writes nothing, for the budget", BUD, "  | .storeB ns _ _ => ns\n  | .seq a b | .ite _ a b => assigns a ++ assigns b",
  "  | .storeB _ _ _ => []\n  | .seq a b | .ite _ a b => assigns a ++ assigns b"),
 # RC-02 step 3: byte stores and outputs, through the lowering
 ("storeB writes the next byte", LOW, ".sb 9 8 (Int.ofNat (8 * ws.headD 0))]", ".sb 9 8 (Int.ofNat (8 * ws.headD 0 + 1))]"),
 ("storeB stores the address, not the value", LOW, ".sb 9 8 (Int.ofNat (8 * ws.headD 0))]", ".sb 8 8 (Int.ofNat (8 * ws.headD 0))]"),
 ("emitB writes one word short", LOW, ".addi 12 0 (Int.ofNat (8 * ws.length))", ".addi 12 0 (Int.ofNat (8 * ws.length - 8))"),
 ("emitB writes from the next word", LOW, ".addi 11 7 (Int.ofNat (8 * ws.headD 0))", ".addi 11 7 (Int.ofNat (8 * ws.headD 0 + 8))"),
 ("emitB writes to stderr", LOW, "[.addi 10 0 (Int.ofNat 1), .addi 11 7", "[.addi 10 0 (Int.ofNat 2), .addi 11 7"),
 ("an output's addresses do not show", CHK, "(pc + 16, (List.range (8 * ws.length)).map fun i => .addr (Int.ofNat (dataBase + 8 * ws.headD 0 + i)))]", "(pc + 16, [])]"),
 ("an output emits nothing on the machine", CHK, "| .emitB ws => [.emit \"out\" (Slots.outBytesS t ws)]", "| .emitB ws => []"),
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
 ("the budget loses its constant", PAS, "cost c := stepL p * c + tailC p", "cost c := stepL p * c"),
 ("the budget does not grow with the source", PAS, "cost c := stepL p * c + tailC p", "cost _ := stepL p + tailC p"),
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
 ("a counter may be an input", BUD, "topC (counters p.body) (readIn p) p.body && (counters p.body).all (fun c => !p.inputs.contains c)", "topC (counters p.body) (readIn p) p.body"),
 ("a decrement by two counts as one", BUD, "  | .add (.var y) (.lit w) => y == c && w.val == 2 ^ 64 - 1", "  | .add (.var y) (.lit w) => y == c && decide (2 ^ 64 - 2 ≤ w.val)"),
 ("countUp's budget is said to be one less", BUD, "budget countUp (inp 5 3) = 14 ∧", "budget countUp (inp 5 3) = 13 ∧"),
 ("the bytes' budget formula is one less per round", BYT, "≤ 8 * (4 * (wordAt u.1 1).val + 2) + 5 := by", "≤ 8 * (3 * (wordAt u.1 1).val + 2) + 5 := by"),
 ("the source budget is said to be 4n + 1", BYT, "budget countUp i = 4 * (i 1).val + 2 := by", "budget countUp i = 4 * (i 1).val + 1 := by"),
 ("the capped budget on the bytes is one less", BYT, "theorem capped_bound_bytes : Cert.bound (rvLang sec0) 97 cappedImage := by", "theorem capped_bound_bytes : Cert.bound (rvLang sec0) 96 cappedImage := by"),
 ("a loop step is charged one less", PAS, "  | .ite e _ _ | .loop e _ => sE e + 2\n", "  | .ite e _ _ | .loop e _ => sE e + 1\n"),
 ("stepMax forgets a loop's body", PAS, "  | .loop e b => max (sE e + 2) (stepMax b)\n", "  | .loop e b => sE e + 2\n"),
 ("one byte of countUp's literal is wrong", BYT, "[183, 3, 2, 0, 3, 180, 131, 0, 35, 176, 131, 64, 3, 180, 3, 64, 99, 4, 4, 4,", "[183, 3, 2, 0, 3, 180, 131, 0, 35, 176, 131, 64, 3, 180, 3, 64, 99, 4, 4, 5,"),
 ("xor means or", WRD, "  | .xor => W64.xor\n", "  | .xor => W64.or\n"),
 ("a shift moves one place too far", WRD, "def shr (a : W64) (k : Nat) : W64 := ofNat (a.val >>> k)", "def shr (a : W64) (k : Nat) : W64 := ofNat (a.val >>> (k + 1))"),
 ("the taint rule ignores an operator's first operand", SRC, "  | .add a b | .bin _ a b => highE H a || highE H b\n", "  | .add a b => highE H a || highE H b\n  | .bin _ _ b => highE H b\n"),
 ("the lowering emits add for every operator", OLD, "[opInsn o (8 + d) (8 + d) (8 + d + 1)]", "[.add (8 + d) (8 + d) (8 + d + 1)]"),
 ("a shift by 64 is accepted", OLD, "  | .shr a k, d => okE a d && decide (k < 64)\n", "  | .shr a k, d => okE a d && decide (k < 65)\n"),
 ("sub is emitted as xor", RVM, "  | .sub, rd, a, b => .sub rd a b\n", "  | .sub, rd, a, b => .xor rd a b\n"),
 ("a byte read big-endian", S2S, "  | some y => byteOfWord (s y) (i % 8)\n", "  | some y => byteOfWord (s y) (7 - i % 8)\n"),
 ("a secret array's byte counts as public", S2S, "    else if ns.any (fun y => decide (y ∈ st.1)) then some (x :: st.1, st.2)", "    else if false then some (x :: st.1, st.2)"),
 ("the source's mask is one byte too wide", S2S, "def bidx (ns : List String) (v : W64) : Nat := v.val % (8 * ns.length)", "def bidx (ns : List String) (v : W64) : Nat := v.val % (8 * ns.length + 1)"),
 ("lbu reads one byte along", LOW, ".lbu 8 8 (Int.ofNat (8 * ws.headD 0)), .sd 8 7 (Int.ofNat (8 * x))]", ".lbu 8 8 (Int.ofNat (8 * ws.headD 0 + 1)), .sd 8 7 (Int.ofNat (8 * x))]"),
 ("an array's words need not be in order", LOW, "decide (x < wordsMax) && okE e 0 && decide (ws = List.range' (ws.headD 0) ws.length) && maskOK ws.length &&", "decide (x < wordsMax) && okE e 0 && maskOK ws.length &&"),
 ("a byte read leaks nothing in the slots", PAS, "  | .loadB _ ws e => [addrLk (Slots.bidxS ws (evalS e t))]\n", "  | .loadB _ ws e => []\n"),
 ("crypto_verify_16 is said to report equal arrays as different", BTS, "(src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234)).ev.map Teeth.evCode = [1] ∧", "(src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234)).ev.map Teeth.evCode = [2 ^ 64] ∧"),
]


def group_rss_kb(pgid):
    r = subprocess.run(['ps', '-o', 'rss=', '-g', str(pgid)], capture_output=True, text=True)
    return sum(int(x) for x in r.stdout.split())


def build():
    """A resident-memory watchdog, not RLIMIT_AS: an address-space cap stops Lean creating threads, and every build then
    aborts with code 134 before checking a proof. That made the first run of this harness report 19 of 19 killed."""
    with tempfile.TemporaryFile('w+') as log:
        p = subprocess.Popen(['lake', 'build', 'LCore.Slice2.Bytes', 'LCore.Slice2.Caps'], cwd=WORK, stdout=log, stderr=subprocess.STDOUT,
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

ONLY = os.environ.get('ONLY')
if ONLY:
    M = [m for m in M if m[0] in ONLY.split('|')]
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
