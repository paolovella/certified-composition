#!/usr/bin/env python3
"""BOUND-01 step 1: hand-written mutants of the seventh shape, since tools/mutants.py does not scan l-core.

Each mutant must fail to build `LCore.Witnesses`. It runs on a copy of the package, never on the working tree, each build in its own process
group, killed as a group on timeout or above 12 GB resident. A kill counts only with a Lean error at a line of a `.lean` file.

Usage, from the repo root: python3 research/2026-11/boundr_mut.py <scratch directory>
"""
import os, re, shutil, signal, subprocess, sys, tempfile, time

WORK = os.path.join(sys.argv[1], 'l-core')
CERT, PASS = 'LCore/Kernel/Cert.lean', 'LCore/Kernel/Pass.lean'
CAP_KB = 12 * 2 ** 20
TIMEOUT = 1500
ERR = re.compile(r'^error: \S+\.lean:\d+')

M = [
 ("the budget is chosen after the fuel", CERT,
  "  ∀ (i : L.In), L.Adm i → ∃ k, R i k ∧ ∀ (n : Nat), (L.run n p i).cost ≤ k\n",
  "  ∀ (i : L.In), L.Adm i → ∀ (n : Nat), ∃ k, R i k ∧ (L.run n p i).cost ≤ k\n"),
 ("the budget ignores the relation", CERT,
  "  ∀ (i : L.In), L.Adm i → ∃ k, R i k ∧ ∀ (n : Nat), (L.run n p i).cost ≤ k\n",
  "  ∀ (i : L.In), L.Adm i → ∃ k, True ∧ ∀ (n : Nat), (L.run n p i).cost ≤ k\n"),
 ("the lifted budget drops the cost transformer", PASS,
  "  fun u k => ∃ i k', S.Adm i ∧ pc.enc i = u ∧ R i k' ∧ k = t.cost k'\n",
  "  fun u k => ∃ i k', S.Adm i ∧ pc.enc i = u ∧ R i k' ∧ k = k'\n"),
 ("the lifted budget forgets which input it came from", PASS,
  "  fun u k => ∃ i k', S.Adm i ∧ pc.enc i = u ∧ R i k' ∧ k = t.cost k'\n",
  "  fun _ k => ∃ i k', S.Adm i ∧ pc.enc i = pc.enc i ∧ R i k' ∧ k = t.cost k'\n"),
 ("unbounded cost is said to have a budget", CERT,
  "    (hgrow : ∀ k, ∃ n, k < (L.run n p i).cost) : ¬ boundR L R p := by",
  "    (hgrow : ∀ k, ∃ n, k ≤ (L.run n p i).cost) : ¬ boundR L R p := by"),
]


def rss(pgid):
    r = subprocess.run(['ps', '-o', 'rss=', '-g', str(pgid)], capture_output=True, text=True)
    return sum(int(x) for x in r.stdout.split())


def build():
    with tempfile.TemporaryFile('w+') as log:
        p = subprocess.Popen(['lake', 'build', 'LCore.Witnesses'], cwd=WORK, stdout=log, stderr=subprocess.STDOUT, text=True,
                             start_new_session=True)
        t0 = time.time()
        while p.poll() is None:
            time.sleep(2)
            if time.time() - t0 > TIMEOUT or rss(p.pid) > CAP_KB:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                return None, ''
        log.seek(0)
        return p.returncode, log.read()


if os.path.exists(WORK):
    shutil.rmtree(WORK)
shutil.copytree('l-core', WORK, symlinks=True)
base = os.path.join(WORK, CERT)
src = open(base).read()
open(base, 'w').write(src + '\n-- force a rebuild\n')
rc, out = build()
open(base, 'w').write(src)
if rc != 0:
    print('the unmutated copy does not build:', rc, out[-800:])
    sys.exit(2)
print('baseline really compiled', flush=True)

bad = 0
for name, fn, old, new in M:
    path = os.path.join(WORK, fn)
    s = open(path).read()
    assert s.count(old) == 1, name
    open(path, 'w').write(s.replace(old, new))
    rc, out = build()
    open(path, 'w').write(s)
    errs = [l for l in out.splitlines() if ERR.match(l)]
    if rc == 0:
        print('SURVIVED  ', name, flush=True)
        bad += 1
    elif errs:
        print('killed    ', name, '|', len(errs), 'errors |', errs[0][7:90], flush=True)
    else:
        print('NO VERDICT', name, '| rc', rc, flush=True)
        bad += 1
print('not killed:', bad, 'of', len(M))
sys.exit(1 if bad else 0)
