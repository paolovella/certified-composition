#!/usr/bin/env python3
"""CC-01's check that the rewrite changed no verdict: the old and new check-claims, on the same export, print the same lines.

Each case copies the working tree (tracked and untracked, not ignored) into a temporary directory, applies one mutation, and runs both scripts
there. The cases reach every rewritten rule, both ways, and the clean tree is the first.

Usage, from the repo root: python3 research/2026-11/cc01_equiv.py <old check-claims.sh>
"""
import os, shutil, subprocess, sys, tempfile

OLD = os.path.abspath(sys.argv[1])
CASES = [
    ("the clean tree", "true"),
    ("a declaration outside the namespace", "printf '\\ntheorem zz_outside : True := trivial\\n' >> conf-typing/ConfTyping/Race.lean"),
    ("a duplicate top-level name", "printf '\\nnamespace ConfTyping\\ntheorem medCheck_sound : True := trivial\\nend ConfTyping\\n' >> conf-typing/ConfTyping/Race.lean"),
    ("the same name, nested in another namespace", "printf '\\nnamespace ConfTyping\\nnamespace Inner\\ntheorem medCheck_sound : True := trivial\\nend Inner\\nend ConfTyping\\n' >> conf-typing/ConfTyping/Race.lean"),
    ("a backlog item loses acceptance", "sed -i '/^acceptance: /d' backlog/P0-01.md"),
    ("a backlog item loses two fields", "sed -i '/^kill: /d; /^tier: /d' backlog/P0-01.md"),
    ("a backlog item loses its status", "sed -i '/^status: /d' backlog/P0-01.md"),
    ("a backlog item gets an unknown status", "sed -i 's/^status: .*/status: someday/' backlog/P0-01.md"),
    ("a key only mid-line", "sed -i 's/^kill: /x kill: /' backlog/P0-01.md"),
    ("a cited theorem renamed", "sed -i 's/theorem medCheck_sound/theorem gone_away/' conf-typing/ConfTyping/Mediation.lean"),
    ("a cited name only in a comment", "sed -i 's/theorem medCheck_sound/theorem gone_away/' conf-typing/ConfTyping/Mediation.lean && printf '\\n-- medCheck_sound\\n' >> conf-typing/ConfTyping/Race.lean"),
    ("1c: a cited name renamed away everywhere", "grep -rl loopFix_terminates conf-typing/ConfTyping transport-calculus | xargs sed -i 's/loopFix_terminates/loopFix_gone/g'"),
    ("1c: a cited name left only in a comment", "grep -rl loopFix_terminates conf-typing/ConfTyping transport-calculus | xargs sed -i 's/loopFix_terminates/loopFix_gone/g' && printf '\\n-- loopFix_terminates\\n' >> conf-typing/ConfTyping/Race.lean"),
    ("1c: a cited name only in a non-Lean file there", "grep -rl loopFix_terminates conf-typing/ConfTyping transport-calculus | xargs sed -i 's/loopFix_terminates/loopFix_gone/g' && printf 'loopFix_terminates\\n' > conf-typing/ConfTyping/notes.txt"),
    ("a cited module not imported", "sed -i '/^import ConfTyping.Race$/d' conf-typing/ConfTyping.lean"),
    ("a cited module imported under a longer name", "sed -i 's/^import ConfTyping.Race$/import ConfTyping.RaceX/' conf-typing/ConfTyping.lean"),
    ("a VULN-COVERAGE citation of a module removed", "sed -i 's/Race\\.lean/Rxce_lean/g' VULN-COVERAGE.md && sed -i '/^import ConfTyping.Race$/d' conf-typing/ConfTyping.lean"),
]


def export(dst):
    files = subprocess.run(['git', 'ls-files', '-co', '--exclude-standard', '-z'], capture_output=True).stdout.split(b'\0')
    for f in (x.decode() for x in files if x):
        if not os.path.isfile(f):
            continue
        os.makedirs(os.path.join(dst, os.path.dirname(f)), exist_ok=True)
        shutil.copy2(f, os.path.join(dst, f))


bad = 0
for name, mutation in CASES:
    with tempfile.TemporaryDirectory() as d:
        export(d)
        if subprocess.run(['bash', '-c', mutation], cwd=d).returncode != 0:
            print('FAIL  ', name, '| the mutation did not apply')
            bad += 1
            continue
        shutil.copy2(OLD, os.path.join(d, 'tools', 'check-claims.old.sh'))
        old = subprocess.run(['bash', 'tools/check-claims.old.sh'], cwd=d, capture_output=True, text=True)
        new = subprocess.run(['bash', 'tools/check-claims.sh'], cwd=d, capture_output=True, text=True)
    drift = [l for l in new.stdout.splitlines() if l.startswith('DRIFT')]
    if old.stdout == new.stdout and old.returncode == new.returncode:
        print('same  ', name, '|', len(drift), 'drift lines', '|', (drift[0][:90] if drift else 'clean'))
    else:
        print('DIFFER', name)
        for l in sorted(set(old.stdout.splitlines()) ^ set(new.stdout.splitlines())):
            print('       ', ('old ' if l in old.stdout.splitlines() else 'new ') + l[:150])
        bad += 1
print('differences:', bad, 'of', len(CASES))
sys.exit(1 if bad else 0)
