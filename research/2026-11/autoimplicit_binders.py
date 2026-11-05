#!/usr/bin/env python3
"""AI-01 step 2: make auto-bound names explicit, in the order Lean bound them: first occurrence in the declaration.

For each `Unknown identifier` that Lean reports with autoImplicit off inside an inductive constructor, add `{names}` straight
after the constructor's name, since auto-bound names come before every written binder. Only constructors: an unknown name
in a proof is a knock-on from a failed statement (a first version also bound theorems' own names when they recurse). Errors
anywhere else are reported as STUCK, for a person. Repeats until the file has no error or stops changing. Prints what it added, so the names can be read for typos. This
tool's output is believed only because decl_fingerprint.py finds every declaration's type unchanged.

Usage, from the repo root: python3 research/2026-11/autoimplicit_binders.py <package> <file>...
"""
import re, subprocess, sys

pkg = sys.argv[1]
ERR = re.compile(r'^\S+\.lean:(\d+):(\d+): error(?:\([^)]*\))?: (.*)')
UNK = re.compile(r'Unknown identifier `([^`]+)`')
TOP = re.compile(r'^((?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |partial |unsafe )*)(theorem|lemma|def|abbrev|instance|inductive|structure|class|example)\b(\s+)?([^\s:({\[]+)?')
CTOR = re.compile(r'^(\s*\|\s*)([^\s:({\[]+)')


def errors(f):
    r = subprocess.run(['lake', 'env', 'lean', '-D', 'autoImplicit=false', f], cwd=pkg, capture_output=True, text=True)
    out = []
    for l in r.stdout.splitlines():
        m = ERR.match(l)
        if m:
            out.append((int(m[1]), int(m[2]), m[3]))
    return out


def target(lines, i):
    """The constructor line for an error at index i and the column just after its name, or None if it is not in a constructor."""
    top = i
    while top >= 0 and not TOP.match(lines[top]):
        top -= 1
    if top < 0:
        raise SystemExit(f'no declaration above line {i + 1}')
    m = TOP.match(lines[top])
    if m[2] == 'inductive':
        j = i
        while j > top:
            c = CTOR.match(lines[j])
            if c:
                return j, c.end(2)
            j -= 1
    return None


for f in sys.argv[2:]:
    for rnd in range(6):
        errs = errors(f)
        if not errs:
            print(f'{f}: clean after {rnd} rounds')
            break
        lines = open(f'{pkg}/{f}').read().split('\n')
        add = {}
        for ln, col, msg in sorted(errs):
            u = UNK.search(msg)
            if not u or '.' in u[1]:
                continue
            site = target(lines, ln - 1)
            if site is None:
                continue
            add.setdefault(site, [])
            if u[1] not in add[site]:
                add[site].append(u[1])
        if not add:
            print(f'{f}: STUCK with {len(errs)} errors, first: line {errs[0][0]}: {errs[0][2][:100]}')
            break
        for (ln, col), names in sorted(add.items(), reverse=True):
            l = lines[ln]
            lines[ln] = l[:col] + ' {' + ' '.join(names) + '}' + l[col:]
            print(f'{f}:{ln + 1}: {{{" ".join(names)}}}')
        open(f'{pkg}/{f}', 'w').write('\n'.join(lines))
    else:
        print(f'{f}: STUCK after 6 rounds')
