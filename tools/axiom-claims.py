#!/usr/bin/env python3
"""Resolve every "axiom-free / choice-free / propext-only" claim in the docs against the axiom
manifest (tools/axioms.expected), and fail on any claim the manifest contradicts.

Why: these claims were each checked once, by hand, when written. The manifest is regenerated
by CI, so a proof that later picks up Classical.choice through a lemma it calls now makes the
sentence that calls it choice-free fail the build, instead of standing forever.

Binding rules (deliberately narrow, so a claim is never attached to the wrong name):
  * table row: a cell containing a footprint keyword binds every backticked name in the cell
    immediately before it;
  * prose: a keyword binds the nearest backticked name before it on the same line, provided
    the text between them is short (at most 48 characters) and contains no other keyword.
Meanings: axiom-free = no axioms; propext-only = a subset of {propext}; choice-free = no
Classical.choice.
Doc names are unqualified; a name matching several manifest theorems resolves only if every
match satisfies the claim (then ok) or every match violates it (then a contradiction).

usage: tools/axiom-claims.py [--verbose]     (run from the repo root)
exit 1 iff some claim is contradicted by the manifest.
"""
import re
import glob
import sys

MANIFEST = "tools/axioms.expected"
# Docs that make claims about this repo's theorems. Research notes, plans of record that only
# talk about the claim mechanism, and backlog items are not claims about specific theorems.
DOC_GLOBS = ["README.md", "VULN-COVERAGE.md", "CHANGELOG.md", "PLAN-2026-08.md",
             "PLAN-MULTITOOL.md", "conf-typing/*.md", "transport-calculus/*.md"]
KEYWORDS = ("axiom-free", "choice-free", "propext-only")
IDENT = r"[A-Za-z_][A-Za-z0-9_'.₀-₉!?]*"
TICK = re.compile(r"`(" + IDENT + r")`")
# `ConfTyping/X.lean` or `conf-typing/ConfTyping/X.lean`: a claim about every declaration in X
MODTICK = re.compile(r"`(?:[a-z-]+/)?([A-Z][A-Za-z0-9]*(?:/[A-Za-z0-9]+)+)\.lean`")


def satisfies(claim, axioms):
    if claim == "axiom-free":
        return not axioms
    if claim == "propext-only":
        return axioms <= {"propext"}
    return "Classical.choice" not in axioms        # choice-free


by_module = {}


def load_manifest():
    by_short = {}
    with open(MANIFEST) as f:
        for line in f:
            name, mod, axs = line.rstrip("\n").split("\t")
            ax = set(a for a in axs.split(",") if a)
            parts = name.split(".")
            for i in range(len(parts)):          # every dotted suffix is a way docs cite it
                by_short.setdefault(".".join(parts[i:]), []).append((name, ax))
            by_module.setdefault(mod, []).append((name, ax))
    return by_short


STRUCK = re.compile(r"~~.*?~~")


def claims_in_line(line, prev=None):
    """Yield (name, claim) pairs bound by the rules above.

    Text in ~~strikethrough~~ is a *retracted* claim (a correction of record quoting what used
    to be said) and is removed before binding, so recording a correction never re-asserts it."""
    line = STRUCK.sub("", line)
    if prev is not None:
        prev = STRUCK.sub("", prev)
    if line.lstrip().startswith("|"):
        cells = line.strip().strip("|").split("|")
        for i, cell in enumerate(cells):
            kws = [k for k in KEYWORDS if k in cell]
            if not kws or i == 0:
                continue
            names = TICK.findall(cells[i - 1])
            parts = cell.split(" / ")
            if len(parts) > 1 and len(parts) == len(names):
                # "choice-free / standard 3" assigns footprints by position; a part with no
                # keyword ("standard 3", "classical") makes no claim about its name.
                for name, part in zip(names, parts):
                    pk = [k for k in KEYWORDS if k in part]
                    if pk:
                        yield name, pk[0]
            else:
                for name in names:
                    yield name, kws[0]
        return
    for m in re.finditer("|".join(KEYWORDS), line):
        before = line[:m.start()]
        ticks = sorted(list(TICK.finditer(before)) + list(MODTICK.finditer(before)),
                       key=lambda t: t.end())
        if not ticks:
            # a claim wrapped onto the next line: "... `name`\n  (axiom-free): ..."
            if before.strip() in ("", "(", "**", "(**") and prev is not None:
                pt = list(TICK.finditer(prev))
                if pt and len(prev.rstrip()) - pt[-1].end() <= 1:
                    yield pt[-1].group(1), m.group(0)
            continue
        last = ticks[-1]
        gap = before[last.end():]
        if len(gap) <= 48 and not any(k in gap for k in KEYWORDS):
            if last.re is MODTICK:
                yield "module:" + last.group(1).replace("/", "."), m.group(0)
            else:
                yield last.group(1), m.group(0)


def main():
    verbose = "--verbose" in sys.argv
    by_short = load_manifest()
    # plain globbing, not `git ls-files`: guard-selftest runs this in a non-git export
    files = sorted({f for g in DOC_GLOBS for f in glob.glob(g)})
    ok = unresolved = unbound = 0
    bad = []
    for path in files:
        with open(path, encoding="utf-8") as f:
            prev = None
            for lineno, line in enumerate(f, 1):
                bound = list(claims_in_line(line, prev))
                prev = line
                # Keyword occurrences no rule attached to a name: reported, never silently
                # dropped, so "N confirmed" cannot be read as "every claim confirmed".
                unbound += max(0, sum(STRUCK.sub("", line).count(k) for k in KEYWORDS) - len(bound))
                if verbose and sum(line.count(k) for k in KEYWORDS) > len(bound):
                    print(f"  unbound     {path}:{lineno}  {line.strip()[:100]}")
                for name, claim in bound:
                    if name.startswith("module:"):
                        matches = by_module.get(name[len("module:"):])
                    else:
                        matches = by_short.get(name)
                    if not matches:
                        unresolved += 1
                        if verbose:
                            print(f"  unresolved  {path}:{lineno}  `{name}` {claim}")
                        continue
                    verdicts = {satisfies(claim, ax) for _, ax in matches}
                    if name.startswith("module:") and False in verdicts:
                        # a module claim is about every declaration in it: one violation
                        # contradicts it (mixed verdicts are only ambiguous for a short name)
                        viol = [f"{n}: {','.join(sorted(ax)) or 'none'}" for n, ax in matches
                                if not satisfies(claim, ax)]
                        bad.append(f"{path}:{lineno}: `{name[7:]}` claimed {claim} as a module, "
                                   f"violated by {'; '.join(viol[:3])}")
                    elif verdicts == {True}:
                        ok += 1
                    elif verdicts == {False}:
                        actual = "; ".join(f"{n}: {','.join(sorted(ax)) or 'none'}"
                                           for n, ax in matches)
                        bad.append(f"{path}:{lineno}: `{name}` claimed {claim}, manifest says {actual}")
                    else:
                        unresolved += 1
                        if verbose:
                            print(f"  ambiguous   {path}:{lineno}  `{name}` {claim}")
    for b in bad:
        print("DRIFT: " + b)
    print(f"axiom-claims: {ok} confirmed, {len(bad)} contradicted, {unresolved} unresolved, "
          f"{unbound} keyword uses bound to no name")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
