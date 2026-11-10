---
id: ENG-01
title: "The tier classifier: the gate assigns each PR its tier from its paths and a type manifest, and a PR cannot name its own tier"
ring: 0
tier: G-0
milestone: M2 (2026-12-18)
deps: [P0-06]
closes: ['PLAN-2026-10 §7: the tier classifier does not exist; the base gate knows Ring 0 and nothing else']
acceptance: tools/gate/ computes the tier of a PR from BASE's rules; a type manifest hashes each declaration's elaborated type, and proof-only means no existing hash changed; witnesses, each run by the gate's witness script - a corpus-only PR is G-P, a new checker is G-X, a PR that changes one statement's type and calls itself proof-only is refused, a PR that touches tools/ is G-0; the highest tier among a PR's files is the PR's tier
kill: if the type manifest costs more than 5 minutes on the fast runner, it runs on the heavy runner and a PR waits for it; that is recorded and is not a reason to skip it
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2026-11-16 to 2026-11-27. Every file here is Ring 0. The agent proposes on a branch, and the user merges.

1. **Path rules**, in a table the gate reads from BASE: Ring 0 paths as `CLAUDE.md` lists them; `l-core/LCore/Slice*/` and `conf-typing/ConfTyping/` checkers are G-X; corpus directories are G-P; prose is G-D.
2. **The type manifest.** `research/2026-11/decl_fingerprint.py` already prints a fingerprint per declaration. The manifest is its output for BASE and for the PR. A changed or removed line outside proofs raises the tier.
3. **The classifier's output** is a line in the gate's report and a required check. `tier:` in a backlog item is a statement of intent, and the gate does not read it.
4. Witnesses under `tools/gate/witness/`, as `base-gate-witness.sh` does.

## Log
