---
id: EXPR-02
title: "Nested counted loops: bcheck checks a loop body with bcheck, fuel-indexed so decide still reduces"
ring: 1
tier: G-X
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: corpus program 24 and blind programs 11 and 20 are accepted; bcheck_sound still proved and Frozen.bcheck_sound unchanged; every existing witness still decides
kill: -
status: in-progress
---

## Plan

The counted-loop rule (`CountedLoop.lean`, `bcheck`) checks its body with `allcheck`, which
has no loop rule. Its docstring says "nesting is a follow-on, not a claim". The cost: one false
refusal in August's corpus (24) and two in the blind set (11, 20).

1. `bcheckF : Nat → ...`, with the counted-loop body checked by `bcheckF n` at fuel `n + 1`.
   `bcheck P A V c := bcheckF (usize c) P A V c`, where `usize` is a structural size,
   so the signature the frozen statement names does not change. No `termination_by`, which
   CLAUDE.md forbids in validators: the kernel must reduce it.
2. `bcheck_sound` re-proved by induction on fuel. The statement is frozen
   (`Frozen.bcheck_sound`), and the comparator checks it is unchanged.
3. This is a checker edit, so it is judged by P0-11: `tools/checkers.lock` changes for
   `bcheck` (and `allcheck` if touched), within the limit of 3, and the boundary warden reviews
   it (P0-12). It is the first real checker change to go through that path.
4. Witnesses: the nested-loop programs are accepted (`decide`). Accept witnesses for nested
   bodies go in `Witnesses.lean`. The nested double-free (`for { for { free p } }`) is refused.
   The mutant table is regenerated, and every mutant must be killed.
5. Re-run both corpora. The frozen ones are only reported, not tuned against.

## Log

- 2026-10-28, branch `expr-02/nested-loops`. Steps 1–5 as planned.
  - `bcheckF` (fuelled) and `usize` (structural), with `bcheck := bcheckF (usize c)`. No
    `termination_by`. `bcheckF_sound` proved by induction on fuel on the first build;
    `bcheck_sound` is a corollary with its statement unchanged.
  - Locks: `ring0.lock` unchanged, so the meaning did not move. In `checkers.lock` only `bcheck`
    changed (1 of the limit of 3).
  - Registry 37 → 38 checkers, since `bcheckF` is a checker and has its own pair; 0 missing.
    Manifest +7 lines, none removed.
  - Mutants 319/319 killed: `bcheck`'s five sites moved into `bcheckF`, plus the fuel-0 site.
  - Kernel witnesses: `bcheck_accepts_nested_loops` (budget 34),
    `bcheck_refuses_nested_double_free`, and `bcheckF`'s accept/refuse pair.
  - Effect (reported only):
    - August corpus 21/25 → **22/25**; 24 is accepted, and 09, 11 and 21 are still refused.
    - Blind set: 11 and 20 are accepted; all 8 unsafe programs are still refused. The
      remaining safe refusals are 09, 10 and 22 (EXPR-01's rule) and 18 (EXPR-03).
  - `tools/gate/base-gate-witness.sh` hard-coded "all 318 killed"; it now reads the count from
    the table.
  - Merge path: `tools/witnesses.expected` and `tools/gate/base-gate-witness.sh` are Ring 0,
    and only `checkers.lock` and `mutants.expected` are data, so this PR needs the user's key.
    The boundary warden reviews the `bcheck` change on GitHub; this is its first real case.
  - Full CI run 1 (`expr02-ci-full`) failed one step: the warden witness pinned "0 drifted" and "1 drifted", true only while the tree equals the baseline. With `bcheck` drifted, as it now is, both cases failed. It now checks this PR's own change (0, and `costCheck` marked "changed by this PR: yes") and leaves the drifted total, which depends on history, unpinned.
  - Full CI green (`expr02-ci-full2`, 897 s).
  - The boundary warden cleared PR #6 (run on GitHub, answer kept as the `warden` artifact). It noted one unchecked claim: the docstring said the fuel `usize c` "is always enough", and that is not proved. Reworded to what holds (sound at any fuel; enough only witnessed). Open: prove `usize c ≤ n → bcheckF P n A V c = bcheckF P (usize c) A V c`.
