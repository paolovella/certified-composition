---
id: EXPR-02
title: "Nested counted loops: bcheck checks a loop body with bcheck, fuel-indexed so decide still reduces"
ring: 1
tier: G-X
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: corpus program 24 and blind programs 11 and 20 are accepted; bcheck_sound still proved and Frozen.bcheck_sound unchanged; every existing witness still decides
kill: -
status: planned
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
