---
id: S-OBS
title: Spike: JSecTy NI proof with addresses moved into the leakage
ring: 1
tier: G-X
deps: []
closes: ['state to observation move']
acceptance: proof goes through or fallback chosen
kill: public-only allocator as edition-1 removal
status: done
---

## Plan

PLAN-2026-10 §5: the one-time move from state to observation. `Beh` observes events,
leakage (branches and **addresses**), cost and outcome, not internal state. Today's
noninterference relation `uLowEqA` (`HeapJoint.lean`) equates `fresh`, `freed` and `hlab`
across the two runs. The riskiest certificate to re-state is `JSecTy`'s: is noninterference
still true once the attacker also sees the address of every memory operation?

**The conjecture.** A variable enters the tracked set `V` only by `alloc`/`allocS`. It leaves
`V` on reassignment (`assign*`), on being loaded over (`load*`), and on `free`. Allocation is
synchronised between two Low-equal runs (`fresh`, `freed` equal, Low guards only). So two runs
agree on every tracked pointer's value, `AddrEq V s s' := ∀ x ∈ V, s.store x = s'.store x`, and
every memory operation `JSecTy` allows (`deref`, `free`, `load`, `store` all require their
pointer in `V`) touches the same address in both runs.

1. Define `AddrEq` and prove it is preserved: if `JSecTy P V c V'` holds, the usual invariants
   (`SepInv`, `LabInv`, `uLowEqA`) hold for `s` and `s'`, and `AddrEq V s s'`, then the two
   runs of `c` both diverge or both end in states with `AddrEq V'`. By induction on fuel,
   using `jsecTy_sound` for the Low-equality of intermediate states.
2. The per-operation corollary: at every `deref x`, `free x`, `load d p`, `store p v` with the
   pointer in `V`, the addresses are equal.
3. If 1 and 2 hold, define an address trace (`uaddrs`, the addresses `uexec` touches) and prove
   it equal across the runs. That is addresses-in-leakage noninterference for `JSecTy`.
4. **Kill rule:** if `AddrEq` fails, keep its counterexample as a Lean witness. The fallback is
   then PLAN-2026-10's public-only allocator (no reuse of cells allocated under secret
   control), as an edition-1 removal.

Module: `conf-typing/ConfTyping/AddrLeak.lean`, additive, with no change to any existing
definition or statement.

## Log
- 2026-10-28, branch `s-obs/addr-eq`. **The proof goes through; no fallback.**
  - `AddrEq V s s'`: two live runs agree on every tracked pointer. `jsecTy_addrEq`: preserved
    by every `JSecTy` rule, by induction on fuel next to `jsecTy_sound`. Allocation is the only
    case with content, since the synchronised allocator gives both runs the same address.
  - `uaddrs` is the address trace: allocation addresses and the pointer of every
    `deref`/`free`/`load`/`store`. `jsecTy_addrs`: equal across Low-equal runs.
    `jsecTy_addrs_initU`: the same from two Low-equal initial stores.
  - Witnesses:
    - accepted: `secretCellProg` (allocate, store into and free a secret cell), with trace
      `[0, 0, 0]` for either secret;
    - refused: `secretAddrProg` (a pointer taken from the secret), with traces `[5]` and
      `[7]`, so the trace can see a secret, and the type system is what keeps it equal.
  - Footprint: the standard three, inherited from `jsecTy_sound`. Additive: no existing
    definition or statement changed; `ring0.lock`, `checkers.lock` and the mutant sites are
    unchanged.
  - For PH1: addresses can move into `Beh`'s leakage `Lk` for `JSecTy` as they are. The other
    certificates still need their own re-statement; this was the one the plan flagged as
    riskiest.
