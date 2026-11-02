/-
  A language, as the certificates see it (PLAN-2026-10 §2, `Lang.lean`). Ring 0.

  A language is a type of programs, a type of inputs, which inputs an attacker cannot tell
  apart (`lowIn`), and a fuelled run that produces the one observation `Beh`. That is the whole
  interface. A source language, an IR between passes and RV64IM are all `Lang`s, so certificate
  meanings are defined once (`Cert.lean`) and carried across passes (`Pass.lean`).
-/
import LCore.Kernel.Obs

namespace LCore

structure Lang where
  Prog  : Type
  In    : Type
  /-- The attacker cannot tell these inputs apart (they agree on everything public). -/
  lowIn : In → In → Prop
  /-- A run with `n` units of fuel. -/
  run   : Nat → Prog → In → Beh
  /-- The inputs the certificates speak about (F3): well-formed ones, such as a machine state
      with a valid layout. By default every input. A certificate is a claim about every
      admissible input, so a compiler must reach every admissible target input from an
      admissible source input (`PassCert.cover`). -/
  Adm   : In → Prop := fun _ => True

/-- **A lawful language** (F2). More fuel only extends a run: its events and leakage grow at
    the end, its cost grows, and once it has finished it stays finished. And a run that has not
    finished has paid for its fuel: up to a constant that depends only on the program, the fuel
    spent is at most the cost, so a run that never finishes has unbounded cost. -/
structure Lang.Lawful (L : Lang) : Prop where
  ev_mono   : ∀ (p : L.Prog) (i : L.In) (n n' : Nat), n ≤ n' →
    (L.run n p i).ev <+: (L.run n' p i).ev
  lk_mono   : ∀ (p : L.Prog) (i : L.In) (n n' : Nat), n ≤ n' →
    (L.run n p i).lk <+: (L.run n' p i).lk
  cost_mono : ∀ (p : L.Prog) (i : L.In) (n n' : Nat), n ≤ n' →
    (L.run n p i).cost ≤ (L.run n' p i).cost
  stable    : ∀ (p : L.Prog) (i : L.In) (n n' : Nat), n ≤ n' →
    (L.run n p i).out ≠ .fuel → L.run n' p i = L.run n p i
  diverge   : ∀ (p : L.Prog), ∃ d : Nat, ∀ (n : Nat) (i : L.In),
    (L.run n p i).out = .fuel → n ≤ (L.run n p i).cost + d

end LCore
