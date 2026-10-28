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

end LCore
