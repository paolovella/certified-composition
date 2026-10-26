/-
  The witness registry (P0-04): for every checker, the theorems that witness it accepting and
  refusing. A refusal alone is satisfied by a checker that rejects everything, and an acceptance
  alone by one that accepts everything (CLAUDE.md), so each checker needs both.

  Nothing is registered by hand. Both lists are computed from the environment:
  - a *checker* is a definition of `ConfTyping` whose name contains `check` and whose result,
    after its arguments, is `Option _` or `Bool`;
  - a *witness* is a closed theorem (no leading `∀`) stating `c args = r`, or
    `(c args).isSome = r`, with `c` a checker and `r` a literal:
      accepted:  `some _`, `true`, or `isSome … = true`
      refused:   `none`,   `false`, or `isSome … = false`
    Closed, because `∀ c, check c = none → …` is a lemma about the checker, not a witness.

  Run:  cd conf-typing && lake env lean WitnessRegistry.lean
  Prints one row per checker (`name<TAB>accepted<TAB>refused<TAB>an example of each`), then
  `registry: N checkers, M missing a witness`. Not part of the `ConfTyping` library.
-/
import ConfTyping
import Lean

open Lean Meta Elab Command

def inConfTyping (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx => (`ConfTyping).isPrefixOf env.header.moduleNames[idx.toNat]!

/-- Generated auxiliaries are not checkers anyone wrote. -/
def generated (n : Name) : Bool :=
  n.isInternal || match n with
    | .str _ s => s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "proof_"
                  || s == "_unary" || s == "_binary" || s.startsWith "_"
    | _ => false

def lastHasCheck (n : Name) : Bool :=
  match n with
  | .str _ s => (s.toLower.splitOn "check").length > 1
  | _ => false

/-- `Option _` or `Bool`, after all arguments. -/
def isVerdictType (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ body => do
    let body ← whnfR body
    return body.isAppOfArity ``Option 1 || body.isConstOf ``Bool

inductive Verdict | accepted | refused

/-- The checker a closed witness statement is about, and which way it goes. -/
def classify (checkers : NameSet) (t : Expr) : Option (Name × Verdict) := do
  guard (!t.isForall)
  let some (_, lhs, rhs) := t.eq? | none
  let rhsHead := rhs.getAppFn.constName?
  let lhsHead ← lhs.getAppFn.constName?
  if lhsHead == ``Option.isSome then
    let c ← lhs.appArg!.getAppFn.constName?
    guard (checkers.contains c)
    if rhsHead == some ``Bool.true then return (c, .accepted)
    if rhsHead == some ``Bool.false then return (c, .refused)
    none
  else
    guard (checkers.contains lhsHead)
    match rhsHead with
    | some ``Option.some | some ``Bool.true => return (lhsHead, .accepted)
    | some ``Option.none | some ``Bool.false => return (lhsHead, .refused)
    | _ => none

run_cmd liftTermElabM do
  let env ← getEnv
  let mut checkers : NameSet := {}
  for (n, ci) in env.constants.toList do
    if let .defnInfo _ := ci then
      if inConfTyping env n && !generated n && lastHasCheck n then
        if ← isVerdictType ci.type then
          checkers := checkers.insert n
  let mut acc : Std.HashMap Name (Array Name) := {}
  let mut ref : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if inConfTyping env n && !generated n then
        match classify checkers ci.type with
        | some (c, .accepted) => acc := acc.insert c ((acc.getD c #[]).push n)
        | some (c, .refused) => ref := ref.insert c ((ref.getD c #[]).push n)
        | none => pure ()
  let mut missing := 0
  for c in checkers.toList.toArray.qsort (·.toString < ·.toString) do
    let a := (acc.getD c #[]).qsort (·.toString < ·.toString)
    let r := (ref.getD c #[]).qsort (·.toString < ·.toString)
    if a.isEmpty || r.isEmpty then missing := missing + 1
    let ex (xs : Array Name) := if xs.isEmpty then "-" else toString xs[0]!
    IO.println s!"{c}\t{a.size}\t{r.size}\t{ex a}\t{ex r}"
  IO.println s!"registry: {checkers.size} checkers, {missing} missing a witness"
