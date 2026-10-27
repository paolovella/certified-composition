/-
  The definition half of `tools/ring0.lock` (P0-03) and all of `tools/checkers.lock` (P0-11).
  A frozen statement can be weakened without touching its text, by editing a definition it
  mentions: make `CostAtMost` always true and `costCheck_sound` still says the same words. So
  this walks every frozen statement's dependency closure inside the two mathlib-free packages,
  through definitions' values and inductives' constructors, and prints one structural hash per
  constant.

  The walk does not enter the checkers. A frozen theorem `X_sound` names its checker `X`
  (`costCheck c = some k → CostAtMost c k`), and the comparator makes every such theorem be
  re-proved against the rest, so an edit to `X` cannot weaken what the statement says. What the
  statements mean (`ring0.lock`) is the closure that avoids the checkers; only the user's key may
  change it. Each checker's own closure, minus the meaning, is printed as `checker` lines
  (`checkers.lock`), which a change may update within the base gate's limit.

  Run from the repo root: `lake env lean tools/gate/Ring0Lock.lean` (tools/ring0-lock.sh).
  It reads the statements from `StatementsProof`, whose theorems `lake comparator` has checked
  are exactly the challenge's.
-/
import StatementsProof
import Lean

open Lean Elab Command

def inPackages (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`ConfTyping).isPrefixOf m || (`TransportCalculus).isPrefixOf m

/-- The constants a declaration's meaning rests on: its type, a definition's value, an
    inductive's constructors. A theorem's proof is not followed: proofs are irrelevant. -/
def deps (ci : ConstantInfo) : NameSet :=
  let base := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo d => base.append d.value.getUsedConstantsAsSet
  | .inductInfo i => i.ctors.foldl (fun s c => s.insert c) base
  | .ctorInfo c => base.insert c.induct
  | _ => base

def hashOf (ci : ConstantInfo) : UInt64 :=
  match ci with
  | .defnInfo d => mixHash ci.type.hash d.value.hash
  | _ => ci.type.hash

/-- Everything in the packages reachable from `start`, not entering `avoid`. -/
def closure (env : Environment) (start : Array Name) (avoid : NameSet) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := start
  while work.size > 0 do
    let n := work.back!
    work := work.pop
    if seen.contains n || avoid.contains n || !inPackages env n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in (deps ci).toList do
        unless seen.contains c do work := work.push c
  return seen

def sorted (s : NameSet) : Array Name := s.toList.toArray.qsort (·.toString < ·.toString)

run_cmd do
  let env ← getEnv
  let roots := env.constants.toList.filterMap fun (n, ci) =>
    match ci, env.getModuleIdxFor? n with
    | .thmInfo _, some idx =>
      if n.components.any (· == `Frozen) && env.header.moduleNames[idx.toNat]! == `StatementsProof
      then some (n, ci) else none
    | _, _ => none
  -- `Frozen.X_sound` names the checker `X`: a constant of that last component in its statement
  let mut checkers : NameSet := {}
  for (n, ci) in roots do
    if let .str _ s := n then
      if s.endsWith "_sound" then
        let stem := String.ofList (s.toList.take (s.length - "_sound".length))
        for c in ci.type.getUsedConstants do
          if let .str _ cs := c then
            if cs == stem && inPackages env c then checkers := checkers.insert c
  let start := roots.toArray.flatMap fun (_, ci) => ci.type.getUsedConstants
  let meaning := closure env start checkers
  IO.println s!"frozen statements\t{roots.length}"
  IO.println s!"checkers\t{checkers.size}\t{" ".intercalate ((sorted checkers).map (·.toString)).toList}"
  for n in sorted meaning do
    if let some ci := env.find? n then
      IO.println s!"{n}\t{hashOf ci}"
  for k in sorted checkers do
    for n in sorted (closure env #[k] meaning) do
      if let some ci := env.find? n then
        IO.println s!"checker\t{k}\t{n}\t{hashOf ci}"
