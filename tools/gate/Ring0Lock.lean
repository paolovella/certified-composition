/-
  The definition half of `tools/ring0.lock` (P0-03). A frozen statement can be weakened without
  touching its text, by editing a definition it mentions: make `CostAtMost` always true and
  `costCheck_sound` still says the same words. So this walks every frozen statement's dependency
  closure inside the two mathlib-free packages, through definitions' values and inductives'
  constructors, and prints one structural hash per constant. Any change to any of them is a lock
  diff, which only the user's key may accept.

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
def deps (ci : ConstantInfo) (env : Environment) : NameSet :=
  let base := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo d => base.append d.value.getUsedConstantsAsSet
  | .inductInfo i => i.ctors.foldl (fun s c => s.insert c) base
  | .ctorInfo c => base.insert c.induct
  | _ => let _ := env; base

def hashOf (ci : ConstantInfo) : UInt64 :=
  match ci with
  | .defnInfo d => mixHash ci.type.hash d.value.hash
  | _ => ci.type.hash

run_cmd do
  let env ← getEnv
  let roots := env.constants.toList.filterMap fun (n, ci) =>
    match ci with
    | .thmInfo _ =>
      if (n.components.any (· == `Frozen)) && (env.getModuleIdxFor? n).isSome then
        match env.getModuleIdxFor? n with
        | some idx => if env.header.moduleNames[idx.toNat]! == `StatementsProof then some ci else none
        | none => none
      else none
    | _ => none
  let mut seen : NameSet := {}
  let mut work : Array Name := #[]
  for ci in roots do
    for c in ci.type.getUsedConstants do work := work.push c
  while h : work.size > 0 do
    let n := work.back
    work := work.pop
    if seen.contains n || !inPackages env n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in (deps ci env).toList do
        unless seen.contains c do work := work.push c
  IO.println s!"frozen statements\t{roots.length}"
  for n in seen.toList.toArray.qsort (·.toString < ·.toString) do
    if let some ci := env.find? n then
      IO.println s!"{n}\t{hashOf ci}"
