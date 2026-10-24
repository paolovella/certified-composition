/- S-435 scratch: the axiom manifest recomputed with some constants treated as opaque
   (their dependencies are not followed). If the 4.31 manifest comes back, the blocked
   constants are the whole cause of the 4.35 footprint change. -/
import ConfTyping
import Lean

open Lean Elab Command

def blocked : NameSet := NameSet.empty.insert `Int.instLinearOrderPackage

partial def axs (env : Environment) (n : Name) : StateM (NameMap NameSet) NameSet := do
  if let some r := (← get).find? n then return r
  modify (·.insert n {})  -- cycle guard
  let mut acc : NameSet := {}
  let used : Array Name := match env.find? n with
    | some (.axiomInfo v)  => v.type.getUsedConstants
    | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.ctorInfo v)   => v.type.getUsedConstants
    | some (.recInfo v)    => v.type.getUsedConstants
    | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
    | _ => #[]
  if let some (.axiomInfo _) := env.find? n then acc := acc.insert n
  if !blocked.contains n then
    for c in used do
      for a in (← axs env c) do acc := acc.insert a
  modify (·.insert n acc)
  return acc

def auditedRoots : List Name := [`ConfTyping, `TransportCalculus]

run_cmd do
  let env ← getEnv
  let inAudited (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | none => false
    | some idx => auditedRoots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
  let generated (n : Name) : Bool :=
    match n with
    | .str _ s => s == "inj" || s == "injEq" || s == "sizeOf_spec" || s.startsWith "eq_"
                  || s.startsWith "match_" || s.startsWith "proof_" || s == "_sunfold"
    | _ => false
  let mut cache : NameMap NameSet := {}
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let isTD := match ci with | .thmInfo _ | .defnInfo _ => true | _ => false
    if isTD && inAudited n && !n.isInternal && !generated n then
      let (r, c') := (axs env n).run cache
      cache := c'
      let sorted := (r.toArray.map toString).qsort (· < ·)
      let m := match env.getModuleIdxFor? n with
        | some idx => env.header.moduleNames[idx.toNat]!
        | none => Name.anonymous
      rows := rows.push s!"{n}\t{m}\t{",".intercalate sorted.toList}"
  for r in rows.qsort (· < ·) do
    IO.println r
