import TransportKernel
import Lean
open Lean Elab Command

-- P0-10 scratch check: every TransportKernel declaration uses only the standard three axioms.
run_cmd do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad : Array String := #[]
  for (c, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    unless (`TransportKernel).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    match ci with
    | .thmInfo _ | .defnInfo _ =>
      if c.isInternal then continue
      n := n + 1
      let axs ← liftCoreM <| collectAxioms c
      for a in axs do
        unless std.contains a do bad := bad.push s!"{c}: {a}"
    | _ => pure ()
  IO.println s!"TransportKernel: {n} declarations, {bad.size} outside the standard three"
  for b in bad do IO.println s!"  {b}"
