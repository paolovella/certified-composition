import ConfTyping
import Lean
open Lean Elab Command
def used (env : Environment) (n : Name) : Array Name := match env.find? n with
  | some (.axiomInfo v)  => v.type.getUsedConstants
  | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.ctorInfo v)   => v.type.getUsedConstants
  | some (.recInfo v)    => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | _ => #[]
def path (env : Environment) (src tgt : Name) (blk : NameSet) : Option (List Name) := Id.run do
  let mut q : Array Name := #[src]
  let mut par : NameMap Name := {}
  let mut seen : NameSet := NameSet.empty.insert src
  let mut i := 0
  while i < q.size do
    let x := q[i]!; i := i + 1
    if x == tgt then
      let mut p := [x]; let mut c := x
      while c != src do c := (par.find? c).getD src; p := c :: p
      return some p
    if blk.contains x then continue
    for y in used env x do
      if !seen.contains y then seen := seen.insert y; par := par.insert y x; q := q.push y
  return none
run_cmd do
  let env ← getEnv
  let blk := (NameSet.empty.insert `Int.instLinearOrderPackage).insert `Std.PreorderPackage.toBEq
  for (s, t, b) in [(`ConfTyping.Qsecret, `propext, blk), (`ConfTyping.Qsecret, `Classical.choice, {}),
                    (`ConfTyping.wall_const, `propext, {})] do
    logInfo m!"{s} → {t}: {path env s t b}"
