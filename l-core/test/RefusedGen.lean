/-
  VS-1 step 9: binaries for `refused_diff.py`: each refused program and `clean`, on input pairs differing only in the secret, with
  the checker's verdict. Compiled by the same passes, without the checker. Not part of the library.
-/
import LCore.Slice.Teeth

open LCore.Slice LCore.Slice.Rv LCore.Slice.Slots LCore.Slice.Lower LCore.Slice.Teeth

def image (p : Prog) (a b : Nat) : List UInt8 :=
  (elf (compiled p) ((List.range 16).map (encBytes (inp a b)))).map fun x => x.val.toUInt8

def programs : List (String × Prog × Nat × Nat × Nat) :=
  [ ("clean", clean, 0, 6, 1), ("secretBranch", secretBranch, 0, 6, 1), ("secretRet", secretRet, 5, 6, 1),
    ("laundered", laundered, 5, 6, 1), ("oneArm", oneArm, 5, 6, 1), ("shadowed", shadowed, 5, 6, 1) ]

def main (args : List String) : IO Unit := do
  let d := args.headD "."
  for (name, p, a, a', b) in programs do
    for (tag, s) in [("x", a), ("y", a')] do
      let path := s!"{d}/{name}_{tag}"
      IO.FS.writeBinFile path (ByteArray.mk (image p s b).toArray)
      IO.setAccessRights path { user := { read := true, write := true, execution := true } }
    let verdict := match sliceCheck sec0 p with
      | some k => s!"accepted {k}"
      | none => "refused"
    IO.println s!"{name} {verdict}"
