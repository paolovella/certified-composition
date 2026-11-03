import LCore.Slice.Lower
open LCore.Slice LCore.Slice.Rv LCore.Slice.Slots LCore.Slice.Lower

def image (a b : Nat) : List UInt8 :=
  (elf (code (genP (compile clean))) ((List.range 16).map (encBytes (inp a b)))).map fun x => x.val.toUInt8

def main (args : List String) : IO Unit := do
  let d := args.headD "."
  for (a, b) in [(5, 3), (6, 3), (250, 3), (5, 0), (5, 200)] do
    let p := s!"{d}/clean_{a}_{b}"
    IO.FS.writeBinFile p (ByteArray.mk (image a b).toArray)
    IO.setAccessRights p { user := { read := true, write := true, execution := true } }
    let beh := Rv.run (code (genP (compile clean))) env0 500
      (init (code (genP (compile clean))) (encBytes (inp a b)) env0)
    IO.println s!"{p} predicted cost {beh.cost} ev {repr beh.ev} out {repr beh.out}"
