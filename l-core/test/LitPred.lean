/-
  CAP-01 part 3: the model's prediction for `lit_diff.py`. For each literal on stdin, in decimal: whether the pipeline accepts
  `x0 := c; write(x0)`, its image, how many instructions build the literal, and the bytes the model writes. Not part of the library.
-/
import LCore.Slice2.Caps

open LCore LCore.Slice.Rv LCore.Slice2.Lower LCore.Slice2.Slots
open LCore.Slice (W64)

def litProg (c : Nat) : LCore.Slice2.Prog :=
  { inputs := ["x0"], body := .seq (.assign "x0" (.lit (W64.ofNat c))) (.emitB ["x0"]), ret := .lit (W64.ofNat 0) }

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let lines := (← (← IO.getStdin).readToEnd).splitOn "\n"
  let mut out := ""
  let mut k := 0
  for line in lines do
    match line.trimAscii.toString.toNat? with
    | some c =>
      let p := litProg c
      let ok := fits p && okP (compile p)
      let img := code (genP (compile p))
      IO.FS.writeBinFile s!"{dir}/l{k}.bin" (ByteArray.mk (img.map fun (b : Byte) => b.val.toUInt8).toArray)
      let r := Slice.Rv.run img env0 1000 (init img (Slice.Slots.encBytes fun _ => W64.ofNat 0) env0)
      let so := r.ev.flatMap fun (e : Ev) => match e with | .emit "out" bs => bs | _ => []
      out := out ++ s!"{c} {ok} {Slice.Lower.litLen (W64.ofNat c)} {" ".intercalate (so.map toString)}\n"
      k := k + 1
    | none => pure ()
  IO.FS.writeFile s!"{dir}/pred.txt" out
