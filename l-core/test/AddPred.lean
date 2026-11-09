/-
  RC-02 step 6: the model's prediction for `add_diff.py`. For each line on stdin, eight input words in decimal (`a` then `b`, little-endian),
  the bytes `sodium_add`'s image writes to stdout on the model, its result, outcome and cost. Not part of the library.
-/
import LCore.Slice2.AddBytes

open LCore LCore.Slice.Rv LCore.Slice2.AddBytes
open LCore.Slice (W64)

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  IO.FS.writeBinFile s!"{dir}/add.bin" (ByteArray.mk (addImage.map fun (b : Byte) => b.val.toUInt8).toArray)
  IO.FS.writeBinFile s!"{dir}/leaky.bin" (ByteArray.mk (leakyImage.map fun (b : Byte) => b.val.toUInt8).toArray)
  let lines := (← (← IO.getStdin).readToEnd).splitOn "\n"
  let mut out := ""
  for line in lines do
    let ws := ((line.splitOn " ").filter (· ≠ "")).filterMap String.toNat?
    if ws.length == 8 then
      let w : Nat → W64 := fun k => W64.ofNat (ws.getD k 0)
      let r := Slice.Rv.run addImage env0 5000 (init addImage (Slice.Slots.encBytes w) env0)
      let so := r.ev.flatMap fun (e : Ev) => match e with | .emit "out" bs => bs | _ => []
      let o := match r.out with | .done => "done" | .abort => "abort" | .fuel => "fuel"
      out := out ++ s!"{" ".intercalate (so.map toString)} | {o} {r.cost}\n"
  IO.FS.writeFile s!"{dir}/pred.txt" out
