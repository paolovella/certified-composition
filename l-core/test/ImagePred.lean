/-
  VS-1 step 8: the model's prediction for `image_diff.py`. For each input pair on stdin, the leakage, result, cost and outcome the
  model gives the literal image. It also writes the Lean `elf` of the image once, for the script to compare with its own.

  Input lines: `a b`, the two input words, in decimal. Run by `image_diff.py`. Not part of the library.
-/
import LCore.Slice.Image

open LCore LCore.Slice LCore.Slice.Rv LCore.Slice.Slots LCore.Slice.Lower LCore.Slice.Image

def words (a b : Nat) : Nat → W64 :=
  fun k => if k = 0 then W64.ofNat a else if k = 1 then W64.ofNat b else W64.ofNat 0

def lkLine : Lk → String
  | .step [pc] => s!"P {pc}"
  | .addr a => s!"A {a}"
  | _ => "?"

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let elfBytes := (elf cleanImage ((List.range 16).map (encBytes (words 5 3)))).map fun b => b.val.toUInt8
  IO.FS.writeBinFile s!"{dir}/lean_elf" (ByteArray.mk elfBytes.toArray)
  let stdin ← IO.getStdin
  let mut out : Array String := #[]
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    match (l.trimAscii.toString.splitOn " ").map String.toNat? with
    | [some a, some b] =>
      let beh := Rv.run cleanImage env0 500 (init cleanImage (encBytes (words a b)) env0)
      out := out.push s!"CASE {a} {b}"
      out := out ++ (beh.lk.map lkLine).toArray
      let ret := match beh.ev with
        | [.ext _ [v]] => toString v
        | _ => "none"
      let o := match beh.out with
        | .done => "done"
        | .abort => "abort"
        | .fuel => "fuel"
      out := out.push s!"END {o} {ret} {beh.cost}"
    | _ => pure ()
  IO.FS.writeFile s!"{dir}/pred.txt" ("\n".intercalate out.toList ++ "\n")
