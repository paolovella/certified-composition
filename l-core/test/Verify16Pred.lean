/-
  RC-01 step 6: the model's prediction for `verify16_diff.py`. For each line on stdin, the leakage, result, cost and outcome the model gives
  `crypto_verify_16`'s image, or the early exit's, on four input words at a given fuel.

  Input lines: `image w0 w1 w2 w3 fuel`, where `image` is `verify16` or `earlyExit`, and the words are decimal: `w0 w1` the array `x`, `w2 w3`
  the array `y`, little-endian. Run by `verify16_diff.py`. Not part of the library.
-/
import LCore.Slice2.CTBytes

open LCore LCore.Slice LCore.Slice.Rv LCore.Slice.Slots LCore.Slice2.CTBytes

def lkLine : Lk → String
  | .step [pc] => s!"P {pc}"
  | .addr a => s!"A {a}"
  | _ => "?"

def image : String → Option (List Byte)
  | "verify16" => some verify16Image
  | "earlyExit" => some earlyExitImage
  | _ => none

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  if args.contains "--dump-early" then
    IO.FS.writeBinFile s!"{dir}/early.bin" (ByteArray.mk (earlyExitImage.map fun b => b.val.toUInt8).toArray)
    return
  let stdin ← IO.getStdin
  let mut out : Array String := #[]
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    match l.trimAscii.toString.splitOn " " with
    | [name, a, b, c, d, n] =>
      match image name, a.toNat?, b.toNat?, c.toNat?, d.toNat?, n.toNat? with
      | some code, some a, some b, some c, some d, some n =>
        let beh := Rv.run code env0 n (init code (encBytes (LCore.Slice2.Bytes.words4 a b c d)) env0)
        out := out.push s!"CASE {name} {a} {b} {c} {d} {n}"
        out := out ++ (beh.lk.map lkLine).toArray
        let ret := match beh.ev with
          | [.ext _ [v]] => toString v
          | _ => "none"
        let o := match beh.out with
          | .done => "done"
          | .abort => "abort"
          | .fuel => "fuel"
        out := out.push s!"END {o} {ret} {beh.cost}"
      | _, _, _, _, _, _ => pure ()
    | _ => pure ()
  IO.FS.writeFile s!"{dir}/pred.txt" ("\n".intercalate out.toList ++ "\n")
