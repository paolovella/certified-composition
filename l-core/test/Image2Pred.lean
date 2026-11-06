/-
  VS-2 step 8: the model's prediction for `image2_diff.py`. For each line on stdin, the leakage, result, cost and outcome the model gives one of the
  second slice's images at a given fuel. It also writes the Lean `elf` of `scan` once, for the script to compare with its own.

  Input lines: `image a b fuel`, where `image` is `scan`, `spin`, `tidx`, `tguard` a refused program's name (`Slice2/Teeth.lean`), or `countUp` or `capped` (`Slice2/BoundBytes.lean`), and `a`, `b` are the two input words in decimal. Run by
  `image2_diff.py`. Not part of the library.
-/
import LCore.Slice2.BoundBytes

open LCore LCore.Slice LCore.Slice.Rv LCore.Slice.Slots LCore.Slice2.Image LCore.Slice2.Teeth LCore.Slice2.BoundBytes

def words (a b : Nat) : Nat → W64 :=
  fun k => if k = 0 then W64.ofNat a else if k = 1 then W64.ofNat b else W64.ofNat 0

def lkLine : Lk → String
  | .step [pc] => s!"P {pc}"
  | .addr a => s!"A {a}"
  | _ => "?"

def image : String → Option (List Byte)
  | "scan" => some scanImage
  | "spin" => some spinImage
  | "tidx" => some tamperedIndex
  | "tguard" => some tamperedGuard
  | "secretLoad" => some secretLoadImage
  | "secretStore" => some secretStoreImage
  | "secretLoop" => some secretLoopImage
  | "secondIter" => some secondIterImage
  | "throughArray" => some throughArrayImage
  | "arrayInLoop" => some arrayInLoopImage
  | "countUp" => some countUpImage
  | "capped" => some cappedImage
  | _ => none

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let elfBytes := (elf scanImage ((List.range 16).map (encBytes (words 5 3)))).map fun b => b.val.toUInt8
  IO.FS.writeBinFile s!"{dir}/lean_elf" (ByteArray.mk elfBytes.toArray)
  let stdin ← IO.getStdin
  let mut out : Array String := #[]
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    match l.trimAscii.toString.splitOn " " with
    | [name, a, b, n] =>
      match image name, a.toNat?, b.toNat?, n.toNat? with
      | some c, some a, some b, some n =>
        let beh := Rv.run c env0 n (init c (encBytes (words a b)) env0)
        out := out.push s!"CASE {name} {a} {b} {n}"
        out := out ++ (beh.lk.map lkLine).toArray
        let ret := match beh.ev with
          | [.ext _ [v]] => toString v
          | _ => "none"
        let o := match beh.out with
          | .done => "done"
          | .abort => "abort"
          | .fuel => "fuel"
        out := out.push s!"END {o} {ret} {beh.cost}"
      | _, _, _, _ => pure ()
    | _ => pure ()
  IO.FS.writeFile s!"{dir}/pred.txt" ("\n".intercalate out.toList ++ "\n")
