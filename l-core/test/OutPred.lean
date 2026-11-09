/-
  RC-02 step 3: the model's prediction for `out_diff.py`. For each program and input on stdin, the compiled image, the bytes the model
  writes to stdout, and the result. Not part of the library.

  Input lines: `name w0 w1`, the two input words in decimal.
-/
import LCore.Slice2.Out

open LCore LCore.Slice.Rv LCore.Slice2.Lower LCore.Slice2.Ops
open LCore.Slice (W64)

/-- `for (i = 0; i < 16; i++) a[i] = a[i] + 1;` on two words, then the output: every byte plus one, mod 256. -/
def addOne : LCore.Slice2.Prog where
  inputs := ["x0", "x1"]
  body := .seq (LCore.Slice2.For.forN "c" (lit 16)
    (.seq (.assign "i" (.bin .sub (lit 16) (.var "c")))
      (.seq (.loadB "t" ["x0", "x1"] (.var "i")) (.storeB ["x0", "x1"] (.var "i") (.add (.var "t") (lit 1))))))
    (.emitB ["x0", "x1"])
  ret := lit 0

def prog : String → Option LCore.Slice2.Prog
  | "put1" => some LCore.Slice2.Out.put1
  | "addOne" => some addOne
  | _ => none

def words2 (a b : Nat) : Nat → W64 := fun k => if k = 0 then W64.ofNat a else if k = 1 then W64.ofNat b else W64.ofNat 0

def hexs (l : List Nat) : String := " ".intercalate (l.map toString)

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let lines := (← (← IO.getStdin).readToEnd).splitOn "\n"
  let mut out := ""
  for line in lines do
    match (line.splitOn " ").filter (· ≠ "") with
    | [n, a, b] =>
      match prog n with
      | some p =>
        let img := code (genP (LCore.Slice2.Slots.compile p))
        let d := Slice.Slots.encBytes (words2 a.toNat! b.toNat!)
        let r := Slice.Rv.run img env0 5000 (init img d env0)
        let so := r.ev.flatMap fun (e : Ev) => match e with | .emit "out" bs => bs | _ => []
        let ret := r.ev.filterMap fun (e : Ev) => match e with | .ext "ret" [Int.ofNat v] => some v | _ => none
        out := out ++ s!"CASE {n} {a} {b}\nIMG {hexs (img.map (fun (b : Byte) => b.val))}\nOUT {hexs so}\nRET {hexs ret} {repr r.out}\n"
      | none => pure ()
    | _ => pure ()
  IO.FS.writeFile s!"{dir}/pred.txt" out
