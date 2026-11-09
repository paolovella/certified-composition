/-
  W32-01 part 3: the model's prediction for `w32_diff.py`. The C reading of `uint32_t` (`research/2026-11/W32-01-READING.md`), applied
  by hand: a `uint32_t` is a word whose top 32 bits are zero, and each `+`, `-` and `<<` is followed by `& 0xffffffff`. `^ | & >>` keep
  the top bits zero and are not masked.

  Each case is a program over four input words `x0 … x3`, which writes them back as its output. The `raw` cases are the same programs
  without the masks: the vacuity witness, which should disagree with clang. Not part of the library.

  Input lines: `name a b c d`, the four input words in decimal. Names: `rotl<k>` and `rotlraw<k>` for `k` in 1…31, `add`, `addraw`,
  `sub`, `subraw`, `qr` (ChaCha's quarter round on `x0 … x3`) and `qrraw`.
-/
import LCore.Slice2.Shl

open LCore LCore.Slice.Rv LCore.Slice2.Lower LCore.Slice2.Ops
open LCore.Slice (W64 Expr)

def m32 : Expr := lit 0xffffffff
def v (x : String) : Expr := .var x

/-- `e` masked to 32 bits, under the reading; the identity in the raw variant. -/
def mask (raw : Bool) (e : Expr) : Expr := if raw then e else .bin .and e m32

/-- `ROTL32(x, k)` = `(x << k) | (x >> (32 - k))`, with `<<` masked. -/
def rotl (raw : Bool) (e : Expr) (k : Nat) : Expr := .bin .or (mask raw (.shl e k)) (.shr e (32 - k))

def out4 : LCore.Slice2.Cmd := .emitB ["x0", "x1", "x2", "x3"]

def prog4 (body : LCore.Slice2.Cmd) : LCore.Slice2.Prog :=
  { inputs := ["x0", "x1", "x2", "x3"], body := .seq body out4, ret := lit 0 }

/-- `a += b; d ^= a; d <<<= 16; c += d; b ^= c; b <<<= 12; a += b; d ^= a; d <<<= 8; c += d; b ^= c; b <<<= 7;` (RFC 8439 §2.1). -/
def qr (raw : Bool) : LCore.Slice2.Cmd :=
  let addTo (x y : String) : LCore.Slice2.Cmd := .assign x (mask raw (.add (v x) (v y)))
  let xorRot (x y : String) (k : Nat) : LCore.Slice2.Cmd :=
    .seq (.assign x (.bin .xor (v x) (v y))) (.assign x (rotl raw (v x) k))
  .seq (addTo "x0" "x1") (.seq (xorRot "x3" "x0" 16) (.seq (addTo "x2" "x3") (.seq (xorRot "x1" "x2" 12)
    (.seq (addTo "x0" "x1") (.seq (xorRot "x3" "x0" 8) (.seq (addTo "x2" "x3") (xorRot "x1" "x2" 7)))))))

def prog (n : String) : Option LCore.Slice2.Prog :=
  if n = "add" then some (prog4 (.assign "x0" (mask false (.add (v "x0") (v "x1")))))
  else if n = "addraw" then some (prog4 (.assign "x0" (mask true (.add (v "x0") (v "x1")))))
  else if n = "sub" then some (prog4 (.assign "x0" (mask false (.bin .sub (v "x0") (v "x1")))))
  else if n = "subraw" then some (prog4 (.assign "x0" (mask true (.bin .sub (v "x0") (v "x1")))))
  else if n = "qr" then some (prog4 (qr false))
  else if n = "qrraw" then some (prog4 (qr true))
  else if n.startsWith "rotlraw" then (n.drop 7).toNat?.map fun k => prog4 (.assign "x0" (rotl true (v "x0") k))
  else if n.startsWith "rotl" then (n.drop 4).toNat?.map fun k => prog4 (.assign "x0" (rotl false (v "x0") k))
  else none

def words4 (a b c d : Nat) : Nat → W64 := fun k =>
  if k = 0 then W64.ofNat a else if k = 1 then W64.ofNat b else if k = 2 then W64.ofNat c else if k = 3 then W64.ofNat d
  else W64.ofNat 0

def nums (l : List Nat) : String := " ".intercalate (l.map toString)

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let lines := (← (← IO.getStdin).readToEnd).splitOn "\n"
  let mut out := ""
  for line in lines do
    match (line.splitOn " ").filter (· ≠ "") with
    | [n, a, b, c, d] =>
      match prog n with
      | some p =>
        let ok := LCore.Slice2.Slots.fits p && okP (LCore.Slice2.Slots.compile p)
        let img := code (genP (LCore.Slice2.Slots.compile p))
        let r := Slice.Rv.run img env0 5000 (init img (Slice.Slots.encBytes (words4 a.toNat! b.toNat! c.toNat! d.toNat!)) env0)
        let so := r.ev.flatMap fun (e : Ev) => match e with | .emit "out" bs => bs | _ => []
        out := out ++ s!"CASE {n} {a} {b} {c} {d}\nOK {ok}\nIMG {nums (img.map (fun (b : Byte) => b.val))}\nOUT {nums so}\n"
      | none => out := out ++ s!"CASE {n} {a} {b} {c} {d}\nOK unknown\nIMG\nOUT\n"
    | _ => pure ()
  IO.FS.writeFile s!"{dir}/pred.txt" out
