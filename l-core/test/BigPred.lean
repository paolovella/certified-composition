/-
  CAP-01: the model's prediction for `big_diff.py`: an image past the old ELF layout's 3920 bytes. Not part of the library.
-/
import LCore.Slice2.Caps

open LCore LCore.Slice.Rv LCore.Slice2.Lower LCore.Slice2.Slots
open LCore.Slice (W64 Op)

/-- S-USABLE S1's straight-line shape, `n` statements over 12 names. -/
def stmt (j : Nat) : LCore.Slice2.Cmd :=
  let ops : List Op := [.xor, .or, .and, .sub]
  .assign s!"t{j % 8}" (.bin (ops.getD ((j + 1) % 4) .xor)
    (.bin (ops.getD (j % 4) .xor) (.var s!"t{(j + 7) % 8}") (.var s!"x{j % 4}")) (.var s!"t{(j + 3) % 8}"))

def big (n : Nat) : LCore.Slice2.Prog :=
  { inputs := ["x0", "x1", "x2", "x3"], body := LCore.Slice2.Caps.seqAll ((List.range n).map stmt), ret := .var "t0" }

/-- A counted loop of 3 rounds over a 300-statement body: past `beq`'s reach, so the long form (CAP-01 4b). -/
def bigLoop : LCore.Slice2.Prog :=
  { inputs := ["x0", "x1", "x2", "x3"],
    body := LCore.Slice2.For.forN "c" (.lit (W64.ofNat 3)) (LCore.Slice2.Caps.seqAll ((List.range 300).map stmt)), ret := .var "t0" }

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let p := if args.getD 1 "" == "loop" then bigLoop else big 300
  let img := code (genP (compile p))
  let w : Nat → W64 := fun k => W64.ofNat ([0x0123456789abcdef, 0xfedcba9876543210, 0x5555aaaa5555aaaa, 0x0f0f0f0f0f0f0f0f].getD k 0)
  let d := Slice.Slots.encBytes w
  let r := Slice.Rv.run img env0 100000 (init img d env0)
  let ret := r.ev.filterMap fun (e : Ev) => match e with | .ext "ret" [Int.ofNat v] => some v | _ => none
  let data : List Byte := (List.range 32).map fun i => d i
  IO.FS.writeBinFile s!"{dir}/big.bin" (ByteArray.mk (img.map fun (b : Byte) => b.val.toUInt8).toArray)
  IO.FS.writeBinFile s!"{dir}/big.elf" (ByteArray.mk ((elf img data).map fun (b : Byte) => b.val.toUInt8).toArray)
  IO.FS.writeFile s!"{dir}/pred.txt" s!"{fits p && okP (compile p)} {img.length} {ret} {r.cost} {repr r.out}\n"
