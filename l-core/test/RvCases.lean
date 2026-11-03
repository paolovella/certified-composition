/-
  VS-1 step 4: the cases for `rv_diff.py`. For each, write the ELF the model's `elf` builds, and the model's prediction:
  its outcome, its cost, and each step's PC and registers.

  Run by `rv_diff.py`. Not part of the library, since it does IO and nothing is proved here.
-/
import LCore.Slice.Rv

open LCore.Slice LCore.Slice.Rv

namespace RvCases

abbrev sp := 2
abbrev ra := 1
abbrev t1 := 6
abbrev s1 := 9

/-- Every case first sets its own stack, as the compiled program will, and ends by exiting. -/
def stub : List Insn := [.lui sp 0x21, .lui t2 0x20]
def exit : List Insn := [.addi a7 0 93, .ecall]

def inputWord (v : Nat) : List Byte := le 8 v

/-- The model's steps until it stops, or `n` run out, and how it stopped. -/
def trace (c : List Byte) (e : Env) : Nat → Mach → List Mach × String × W64
  | 0, m => ([m], "fuel", W64.ofNat 0)
  | n + 1, m =>
    match step c e m with
    | .next _ m' => let r := trace c e n m'; (m :: r.1, r.2)
    | .exit w => ([m], "done", w)
    | .fault _ => ([m], "abort", W64.ofNat 0)

def hex (n : Nat) : String :=
  let s := (Nat.toDigits 16 n).asString
  String.ofList (List.replicate (16 - s.length) '0') ++ s

def line (m : Mach) : String :=
  " ".intercalate (hex m.pc :: (List.range 31).map fun i => hex (m.get (i + 1)).val)

/-- An input as the data segment's bytes, with the rest zero. -/
def dataFn (d : List Byte) : Nat → Byte := fun off => d.getD off (byteOf 0)

structure Case where
  name : String
  /-- What the real machine should do differently, if this is a known deviation. -/
  deviates : Bool := false
  body : List Byte
  data : List Byte := []

def ins (name : String) (p : List Insn) (data : List Byte := []) : Case :=
  { name := name, body := code (stub ++ p ++ exit), data := data }

def cases : List Case :=
  [ ins "addi_edges" [.addi a0 0 2047, .addi t0 0 (-2048), .addi t1 t0 (-1), .addi s1 a0 1, .add a0 s1 0]
  , ins "addi_x0_is_zero" [.addi 0 0 5, .add a0 0 0, .addi t0 0 3, .add a0 a0 t0]
  , ins "lui_high_bit" [.lui a0 0x80000, .lui t0 0xfffff, .lui t1 0x7ffff, .lui s1 0x1, .addi s1 s1 (-1)]
  , ins "add_wraps" [.addi t0 0 (-1), .addi t1 0 1, .add a0 t0 t1, .addi s1 0 (-1), .add s1 s1 s1]
  , ins "sd_ld" [.addi t0 0 42, .sd t0 sp (-8), .ld a0 sp (-8), .ld t1 sp (-16)]
  , ins "ld_negative_value" [.addi t0 0 (-2), .sd t0 sp (-8), .ld a0 sp (-8)]
  , ins "ld_positive_offset" [.addi t0 0 7, .sd t0 t2 2047, .ld a0 t2 2047]
  , ins "sd_unaligned" [.addi t0 0 (-1), .sd t0 t2 603, .ld a0 t2 600, .ld t1 t2 603, .ld s1 t2 606]
  , ins "sd_overlap" [.lui t0 0x12345, .sd t0 t2 600, .lui t1 0x54321, .sd t1 t2 604, .ld a0 t2 600, .ld s1 t2 604]
  , ins "beq_taken" [.addi t0 0 1, .beq t0 t0 8, .addi a0 0 9, .addi t1 0 2]
  , ins "beq_not_taken" [.addi t0 0 1, .beq t0 0 8, .addi a0 0 9, .addi t1 0 2]
  , ins "beq_backward" [.addi t0 0 3, .addi t0 t0 (-1), .addi a0 a0 2, .beq t0 0 8, .beq 0 0 (-12)]
  , ins "input_words" [.ld a0 t2 0, .ld t0 t2 8, .add a0 a0 t0] (inputWord 40 ++ inputWord 2)
  , ins "input_full_width" [.ld a0 t2 0, .addi t1 a0 1] (inputWord (2 ^ 64 - 1))
  , ins "zeroed_data" [.ld a0 t2 256] (inputWord 7)
  , ins "exit_keeps_a0" [.addi a0 0 300]
  , ins "fault_load_null" [.ld t0 0 0, .addi a0 0 1]
  , ins "fault_store_code" [.lui t0 0x10, .addi t0 t0 0xb0, .sd t0 t0 0, .addi a0 0 1]
  , ins "fault_store_header" [.lui t0 0x10, .sd t0 t0 0, .addi a0 0 1]
  , ins "fault_store_null" [.sd t0 0 0, .addi a0 0 1]
  , ins "fault_past_data" [.lui t0 0x22, .ld a0 t0 0]
  , { name := "fault_illegal", body := code (stub ++ [.addi a0 0 1]) ++ le 4 0xffffffff }
  , { name := "fault_past_code", body := code (stub ++ [.addi a0 0 1]) }
  , { name := "dev_compressed", deviates := true,
      body := code stub ++ le 2 0x4515 ++ le 2 0x0001 ++ code exit }
  , { name := "dev_unknown_syscall", deviates := true,
      body := code (stub ++ [.addi a7 0 1000, .ecall, .addi a0 0 1] ++ exit) }
  ]

/-- An environment like Linux's: every register zero but the loader's `sp`, which the first instruction replaces,
    and nothing else mapped that these cases touch. -/
def envLinux : Env := env0

def writeCase (dir : String) (c : Case) : IO Unit := do
  let path := s!"{dir}/{c.name}"
  IO.FS.writeBinFile path (ByteArray.mk ((elf c.body c.data).map fun b => b.val.toUInt8).toArray)
  IO.setAccessRights path { user := { read := true, write := true, execution := true } }
  let r := trace c.body envLinux 200 (init c.body (dataFn c.data) envLinux)
  let beh := run c.body envLinux 200 (init c.body (dataFn c.data) envLinux)
  let head := s!"{r.2.1} {hex r.2.2.val} {beh.cost} {if c.deviates then "deviates" else "exact"}"
  IO.FS.writeFile (path ++ ".pred") ("\n".intercalate (head :: r.1.map line) ++ "\n")

end RvCases

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  for c in RvCases.cases do
    RvCases.writeCase dir c
  IO.println s!"{RvCases.cases.length} cases"
