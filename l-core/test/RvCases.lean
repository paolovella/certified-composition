/-
  VS-1 step 4: the cases for `rv_diff.py`. For each, write the ELF the model's `elf` builds, and the model's prediction:
  its outcome, its cost, and each step's PC and registers.

  Run by `rv_diff.py`. Not part of the library, since it does IO and nothing is proved here.
-/
import LCore.Slice.Rv

open LCore LCore.Slice LCore.Slice.Rv

namespace RvCases

abbrev sp := 2
abbrev ra := 1
abbrev t1 := 6
abbrev s1 := 9
abbrev a1 := 11
abbrev a2 := 12

/-- Every case first sets its own stack, as the compiled program will, and ends by exiting. -/
def stub : List Insn := [.lui sp 0x21, .lui t2 0x20]
def exit : List Insn := [.addi a7 0 93, .ecall]

def inputWord (v : Nat) : List Byte := le 8 v

/-- The model's steps until it stops, or `n` run out, and how it stopped. Each step has the leakage it adds. -/
def trace (c : List Byte) (e : Env) : Nat → Mach → List (Mach × List Lk) × String × W64
  | 0, m => ([(m, [])], "fuel", W64.ofNat 0)
  | n + 1, m =>
    match step c e m with
    | .next l m' => let r := trace c e n m'; ((m, l) :: r.1, r.2)
    | .out _ l m' => let r := trace c e n m'; ((m, l) :: r.1, r.2)
    | .exit w => ([(m, [])], "done", w)
    | .fault l => ([(m, l)], "abort", W64.ofNat 0)

def hex (n : Nat) : String :=
  let s := (Nat.toDigits 16 n).asString
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- A step's PC, registers, the first address it leaks or `-`, and how many addresses it leaks (RC-02: `write` leaks a range). -/
def line (x : Mach × List Lk) : String :=
  let a := match x.2 with
    | .addr (.ofNat a) :: _ => hex a
    | _ => "-"
  let k := (x.2.filter fun l => match l with | .addr _ => true | _ => false).length
  " ".intercalate (hex x.1.pc :: ((List.range 31).map fun i => hex (x.1.get (i + 1)).val) ++ [a, hex k])

/-- The bytes a run writes to stdout: the payloads of its `.emit "out"` events. -/
def stdoutOf (b : Beh) : List Nat := b.ev.flatMap fun v => match v with
  | .emit "out" d => d
  | _ => []

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
  , ins "andi_mask" [.addi t0 0 (-1), .andi a0 t0 63, .andi t1 t0 (-1), .addi s1 0 200, .andi s1 s1 63]
  , ins "andi_zero" [.addi t0 0 64, .andi a0 t0 63]
  , ins "andi_input_near_wrap" [.ld t0 t2 0, .andi a0 t0 63, .andi t1 t0 (-64)] (inputWord (2 ^ 64 - 3))
  , ins "array_index_doubled" [.addi t0 0 67, .andi t0 t0 63, .add t0 t0 t0, .add t0 t0 t0, .add t0 t0 t0, .add t0 t0 t2,
      .addi a0 0 9, .sd a0 t0 512, .ld a0 t0 512]
  , ins "sub_wraps" [.addi t0 0 3, .addi t1 0 5, .sub a0 t0 t1, .sub s1 t1 t0, .sub t0 0 t1]
  , ins "sub_full_width" [.ld t0 t2 0, .ld t1 t2 8, .sub a0 t0 t1, .sub s1 t1 t0] (inputWord (2 ^ 64 - 1) ++ inputWord (2 ^ 63))
  , ins "xor_or_and" [.addi t0 0 0x5a, .addi t1 0 0x3c, .xor a0 t0 t1, .or s1 t0 t1, .and t0 t0 t1, .add a0 a0 s1, .add a0 a0 t0]
  , ins "xor_or_and_wide" [.ld t0 t2 0, .ld t1 t2 8, .xor a0 t0 t1, .or s1 t0 t1, .and t1 t0 t1]
      (inputWord 0xf0f0f0f0f0f0f0f0 ++ inputWord 0xff00ff00ff00ff00)
  , ins "xor_self_is_zero" [.addi t0 0 (-7), .xor a0 t0 t0, .or s1 t0 0]
  , ins "srli_edges" [.addi t0 0 (-1), .srli a0 t0 8, .srli s1 t0 63, .srli t1 t0 0, .addi t0 0 256, .srli t0 t0 8]
  , ins "srli_wide" [.ld t0 t2 0, .srli a0 t0 32, .srli s1 t0 1] (inputWord (2 ^ 63 + 5))
  , ins "verify_tail" [.addi t0 0 0, .addi t0 t0 (-1), .srli t0 t0 8, .andi t0 t0 1, .addi a0 t0 (-1),
      .addi t1 0 7, .addi t1 t1 (-1), .srli t1 t1 8, .andi t1 t1 1, .addi s1 t1 (-1)]
  , ins "lbu_bytes" [.ld t0 t2 0, .lbu a0 t2 0, .lbu t1 t2 7, .lbu s1 t2 3, .add a0 a0 t1] (inputWord 0xff2233445566778f)
  , ins "lbu_offsets" [.addi t0 t2 16, .lbu a0 t0 (-15), .lbu t1 t0 (-1), .lbu s1 t2 9] (inputWord 0x0102030405060708 ++ inputWord 0xa0b0c0d0e0f00010)
  , ins "lbu_index_loop" [.addi t0 0 5, .andi t0 t0 15, .add t0 t0 t2, .lbu a0 t0 0, .addi t1 0 12, .add t1 t1 t2, .lbu s1 t1 0]
      (inputWord 0x1122334455667788 ++ inputWord 0x99aabbccddeeff00)
  , ins "fault_lbu_null" [.lbu a0 0 0, .addi a0 0 1]
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
  -- RC-02 step 2: sb, and write(1, buf, len).
  , ins "sb_bytes" [.addi t0 0 0x1ab, .sb t0 t2 0, .addi t1 0 (-1), .sb t1 t2 3, .sb t0 t2 7, .ld a0 t2 0] (inputWord 0x1122334455667788)
  , ins "sb_offsets" [.addi t0 t2 16, .addi t1 0 0x7f, .sb t1 t0 (-15), .sb t1 t0 (-1), .ld a0 t2 0, .ld s1 t2 8]
  , ins "fault_sb_code" [.lui t0 0x10, .addi t0 t0 0xb0, .sb t0 t0 0, .addi a0 0 1]
  , ins "write_input" [.addi a0 0 1, .add a1 t2 0, .addi a2 0 5, .addi a7 0 64, .ecall, .add s1 a0 0, .addi a0 0 0] (inputWord 0x0a6f6c6c6568)
  , ins "write_after_sb" [.addi t0 0 0x4c, .sb t0 t2 1, .addi a0 0 1, .add a1 t2 0, .addi a2 0 3, .addi a7 0 64, .ecall, .addi a0 0 0]
      (inputWord 0x0a2a41)
  , ins "write_offset_twice" [.addi a0 0 1, .addi a1 t2 2, .addi a2 0 2, .addi a7 0 64, .ecall, .addi a0 0 1, .addi a1 t2 0, .addi a2 0 1,
      .addi a7 0 64, .ecall, .addi a0 0 0] (inputWord 0x0a5958575655)
  , ins "write_zero_len" [.addi a0 0 1, .add a1 t2 0, .addi a2 0 0, .addi a7 0 64, .ecall, .addi a0 a0 7]
  , { name := "dev_write_fd2", deviates := true,
      body := code (stub ++ [.addi a0 0 2, .add a1 t2 0, .addi a2 0 1, .addi a7 0 64, .ecall, .addi a0 0 0] ++ exit), data := inputWord 0x0a }
  , { name := "dev_write_unreadable", deviates := true,
      body := code (stub ++ [.addi a0 0 1, .addi a1 0 0, .addi a2 0 1, .addi a7 0 64, .ecall, .addi a0 0 0] ++ exit) }
  -- CAP-01 part 4a: jal, forward, linking, backward, and past beq's reach
  , ins "jal_forward" [.jal 0 8, .addi a0 0 9, .addi t0 0 1]
  , ins "jal_link" [.jal ra 8, .addi a0 0 9, .add a0 ra 0, .srli a0 a0 2]
  , ins "jal_backward" [.addi t0 0 3, .addi t0 t0 (-1), .addi a0 a0 2, .beq t0 0 8, .jal 0 (-12)]
  , ins "jal_far" ([.jal 0 (4 * 1536)] ++ List.replicate 1535 (.addi a0 a0 1) ++ [.addi a0 0 5])
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
  IO.FS.writeBinFile (path ++ ".stdout") (ByteArray.mk ((stdoutOf beh).map fun n => n.toUInt8).toArray)

end RvCases

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  for c in RvCases.cases do
    RvCases.writeCase dir c
  IO.println s!"{RvCases.cases.length} cases"
