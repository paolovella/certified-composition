/-
  VS-1, step 1: the walking skeleton. Lean produces RV64 bytes and a static ELF for fixed programs.

  **No proofs, and nothing here is believed.** It exists to learn how far the bottom of the stack is, and
  what an emulator can show. `objdump` and QEMU check it from outside. Not imported by `LCore`.

  Run: `lake env lean --run LCore/Slice/Skeleton.lean <output directory>`, from `l-core/`.
-/

namespace LCore.Slice.Skeleton

/-- The RV64 instructions this skeleton uses. Registers are numbers, immediates two's complement. -/
inductive Insn where
  | addi (rd rs1 : Nat) (imm : Int)
  | add  (rd rs1 rs2 : Nat)
  | ld   (rd rs1 : Nat) (imm : Int)
  | sd   (rs2 rs1 : Nat) (imm : Int)
  | beq  (rs1 rs2 : Nat) (imm : Int)
  | ecall

def bits (imm : Int) (n : Nat) : Nat := (imm % (2 ^ n : Int)).toNat

def itype (imm : Int) (rs1 f3 rd op : Nat) : Nat :=
  bits imm 12 * 2 ^ 20 + rs1 * 2 ^ 15 + f3 * 2 ^ 12 + rd * 2 ^ 7 + op

def stype (imm : Int) (rs2 rs1 f3 op : Nat) : Nat :=
  let i := bits imm 12
  (i / 32) * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + f3 * 2 ^ 12 + (i % 32) * 2 ^ 7 + op

def btype (imm : Int) (rs1 rs2 f3 op : Nat) : Nat :=
  let i := bits imm 13
  let b12 := i / 4096 % 2
  let b11 := i / 2048 % 2
  let hi := i / 32 % 64
  let lo := i / 2 % 16
  b12 * 2 ^ 31 + hi * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + f3 * 2 ^ 12 + lo * 2 ^ 8 + b11 * 2 ^ 7 + op

def encode : Insn → Nat
  | .addi rd rs1 imm => itype imm rs1 0 rd 0x13
  | .add rd rs1 rs2  => rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + rd * 2 ^ 7 + 0x33
  | .ld rd rs1 imm   => itype imm rs1 3 rd 0x03
  | .sd rs2 rs1 imm  => stype imm rs2 rs1 3 0x23
  | .beq rs1 rs2 imm => btype imm rs1 rs2 0 0x63
  | .ecall           => 0x73

/-- `n` bytes, little-endian. -/
def le (n v : Nat) : List UInt8 :=
  (List.range n).map fun i => (v / 2 ^ (8 * i) % 256).toUInt8

def code (p : List Insn) : List UInt8 := p.flatMap fun i => le 4 (encode i)

/-- A static RV64 ELF: one header, one loadable segment, execution at the first instruction. -/
def elf (p : List Insn) : List UInt8 :=
  let base := 0x10000
  let hdr := 64 + 56
  let body := code p
  let size := hdr + body.length
  let ident : List UInt8 := [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ident ++ le 2 2 ++ le 2 243 ++ le 4 1 ++ le 8 (base + hdr) ++ le 8 64 ++ le 8 0 ++ le 4 0
    ++ le 2 64 ++ le 2 56 ++ le 2 1 ++ le 2 64 ++ le 2 0 ++ le 2 0
    ++ le 4 1 ++ le 4 5 ++ le 8 0 ++ le 8 base ++ le 8 base ++ le 8 size ++ le 8 size ++ le 8 0x1000
    ++ body

/-- x0, sp, t0, t1, a0, a7. -/
abbrev x0 := 0
abbrev sp := 2
abbrev t0 := 5
abbrev t1 := 6
abbrev a0 := 10
abbrev a7 := 17

/-- Exit with 42. -/
def ret42 : List Insn := [.addi a0 x0 42, .addi a7 x0 93, .ecall]

/-- Through memory and a branch: store 7, load it, skip one instruction if it is zero, add 35, exit. -/
def viaMem (v : Int) : List Insn :=
  [ .addi sp sp (-16), .addi t0 x0 v, .sd t0 sp 8, .ld t1 sp 8, .beq t1 x0 8, .addi t1 t1 35,
    .add a0 t1 x0, .addi a7 x0 93, .ecall ]

def write (dir name : String) (p : List Insn) : IO Unit := do
  let path := s!"{dir}/{name}"
  IO.FS.writeBinFile path (ByteArray.mk (elf p).toArray)
  IO.setAccessRights path { user := { read := true, write := true, execution := true } }

end LCore.Slice.Skeleton

open LCore.Slice.Skeleton in
def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  write dir "ret42" ret42
  write dir "viamem7" (viaMem 7)
  write dir "viamem0" (viaMem 0)
