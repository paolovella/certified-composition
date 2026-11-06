/-
  VS-1 step 4: an RV64 subset as a lawful L language. A program is code bytes, fetched and decoded, so a
  statement about it is about bytes.

  **Not linked to Sail.** This model is believed only as far as `test/rv_diff.py` compares it with QEMU, which is
  test evidence on chosen cases. S-SAIL's proof route is the later link.

  **Where it is known to be wrong**, on purpose. It aborts on what it does not model, and the real machine may carry
  on: a compressed instruction runs, and an unknown syscall returns an error. A jump outside the code is an abort
  here, whatever is mapped there. So a certificate on `rvLang` says nothing about a program that uses these, and the
  compiled programs must not. `test/rv_diff.py` runs both first kinds as expected deviations.

  **Not modelled at all:** timing (cost counts instructions retired), speculation, and attacker-readable residue.
-/
import LCore.Kernel.Pass
import LCore.Slice.Word

namespace LCore.Slice.Rv

abbrev Byte := Fin 256

def byteOf (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide)⟩

/-- `n` bytes, little-endian. -/
def le (n v : Nat) : List Byte := (List.range n).map fun i => byteOf (v / 256 ^ i)

/-! ## Instructions -/

inductive Insn where
  | lui  (rd imm : Nat)
  | addi (rd rs1 : Nat) (imm : Int)
  | andi (rd rs1 : Nat) (imm : Int)
  | add  (rd rs1 rs2 : Nat)
  | ld   (rd rs1 : Nat) (imm : Int)
  | sd   (rs2 rs1 : Nat) (imm : Int)
  | beq  (rs1 rs2 : Nat) (imm : Int)
  | ecall
  deriving DecidableEq, Repr

def bits (imm : Int) (n : Nat) : Nat := (imm % (2 ^ n : Int)).toNat

def encode : Insn → Nat
  | .lui rd imm => imm * 2 ^ 12 + rd * 2 ^ 7 + 0x37
  | .addi rd rs1 imm => bits imm 12 * 2 ^ 20 + rs1 * 2 ^ 15 + rd * 2 ^ 7 + 0x13
  | .andi rd rs1 imm => bits imm 12 * 2 ^ 20 + rs1 * 2 ^ 15 + 7 * 2 ^ 12 + rd * 2 ^ 7 + 0x13
  | .add rd rs1 rs2 => rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + rd * 2 ^ 7 + 0x33
  | .ld rd rs1 imm => bits imm 12 * 2 ^ 20 + rs1 * 2 ^ 15 + 3 * 2 ^ 12 + rd * 2 ^ 7 + 0x03
  | .sd rs2 rs1 imm =>
    let i := bits imm 12
    (i / 32) * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + 3 * 2 ^ 12 + (i % 32) * 2 ^ 7 + 0x23
  | .beq rs1 rs2 imm =>
    let i := bits imm 13
    (i / 4096 % 2) * 2 ^ 31 + (i / 32 % 64) * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15
      + (i / 2 % 16) * 2 ^ 8 + (i / 2048 % 2) * 2 ^ 7 + 0x63
  | .ecall => 0x73

def code (p : List Insn) : List Byte := p.flatMap fun i => le 4 (encode i)

/-- Sign-extend an `n`-bit value. -/
def sext (n v : Nat) : Int :=
  if 2 ^ (n - 1) ≤ v then Int.ofNat v - Int.ofNat (2 ^ n) else Int.ofNat v

/-- The word's fields. -/
def rdOf (w : Nat) : Nat := w / 2 ^ 7 % 32
def rs1Of (w : Nat) : Nat := w / 2 ^ 15 % 32
def rs2Of (w : Nat) : Nat := w / 2 ^ 20 % 32
def f3Of (w : Nat) : Nat := w / 2 ^ 12 % 8

/-- Decode one 32-bit word. Anything else is `none`, which the machine treats as an abort. -/
def decode (w : Nat) : Option Insn :=
  match w % 128 with
  | 0x37 => some (.lui (rdOf w) (w / 2 ^ 12))
  | 0x13 =>
    if f3Of w = 0 then some (.addi (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20)))
    else if f3Of w = 7 then some (.andi (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20)))
    else none
  | 0x33 => if f3Of w = 0 ∧ w / 2 ^ 25 = 0 then some (.add (rdOf w) (rs1Of w) (rs2Of w)) else none
  | 0x03 => if f3Of w = 3 then some (.ld (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20))) else none
  | 0x23 =>
    if f3Of w = 3 then some (.sd (rs2Of w) (rs1Of w) (sext 12 ((w / 2 ^ 25) * 32 + rdOf w))) else none
  | 0x63 =>
    if f3Of w = 0 then
      some (.beq (rs1Of w) (rs2Of w) (sext 13
        ((w / 2 ^ 31) * 4096 + (w / 2 ^ 7 % 2) * 2048 + (w / 2 ^ 25 % 64) * 32 + (w / 2 ^ 8 % 16) * 2)))
    else none
  | 0x73 => if w = 0x73 then some .ecall else none
  | _ => none

/-! ## The machine -/

/-- Where the code and the data segment are. The ELF's two headers occupy the code segment's first bytes. -/
def codeBase : Nat := 0x100b0
def dataBase : Nat := 0x20000
def dataSize : Nat := 0x1000

/-- **The environment**: what the loader leaves and the program must not depend on. The initial registers, and
    memory outside the image: what is there and what may be read or written. -/
structure Env where
  reg : Nat → W64
  mem : Nat → Byte
  rd  : Nat → Bool
  wr  : Nat → Bool

structure Mach where
  pc  : Nat
  x   : Nat → W64
  mem : Nat → Byte

def Mach.get (m : Mach) (r : Nat) : W64 := if r = 0 then W64.ofNat 0 else m.x r

def Mach.set (m : Mach) (r : Nat) (v : W64) : Nat → W64 :=
  if r = 0 then m.x else fun y => if y = r then v else m.x y

def wordOfInt (i : Int) : W64 := W64.ofNat (i % (2 ^ 64 : Int)).toNat

def addImm (a : W64) (i : Int) : Nat := (W64.add a (wordOfInt i)).val

def inCode (code : List Byte) (a : Nat) : Bool := codeBase ≤ a && a < codeBase + code.length
def inData (a : Nat) : Bool := dataBase ≤ a && a < dataBase + dataSize

def canRead (code : List Byte) (e : Env) (a : Nat) : Bool := inCode code a || inData a || e.rd a
def canWrite (code : List Byte) (e : Env) (a : Nat) : Bool := inData a || (!inCode code a && e.wr a)

/-- The 8 addresses of an access, wrapping. -/
def addrs8 (a : Nat) : List Nat := (List.range 8).map fun i => (a + i) % 2 ^ 64

def load8 (m : Mach) (a : Nat) : W64 :=
  W64.ofNat ((List.range 8).foldr (fun i acc => (m.mem ((a + i) % 2 ^ 64)).val + 256 * acc) 0)

def store8 (mem : Nat → Byte) (a : Nat) (v : W64) : Nat → Byte :=
  fun b =>
    match (List.range 8).find? (fun i => (a + i) % 2 ^ 64 == b) with
    | some i => byteOf (v.val / 256 ^ i)
    | none => mem b

/-- The 32-bit word at `pc`, if `pc` is aligned and in the code. -/
def fetch (code : List Byte) (pc : Nat) : Option Nat :=
  if codeBase ≤ pc ∧ pc % 4 = 0 ∧ pc - codeBase + 4 ≤ code.length then
    some ((List.range 4).foldr
      (fun i acc => (code.getD (pc - codeBase + i) (byteOf 0)).val + 256 * acc) 0)
  else none

/-- What one step did. A fault's leakage is what it tried. -/
inductive Step where
  | next  (l : List Lk) (m : Mach)
  | exit  (w : W64)
  | fault (l : List Lk)

/-- The exit syscall's number. -/
def sysExit : W64 := W64.ofNat 93

/-- **One instruction.** -/
def step (code : List Byte) (e : Env) (m : Mach) : Step :=
  match fetch code m.pc with
  | none => .fault []
  | some w =>
    match decode w with
    | none => .fault []
    | some i =>
      let n := m.pc + 4
      match i with
      | .lui rd imm =>
        .next [] { m with pc := n, x := m.set rd (wordOfInt (sext 32 (imm * 2 ^ 12))) }
      | .addi rd rs imm => .next [] { m with pc := n, x := m.set rd (W64.ofNat (addImm (m.get rs) imm)) }
      | .andi rd rs imm => .next [] { m with pc := n, x := m.set rd (W64.and (m.get rs) (wordOfInt imm)) }
      | .add rd a b => .next [] { m with pc := n, x := m.set rd (W64.add (m.get a) (m.get b)) }
      | .ld rd rs imm =>
        let a := addImm (m.get rs) imm
        if (addrs8 a).all (canRead code e) then
          .next [.addr (Int.ofNat a)] { m with pc := n, x := m.set rd (load8 m a) }
        else .fault [.addr (Int.ofNat a)]
      | .sd rv rs imm =>
        let a := addImm (m.get rs) imm
        if (addrs8 a).all (canWrite code e) then
          .next [.addr (Int.ofNat a)] { m with pc := n, mem := store8 m.mem a (m.get rv) }
        else .fault [.addr (Int.ofNat a)]
      | .beq a b imm =>
        .next [] { m with pc := if m.get a = m.get b then addImm (W64.ofNat m.pc) imm else n }
      | .ecall => if m.get 17 = sysExit then .exit (m.get 10) else .fault []

/-- The event that returns a word: the same as the source's. -/
def retEv (w : W64) : Ev := .ext "ret" [Int.ofNat w.val]

/-- **The run**: `n` instructions. Cost counts instructions retired, so a faulting one is not counted. -/
def run (code : List Byte) (e : Env) : Nat → Mach → Beh
  | 0, _ => { ev := [], lk := [], cost := 0, out := .fuel }
  | n + 1, m =>
    let mark : Lk := .step [m.pc]
    match step code e m with
    | .next l m' =>
      let r := run code e n m'
      { r with cost := 1 + r.cost, lk := mark :: (l ++ r.lk) }
    | .exit w => { ev := [retEv w], lk := [mark], cost := 1, out := .done }
    | .fault l => { ev := [], lk := mark :: l, cost := 0, out := .abort }

/-- The machine at entry: code, then the data segment's bytes, then whatever the environment has. -/
def init (code : List Byte) (data : Nat → Byte) (e : Env) : Mach where
  pc := codeBase
  x := e.reg
  mem := fun a =>
    if inCode code a then code.getD (a - codeBase) (byteOf 0)
    else if inData a then data (a - dataBase)
    else e.mem a

/-- How many bytes of the data segment hold input. -/
def inBytes : Nat := 8 * 64

/-- **RV64, the slice's subset.** `P` marks secret input words, by position. -/
def rvLang (P : Nat → Bool) : Lang where
  Prog  := List Byte
  In    := (Nat → Byte) × Env
  lowIn i i' := ∀ off, P (off / 8) = false → i.1 off = i'.1 off
  run n c i := run c i.2 n (init c i.1 i.2)
  Adm i := ∀ off, inBytes ≤ off → i.1 off = byteOf 0

/-! ## Lawful -/

def Ext (a b : Beh) : Prop :=
  (a.out ≠ .fuel → a = b) ∧ a.ev <+: b.ev ∧ a.lk <+: b.lk ∧ a.cost ≤ b.cost

theorem run_ext (c : List Byte) (e : Env) : ∀ (n n' : Nat) (m : Mach), n ≤ n' →
    Ext (run c e n m) (run c e n' m) := by
  intro n
  induction n with
  | zero =>
    intro n' m _
    exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ k ih =>
    intro n' m hle
    obtain ⟨k', rfl⟩ : ∃ k', n' = k' + 1 := ⟨n' - 1, by omega⟩
    have hk : k ≤ k' := by omega
    simp only [run]
    cases step c e m with
    | next l m' =>
      obtain ⟨h1, h2, ⟨t, ht⟩, h4⟩ := ih k' m' hk
      refine ⟨fun hf => ?_, h2, ⟨t, ?_⟩, ?_⟩
      · simp only at hf ⊢; rw [h1 hf]
      · simp [← ht]
      · simp only; omega
    | exit w => exact ⟨fun _ => rfl, List.prefix_refl _, List.prefix_refl _, Nat.le_refl _⟩
    | fault l => exact ⟨fun _ => rfl, List.prefix_refl _, List.prefix_refl _, Nat.le_refl _⟩

theorem run_diverge (c : List Byte) (e : Env) : ∀ (n : Nat) (m : Mach),
    (run c e n m).out = .fuel → n ≤ (run c e n m).cost := by
  intro n
  induction n with
  | zero => intro _ _; exact Nat.zero_le _
  | succ k ih =>
    intro m hf
    simp only [run] at hf ⊢
    revert hf
    cases step c e m with
    | next l m' =>
      intro hf
      simp only at hf ⊢
      have := ih m' hf; omega
    | exit w => intro hf; simp at hf
    | fault l => intro hf; simp at hf

theorem rvLang_lawful (P : Nat → Bool) : (rvLang P).Lawful where
  ev_mono c i n n' h := (run_ext c i.2 n n' _ h).2.1
  lk_mono c i n n' h := (run_ext c i.2 n n' _ h).2.2.1
  cost_mono c i n n' h := (run_ext c i.2 n n' _ h).2.2.2
  stable c i n n' h hf := ((run_ext c i.2 n n' _ h).1 hf).symm
  diverge c := ⟨0, fun n i h => run_diverge c i.2 n _ h⟩

/-! ## The image -/

/-- A static RV64 ELF with these two segments. Trust base: the loader places them as `init` says. -/
def elf (body data : List Byte) : List Byte :=
  let cbase := 0x10000
  let hdr := 64 + 2 * 56
  let csize := hdr + body.length
  let ident : List Byte := ([0x7f, 0x45, 0x4c, 0x46, 2, 1, 1] : List Nat).map byteOf ++ List.replicate 9 (byteOf 0)
  let head := ident ++ le 2 2 ++ le 2 243 ++ le 4 1 ++ le 8 (cbase + hdr) ++ le 8 64 ++ le 8 0 ++ le 4 0
    ++ le 2 64 ++ le 2 56 ++ le 2 2 ++ le 2 64 ++ le 2 0 ++ le 2 0
    ++ le 4 1 ++ le 4 5 ++ le 8 0 ++ le 8 cbase ++ le 8 cbase ++ le 8 csize ++ le 8 csize ++ le 8 0x1000
    ++ le 4 1 ++ le 4 6 ++ le 8 0x1000 ++ le 8 dataBase ++ le 8 dataBase ++ le 8 data.length ++ le 8 dataSize
    ++ le 8 0x1000
    ++ body
  head ++ List.replicate (0x1000 - head.length) (byteOf 0) ++ data

/-- The entry address is where `init` starts. -/
theorem elf_entry : 0x10000 + (64 + 2 * 56) = codeBase := by decide

/-! ## Witnesses -/

/-- An environment with nothing mapped and every register zero. -/
def env0 : Env where
  reg _ := W64.ofNat 0
  mem _ := byteOf 0
  rd _ := false
  wr _ := false

abbrev a0 := 10
abbrev a7 := 17
abbrev t0 := 5
abbrev t2 := 7

/-- Input word `v` at position 0. -/
def word0 (v : Nat) : Nat → Byte :=
  fun off => if off < 8 then byteOf (v / 256 ^ off) else byteOf 0

/-- Read input word 0, skip one instruction if it is zero, and return it. -/
def probe : List Byte :=
  code [ .lui t2 0x20, .ld t0 t2 0, .beq t0 0 8, .addi t0 t0 1, .add a0 t0 0, .addi a7 0 93, .ecall ]

theorem probe_runs :
    (run probe env0 20 (init probe (word0 5) env0)).ev = [retEv (W64.ofNat 6)]
  ∧ (run probe env0 20 (init probe (word0 5) env0)).out = .done
  ∧ (run probe env0 20 (init probe (word0 5) env0)).cost = 7
  ∧ (run probe env0 20 (init probe (word0 0) env0)).cost = 6 := by
  decide

/-- **It leaks the address of each access**, which `rv_diff.py` cannot check, so it is stated here. -/
theorem probe_leaks_address :
    Lk.addr 0x20000 ∈ (run probe env0 20 (init probe (word0 5) env0)).lk := by
  decide

/-- **The model sees a secret branch**, so `rel` on it is not vacuous. -/
theorem probe_leaks : ¬ Cert.rel (rvLang (fun k => k == 0)) probe := by
  intro h
  have hl : (rvLang (fun k => k == 0)).lowIn (word0 5, env0) (word0 0, env0) := by
    intro off hoff
    have h8 : ¬ off < 8 := by
      intro hlt
      have : off / 8 = 0 := Nat.div_eq_of_lt hlt
      simp [this] at hoff
    show word0 5 off = word0 0 off
    simp [word0, h8]
  have ha : ∀ v, (rvLang (fun k => k == 0)).Adm (word0 v, env0) := by
    intro v off hoff
    have : inBytes = 512 := rfl
    have h8 : ¬ off < 8 := by omega
    show word0 v off = _
    simp [word0, h8]
  have := h 20 _ _ (ha 5) (ha 0) hl
  revert this; decide

/-- A compressed instruction is outside the model: it aborts here, and runs on the real machine. -/
theorem compressed_aborts :
    (run (le 2 0x4515 ++ le 2 0) env0 5 (init (le 2 0x4515 ++ le 2 0) (word0 0) env0)).out = .abort := by
  decide

/-- The decoder inverts the encoder on these. Step 7 proves it for every instruction the compiler emits. -/
theorem decode_encode_samples :
    decode (encode (.addi 10 0 (-2048))) = some (.addi 10 0 (-2048))
  ∧ decode (encode (.ld 5 7 2047)) = some (.ld 5 7 2047)
  ∧ decode (encode (.sd 5 2 (-8))) = some (.sd 5 2 (-8))
  ∧ decode (encode (.beq 6 0 (-4096))) = some (.beq 6 0 (-4096))
  ∧ decode (encode (.beq 6 0 4094)) = some (.beq 6 0 4094)
  ∧ decode (encode (.lui 2 0xfffff)) = some (.lui 2 0xfffff)
  ∧ decode (encode (.andi 9 8 63)) = some (.andi 9 8 63)
  ∧ decode (encode (.andi 9 8 (-1))) = some (.andi 9 8 (-1))
  ∧ decode (encode .ecall) = some .ecall := by
  decide

end LCore.Slice.Rv
