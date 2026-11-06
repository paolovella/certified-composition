/-
  VS-1 step 6: slots to machine bytes. One source step becomes many instructions, and the machine has an environment.

  **The one equation.** At every fuel, a run of the compiled bytes shows a list of micro-steps, each a PC and the addresses
  it touches, played up to that fuel, then the exit (`run_eq`). The list is computed from the slots alone, so the machine's
  environment cannot appear in it. Two runs whose source leakage agrees have equal lists (`walk_same`). That is `det`.

  **A simplification, recorded.** `t.fuel` is a constant: the fuel at which the source has finished. It is sound here because
  the slice has no loops, and a language with loops cannot do it.

  **`comp` refuses** large literals, high slots, deep expressions and code over 3 KB.
-/
import LCore.Slice.Slots

namespace LCore.Slice.Lower

open Rv Slots

/-! ## Decoding what the compiler emits -/

/-- An instruction the decoder gets back, and whose word fits 32 bits. -/
def Good (i : Insn) : Prop := decode (encode i) = some i ∧ encode i < 4294967296

theorem sext_small {n v : Nat} (h : v < 2 ^ (n - 1)) : sext n v = Int.ofNat v := by
  simp only [sext]
  rw [if_neg (by omega)]

theorem bits_ofNat (i n : Nat) (h : i < 2 ^ n) : bits (Int.ofNat i) n = i := by
  simp only [bits]
  have hp : ((2 ^ n : Nat) : Int) = (2 ^ n : Int) := by simp
  rw [← hp]
  show ((i : Int) % ((2 ^ n : Nat) : Int)).toNat = i
  rw [← Int.natCast_emod, Nat.mod_eq_of_lt h]
  simp

theorem good_lui {rd imm : Nat} (hr : rd < 32) (hi : imm < 1048576) : Good (.lui rd imm) := by
  have hw : encode (.lui rd imm) = imm * 4096 + rd * 128 + 0x37 := rfl
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  have h1 : (imm * 4096 + rd * 128 + 0x37) % 128 = 0x37 := by omega
  have h2 : rdOf (imm * 4096 + rd * 128 + 0x37) = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : (imm * 4096 + rd * 128 + 0x37) / 2 ^ 12 = imm := by simp only [Nat.reducePow]; omega
  simp only [decode, h1, h2, h3]

theorem good_addi {rd rs i : Nat} (hd : rd < 32) (hs : rs < 32) (hi : i < 2048) :
    Good (.addi rd rs (Int.ofNat i)) := by
  have hw : encode (.addi rd rs (Int.ofNat i)) = i * 1048576 + rs * 32768 + rd * 128 + 0x13 := by
    show bits (Int.ofNat i) 12 * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13 = _
    rw [bits_ofNat i 12 (by simp only [Nat.reducePow]; omega)]
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : i * 1048576 + rs * 32768 + rd * 128 + 0x13 = W
  have h1 : W % 128 = 0x13 := by omega
  have h2 : rdOf W = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : rs1Of W = rs := by simp only [rs1Of, Nat.reducePow]; omega
  have h4 : f3Of W = 0 := by simp only [f3Of, Nat.reducePow]; omega
  have h5 : W / 2 ^ 20 = i := by simp only [Nat.reducePow]; omega
  have h6 : sext 12 i = Int.ofNat i := sext_small (by show i < 2048; omega)
  simp only [decode, h1, h2, h3, h4, h5, h6, ↓reduceIte]

/-- **A negative immediate**: `addi` sign-extends, so a literal near `2^64` is one instruction. -/
theorem good_addi_neg {rd rs i : Nat} (hd : rd < 32) (hs : rs < 32) (h0 : 0 < i) (hi : i ≤ 2048) :
    Good (.addi rd rs (-(Int.ofNat i))) := by
  obtain ⟨v, hv, hv1, hv2⟩ : ∃ v, v = 4096 - i ∧ 2048 ≤ v ∧ v < 4096 := ⟨_, rfl, by omega, by omega⟩
  have hbits : bits (-(Int.ofNat i)) 12 = v := by
    simp only [bits, Nat.reducePow]
    have : (-(Int.ofNat i)) % ((2 : Int) ^ 12) = Int.ofNat v := by
      have hp : ((2 : Int) ^ 12) = 4096 := by decide
      rw [hp]
      show (-(i : Int)) % 4096 = (v : Int)
      omega
    rw [this]; rfl
  have hw : encode (.addi rd rs (-(Int.ofNat i))) = v * 1048576 + rs * 32768 + rd * 128 + 0x13 := by
    show bits (-(Int.ofNat i)) 12 * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13 = _
    rw [hbits]
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : v * 1048576 + rs * 32768 + rd * 128 + 0x13 = W
  have h1 : W % 128 = 0x13 := by omega
  have h2 : rdOf W = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : rs1Of W = rs := by simp only [rs1Of, Nat.reducePow]; omega
  have h4 : f3Of W = 0 := by simp only [f3Of, Nat.reducePow]; omega
  have h5 : W / 2 ^ 20 = v := by simp only [Nat.reducePow]; omega
  have h6 : sext 12 v = -(Int.ofNat i) := by
    simp only [sext]
    rw [if_pos (by simp only [Nat.reducePow, Nat.add_one_sub_one]; omega)]
    show ((v : Int) - ((2 ^ 12 : Nat) : Int)) = -(i : Int)
    simp only [Nat.reducePow]
    omega
  simp only [decode, h1, h2, h3, h4, h5, h6, ↓reduceIte]

theorem good_add {rd a b : Nat} (hd : rd < 32) (ha : a < 32) (hb : b < 32) : Good (.add rd a b) := by
  have hw : encode (.add rd a b) = b * 1048576 + a * 32768 + rd * 128 + 0x33 := rfl
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : b * 1048576 + a * 32768 + rd * 128 + 0x33 = W
  have h1 : W % 128 = 0x33 := by omega
  have h2 : rdOf W = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : rs1Of W = a := by simp only [rs1Of, Nat.reducePow]; omega
  have h4 : rs2Of W = b := by simp only [rs2Of, Nat.reducePow]; omega
  have h5 : f3Of W = 0 := by simp only [f3Of, Nat.reducePow]; omega
  have h6 : W / 2 ^ 25 = 0 := by simp only [Nat.reducePow]; omega
  simp [decode, h1, h2, h3, h4, h5, h6]

/-- **The R-type instructions RC-01 needs**, `sub`, `xor`, `or` and `and`: their encodings decode back. -/
theorem good_sub {rd a b : Nat} (hd : rd < 32) (ha : a < 32) (hb : b < 32) : Good (.sub rd a b) := by
  have hw : encode (.sub rd a b) = 32 * 33554432 + b * 1048576 + a * 32768 + rd * 128 + 0x33 := rfl
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : 32 * 33554432 + b * 1048576 + a * 32768 + rd * 128 + 0x33 = W
  have h1 : W % 128 = 0x33 := by omega
  have h2 : rdOf W = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : rs1Of W = a := by simp only [rs1Of, Nat.reducePow]; omega
  have h4 : rs2Of W = b := by simp only [rs2Of, Nat.reducePow]; omega
  have h5 : f3Of W = 0 := by simp only [f3Of, Nat.reducePow]; omega
  have h6 : W / 2 ^ 25 = 32 := by simp only [Nat.reducePow]; omega
  simp [decode, h1, h2, h3, h4, h5, h6]

theorem good_r3 {rd a b f : Nat} (hd : rd < 32) (ha : a < 32) (hb : b < 32) (hf : f < 8) :
    let W := b * 1048576 + a * 32768 + f * 4096 + rd * 128 + 0x33
    W % 128 = 0x33 ∧ rdOf W = rd ∧ rs1Of W = a ∧ rs2Of W = b ∧ f3Of W = f ∧ W / 2 ^ 25 = 0 ∧ W < 4294967296 := by
  intro W
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · simp only [W, rdOf, Nat.reducePow]; omega
  · simp only [W, rs1Of, Nat.reducePow]; omega
  · simp only [W, rs2Of, Nat.reducePow]; omega
  · simp only [W, f3Of, Nat.reducePow]; omega
  · simp only [W, Nat.reducePow]; omega

theorem good_xor {rd a b : Nat} (hd : rd < 32) (ha : a < 32) (hb : b < 32) : Good (.xor rd a b) := by
  have hw : encode (.xor rd a b) = b * 1048576 + a * 32768 + 4 * 4096 + rd * 128 + 0x33 := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := good_r3 (f := 4) hd ha hb (by omega)
  refine ⟨?_, by rw [hw]; exact h7⟩
  rw [hw]
  simp [decode, h1, h2, h3, h4, h5, h6]

theorem good_or {rd a b : Nat} (hd : rd < 32) (ha : a < 32) (hb : b < 32) : Good (.or rd a b) := by
  have hw : encode (.or rd a b) = b * 1048576 + a * 32768 + 6 * 4096 + rd * 128 + 0x33 := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := good_r3 (f := 6) hd ha hb (by omega)
  refine ⟨?_, by rw [hw]; exact h7⟩
  rw [hw]
  simp [decode, h1, h2, h3, h4, h5, h6]

theorem good_and {rd a b : Nat} (hd : rd < 32) (ha : a < 32) (hb : b < 32) : Good (.and rd a b) := by
  have hw : encode (.and rd a b) = b * 1048576 + a * 32768 + 7 * 4096 + rd * 128 + 0x33 := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := good_r3 (f := 7) hd ha hb (by omega)
  refine ⟨?_, by rw [hw]; exact h7⟩
  rw [hw]
  simp [decode, h1, h2, h3, h4, h5, h6]

/-- **`srli` by a shift below 64.** -/
theorem good_srli {rd a k : Nat} (hd : rd < 32) (ha : a < 32) (hk : k < 64) : Good (.srli rd a k) := by
  have hw : encode (.srli rd a k) = k * 1048576 + a * 32768 + 5 * 4096 + rd * 128 + 0x13 := rfl
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : k * 1048576 + a * 32768 + 5 * 4096 + rd * 128 + 0x13 = W
  have h1 : W % 128 = 0x13 := by omega
  have h2 : rdOf W = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : rs1Of W = a := by simp only [rs1Of, Nat.reducePow]; omega
  have h5 : f3Of W = 5 := by simp only [f3Of, Nat.reducePow]; omega
  have h6 : W / 2 ^ 26 = 0 := by simp only [Nat.reducePow]; omega
  have h7 : W / 2 ^ 20 % 64 = k := by simp only [Nat.reducePow]; omega
  simp [decode, h1, h2, h3, h5, h6, h7]

theorem good_ld {rd rs i : Nat} (hd : rd < 32) (hs : rs < 32) (hi : i < 2048) :
    Good (.ld rd rs (Int.ofNat i)) := by
  have hw : encode (.ld rd rs (Int.ofNat i)) = i * 1048576 + rs * 32768 + 12288 + rd * 128 + 0x03 := by
    show bits (Int.ofNat i) 12 * 2 ^ 20 + rs * 2 ^ 15 + 3 * 2 ^ 12 + rd * 2 ^ 7 + 0x03 = _
    rw [bits_ofNat i 12 (by simp only [Nat.reducePow]; omega)]
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : i * 1048576 + rs * 32768 + 12288 + rd * 128 + 0x03 = W
  have h1 : W % 128 = 0x03 := by omega
  have h2 : rdOf W = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : rs1Of W = rs := by simp only [rs1Of, Nat.reducePow]; omega
  have h4 : f3Of W = 3 := by simp only [f3Of, Nat.reducePow]; omega
  have h5 : W / 2 ^ 20 = i := by simp only [Nat.reducePow]; omega
  have h6 : sext 12 i = Int.ofNat i := sext_small (by show i < 2048; omega)
  simp only [decode, h1, h2, h3, h4, h5, h6, ↓reduceIte]

/-- A field of a word, which `omega` cannot always find alone in a sum this wide. -/
theorem div_field {W k : Nat} (a b : Nat) (h : W = a * k + b) (hb : b < k) : W / k = a := by
  subst h
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem good_sd {rv rs i : Nat} (hv : rv < 32) (hs : rs < 32) (hi : i < 2048) :
    Good (.sd rv rs (Int.ofNat i)) := by
  obtain ⟨q, r, hir, hr, hq⟩ : ∃ q r, i = 32 * q + r ∧ r < 32 ∧ q < 64 :=
    ⟨i / 32, i % 32, by omega, by omega, by omega⟩
  have hq' : i / 32 = q := by omega
  have hr' : i % 32 = r := by omega
  have hw : encode (.sd rv rs (Int.ofNat i)) =
      q * 33554432 + rv * 1048576 + rs * 32768 + 12288 + r * 128 + 0x23 := by
    show (bits (Int.ofNat i) 12 / 32) * 2 ^ 25 + rv * 2 ^ 20 + rs * 2 ^ 15 + 3 * 2 ^ 12
      + (bits (Int.ofNat i) 12 % 32) * 2 ^ 7 + 0x23 = _
    rw [bits_ofNat i 12 (by simp only [Nat.reducePow]; omega), hq', hr']
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : q * 33554432 + rv * 1048576 + rs * 32768 + 12288 + r * 128 + 0x23 = W
  have h1 : W % 128 = 0x23 := by omega
  have h2 : rs2Of W = rv := by
    simp only [rs2Of, Nat.reducePow]
    rw [div_field (q * 32 + rv) (rs * 32768 + 12288 + r * 128 + 0x23) (by omega) (by omega)]; omega
  have h3 : rs1Of W = rs := by
    simp only [rs1Of, Nat.reducePow]
    rw [div_field (q * 1024 + rv * 32 + rs) (12288 + r * 128 + 0x23) (by omega) (by omega)]; omega
  have h4 : f3Of W = 3 := by
    simp only [f3Of, Nat.reducePow]
    rw [div_field (q * 8192 + rv * 256 + rs * 8 + 3) (r * 128 + 0x23) (by omega) (by omega)]; omega
  have h5 : (W / 2 ^ 25) * 32 + rdOf W = i := by
    simp only [rdOf, Nat.reducePow]
    rw [div_field q (rv * 1048576 + rs * 32768 + 12288 + r * 128 + 0x23) (by omega) (by omega),
      div_field (q * 262144 + rv * 8192 + rs * 256 + 96 + r) 0x23 (by omega) (by omega)]
    omega
  have h6 : sext 12 i = Int.ofNat i := sext_small (by show i < 2048; omega)
  simp only [decode, h1, h2, h3, h4, h5, h6, ↓reduceIte]

theorem beq_fields (h b a l t : Nat) (hl : l < 16) (ht : t < 2) :
    (h * 262144 + b * 8192 + a * 256 + l * 2 + t) % 2 = t ∧ (h * 131072 + b * 4096 + a * 128 + l) % 16 = l := by
  omega

set_option maxRecDepth 20000 in
theorem good_beq {a b i : Nat} (ha : a < 32) (hb : b < 32) (hi : i < 4096) (he : i % 2 = 0) :
    Good (.beq a b (Int.ofNat i)) := by
  obtain ⟨lo, hi', t, hir, hl, hh, ht⟩ : ∃ lo hi' t, i = 2 * lo + 32 * hi' + 2048 * t ∧ lo < 16 ∧ hi' < 64 ∧ t < 2 :=
    ⟨i / 2 % 16, i / 32 % 64, i / 2048 % 2, by omega, by omega, by omega, by omega⟩
  have e1 : i / 4096 % 2 = 0 := by omega
  have e2 : i / 32 % 64 = hi' := by omega
  have e3 : i / 2 % 16 = lo := by omega
  have e4 : i / 2048 % 2 = t := by omega
  have hw : encode (.beq a b (Int.ofNat i)) =
      hi' * 33554432 + b * 1048576 + a * 32768 + lo * 256 + t * 128 + 0x63 := by
    show (bits (Int.ofNat i) 13 / 4096 % 2) * 2 ^ 31 + (bits (Int.ofNat i) 13 / 32 % 64) * 2 ^ 25 + b * 2 ^ 20
      + a * 2 ^ 15 + (bits (Int.ofNat i) 13 / 2 % 16) * 2 ^ 8 + (bits (Int.ofNat i) 13 / 2048 % 2) * 2 ^ 7 + 0x63 = _
    rw [bits_ofNat i 13 (by simp only [Nat.reducePow]; omega), e1, e2, e3, e4]
    simp only [Nat.reducePow]
    omega
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : hi' * 33554432 + b * 1048576 + a * 32768 + lo * 256 + t * 128 + 0x63 = W
  have h1 : W % 128 = 0x63 := by omega
  have h3 : rs1Of W = a := by
    simp only [rs1Of, Nat.reducePow]
    rw [div_field (hi' * 1024 + b * 32 + a) (lo * 256 + t * 128 + 0x63) (by omega) (by omega)]; omega
  have h4 : rs2Of W = b := by
    simp only [rs2Of, Nat.reducePow]
    rw [div_field (hi' * 32 + b) (a * 32768 + lo * 256 + t * 128 + 0x63) (by omega) (by omega)]; omega
  have h5 : f3Of W = 0 := by
    simp only [f3Of, Nat.reducePow]
    rw [div_field (hi' * 8192 + b * 256 + a * 8) (lo * 256 + t * 128 + 0x63) (by omega) (by omega)]; omega
  have h6 : (W / 2 ^ 31) * 4096 + (W / 2 ^ 7 % 2) * 2048 + (W / 2 ^ 25 % 64) * 32 + (W / 2 ^ 8 % 16) * 2 = i := by
    have p31 : (2 : Nat) ^ 31 = 2147483648 := rfl
    have p7 : (2 : Nat) ^ 7 = 128 := rfl
    have p25 : (2 : Nat) ^ 25 = 33554432 := rfl
    have p8 : (2 : Nat) ^ 8 = 256 := rfl
    rw [p31, p7, p25, p8]
    have hW31 : W < 2147483648 := by omega
    rw [Nat.div_eq_of_lt hW31,
      div_field (hi' * 262144 + b * 8192 + a * 256 + lo * 2 + t) 0x63 (by omega) (by omega),
      div_field hi' (b * 1048576 + a * 32768 + lo * 256 + t * 128 + 0x63) (by omega) (by omega),
      div_field (hi' * 131072 + b * 4096 + a * 128 + lo) (t * 128 + 0x63) (by omega) (by omega)]
    obtain ⟨f1, f2⟩ := beq_fields hi' b a lo t hl ht
    rw [f1, f2, Nat.mod_eq_of_lt hh]
    omega
  have h7 : sext 13 i = Int.ofNat i := sext_small (by show i < 4096; omega)
  simp only [decode, h1, h3, h4, h5, h6, h7, ↓reduceIte]

theorem good_ecall : Good .ecall := ⟨rfl, by decide⟩

/-! ## Fetching from the code -/

/-- The instruction at a PC. -/
def fetchI (C : List Byte) (pc : Nat) : Option Insn := (fetch C pc).bind decode

theorem gD_left {α} {a b : List α} {j : Nat} (d : α) (h : j < a.length) : (a ++ b).getD j d = a.getD j d := by
  simp [List.getD, List.getElem?_append_left h]

theorem gD_right {α} {a b : List α} {j : Nat} (d : α) (h : a.length ≤ j) :
    (a ++ b).getD j d = b.getD (j - a.length) d := by
  simp [List.getD, List.getElem?_append_right h]

theorem gD_mem {α} {L : List α} {j : Nat} (d : α) (h : j < L.length) : L.getD j d ∈ L := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem code_getD : ∀ (L : List Insn) (j i : Nat), j < L.length → i < 4 →
    (code L).getD (4 * j + i) (byteOf 0) = byteOf (encode (L.getD j .ecall) / 256 ^ i)
  | [], _, _, h, _ => by cases h
  | x :: xs, j, i, hj, hi => by
    have hl : (le 4 (encode x)).length = 4 := by simp [le]
    have hc : code (x :: xs) = le 4 (encode x) ++ code xs := by simp [code]
    rw [hc]
    cases j with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      rw [gD_left _ (by omega)]
      have hr : List.range 4 = [0, 1, 2, 3] := rfl
      have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl <;> simp [le, hr]
    | succ j =>
      rw [gD_right _ (by omega), hl]
      rw [show 4 * (j + 1) + i - 4 = 4 * j + i by omega]
      simpa using code_getD xs j i (by simpa using hj) hi

theorem code_length (L : List Insn) : (code L).length = 4 * L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hc : code (x :: xs) = le 4 (encode x) ++ code xs := by simp [code]
    rw [hc, List.length_append, ih]
    simp [le]; omega

theorem word_of_bytes (w : Nat) (h : w < 4294967296) :
    (byteOf (w / 1)).val + 256 * ((byteOf (w / 256)).val + 256 * ((byteOf (w / 65536)).val
      + 256 * ((byteOf (w / 16777216)).val + 256 * 0))) = w := by
  simp only [byteOf]
  omega

/-- **Every good instruction in the code is what fetching and decoding gives.** -/
theorem fetchI_code {L : List Insn} (hg : ∀ i ∈ L, Good i) {j : Nat} (hj : j < L.length) :
    fetchI (code L) (codeBase + 4 * j) = some (L.getD j .ecall) := by
  have hmem : L.getD j .ecall ∈ L := gD_mem _ hj
  obtain ⟨hd, hw⟩ := hg _ hmem
  have hlen := code_length L
  have hf : fetch (code L) (codeBase + 4 * j) = some (encode (L.getD j .ecall)) := by
    have hcb : codeBase = 0x100b0 := rfl
    simp only [fetch]
    rw [ite_eq_left (by omega)]
    congr 1
    have hsub : codeBase + 4 * j - codeBase = 4 * j := by omega
    rw [hsub]
    have hr : List.range 4 = [0, 1, 2, 3] := rfl
    rw [hr]
    simp only [List.foldr]
    have h0 := code_getD L j 0 hj (by omega)
    have h1 := code_getD L j 1 hj (by omega)
    have h2 := code_getD L j 2 hj (by omega)
    have h3 := code_getD L j 3 hj (by omega)
    rw [Nat.add_zero] at h0 ⊢
    rw [h0, h1, h2, h3]
    simpa using word_of_bytes _ hw
  simp only [fetchI, hf, Option.bind_some]
  exact hd

/-! ## The code -/

def wordsMax : Nat := 256

/-- The immediate for a literal: a word near `2^64` is a negative number, which `addi` sign-extends. VS-2 step 6: without this, a compiled loop could not count down. -/
def litImm (w : W64) : Int :=
  if w.val < 2048 then Int.ofNat w.val else -(Int.ofNat (18446744073709551616 - w.val))

def genE : SExpr → Nat → List Insn
  | .lit w, d => [.addi (8 + d) 0 (litImm w)]
  | .slot n, d => [.ld (8 + d) 7 (Int.ofNat (8 * n))]
  | .add a b, d => genE a d ++ genE b (d + 1) ++ [.add (8 + d) (8 + d) (8 + d + 1)]

def sE : SExpr → Nat
  | .lit _ | .slot _ => 1
  | .add a b => sE a + sE b + 1

def sC : SCmd → Nat
  | .skip => 1
  | .set _ e => sE e + 1
  | .seq a b => sC a + sC b
  | .ite e a b => sE e + 1 + sC a + 1 + sC b

def genC : SCmd → List Insn
  | .skip => [.addi 0 0 (Int.ofNat 0)]
  | .set n e => genE e 0 ++ [.sd 8 7 (Int.ofNat (8 * n))]
  | .seq a b => genC a ++ genC b
  | .ite e a b =>
    genE e 0 ++ [.beq 8 0 (Int.ofNat (4 * (sC a + 2)))] ++ genC a ++ [.beq 0 0 (Int.ofNat (4 * (sC b + 1)))] ++ genC b

/-- Does this fit the instructions: small literals, low slots, enough registers? -/
def okE : SExpr → Nat → Bool
  | .lit w, d => (decide (w.val < 2048) || decide (18446744073709549568 ≤ w.val)) && decide (d < 24)
  | .slot n, d => decide (n < wordsMax) && decide (d < 24)
  | .add a b, d => okE a d && okE b (d + 1) && decide (d + 1 < 24)

def okC : SCmd → Bool
  | .skip => true
  | .set n e => decide (n < wordsMax) && okE e 0
  | .seq a b => okC a && okC b
  | .ite e a b => okE e 0 && okC a && okC b && decide (sC a + 2 < 1024) && decide (sC b + 1 < 1024)

theorem genE_length : ∀ (e : SExpr) (d : Nat), (genE e d).length = sE e
  | .lit _, _ | .slot _, _ => rfl
  | .add a b, d => by simp only [genE, sE, List.length_append, genE_length a, genE_length b]; rfl

theorem genC_length : ∀ c : SCmd, (genC c).length = sC c
  | .skip => rfl
  | .set n e => by simp only [genC, sC, List.length_append, genE_length]; rfl
  | .seq a b => by simp only [genC, sC, List.length_append, genC_length a, genC_length b]
  | .ite e a b => by
    simp only [genC, sC, List.length_append, genE_length, genC_length a, genC_length b]; rfl

theorem genE_good : ∀ (e : SExpr) (d : Nat), okE e d = true → ∀ i ∈ genE e d, Good i
  | .lit w, d, h, i, hi => by
    simp only [okE, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [genE, List.mem_singleton] at hi
    subst hi
    have hw := w.isLt
    simp only [litImm]
    split
    · exact good_addi (by omega) (by omega) (by assumption)
    · exact good_addi_neg (by omega) (by omega) (by simp only [Nat.reducePow] at hw; omega) (by omega)
  | .slot n, d, h, i, hi => by
    simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at h
    have hm : wordsMax = 256 := rfl
    simp only [genE, List.mem_singleton] at hi
    subst hi; exact good_ld (by omega) (by omega) (by omega)
  | .add a b, d, h, i, hi => by
    simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [genE, List.mem_append, List.mem_singleton] at hi
    rcases hi with (hi | hi) | hi
    · exact genE_good a d h.1.1 i hi
    · exact genE_good b (d + 1) h.1.2 i hi
    · subst hi; exact good_add (by omega) (by omega) (by omega)

theorem genC_good : ∀ c : SCmd, okC c = true → ∀ i ∈ genC c, Good i
  | .skip, _, i, hi => by
    simp only [genC, List.mem_singleton] at hi
    subst hi; exact good_addi (by omega) (by omega) (by omega)
  | .set n e, h, i, hi => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h
    have hm : wordsMax = 256 := rfl
    simp only [genC, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi
    · exact genE_good e 0 h.2 i hi
    · subst hi; exact good_sd (by omega) (by omega) (by omega)
  | .seq a b, h, i, hi => by
    simp only [okC, Bool.and_eq_true] at h
    simp only [genC, List.mem_append] at hi
    rcases hi with hi | hi
    · exact genC_good a h.1 i hi
    · exact genC_good b h.2 i hi
  | .ite e a b, h, i, hi => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [genC, List.mem_append, List.mem_singleton] at hi
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rcases hi with (((hi | hi) | hi) | hi) | hi
    · exact genE_good e 0 h1 i hi
    · subst hi; exact good_beq (by omega) (by omega) (by omega) (by omega)
    · exact genC_good a h2 i hi
    · subst hi; exact good_beq (by omega) (by omega) (by omega) (by omega)
    · exact genC_good b h3 i hi

/-! ## A run as played micro-steps -/

abbrev Micro := Nat × List Lk

def tickM (x : Micro) (r : Beh) : Beh :=
  { r with cost := 1 + r.cost, lk := .step [x.1] :: (x.2 ++ r.lk) }

def fuelB : Beh := { ev := [], lk := [], cost := 0, out := .fuel }

/-- Play micro-steps up to the fuel, then carry on with `F`. -/
def playApp : List Micro → (Nat → Beh) → Nat → Beh
  | [], F, n => F n
  | _ :: _, _, 0 => fuelB
  | x :: c, F, n + 1 => tickM x (playApp c F n)

theorem playApp_append : ∀ (a b : List Micro) (F : Nat → Beh) (n : Nat),
    playApp (a ++ b) F n = playApp a (playApp b F) n
  | [], _, _, _ => rfl
  | _ :: _, _, _, 0 => rfl
  | x :: a, b, F, n + 1 => by
    show tickM x (playApp (a ++ b) F n) = tickM x (playApp a (playApp b F) n)
    rw [playApp_append a b F n]

/-- From `m` the machine plays `c` and arrives at `m'`, at every fuel. -/
def Exec (C : List Byte) (e : Env) (c : List Micro) (m m' : Mach) : Prop :=
  ∀ n, Rv.run C e n m = playApp c (fun k => Rv.run C e k m') n

theorem Exec.nil (C : List Byte) (e : Env) (m : Mach) : Exec C e [] m m := fun _ => rfl

theorem Exec.trans {C : List Byte} {e : Env} {a b : List Micro} {m m₁ m₂ : Mach}
    (h₁ : Exec C e a m m₁) (h₂ : Exec C e b m₁ m₂) : Exec C e (a ++ b) m m₂ := by
  intro n
  rw [playApp_append, h₁ n]
  have : (fun k => Rv.run C e k m₁) = playApp b (fun k => Rv.run C e k m₂) := funext h₂
  rw [this]

theorem Exec.step {C : List Byte} {e : Env} {m m' : Mach} {l : List Lk}
    (h : Rv.step C e m = .next l m') : Exec C e [(m.pc, l)] m m' := by
  intro n
  cases n with
  | zero => rfl
  | succ k =>
    simp only [Rv.run, h]
    rfl

theorem Exec.stepAt {C : List Byte} {e : Env} {m m' : Mach} {l : List Lk} {q : Nat}
    (h : Rv.step C e m = .next l m') (hq : m.pc = q) : Exec C e [(q, l)] m m' := by
  subst hq; exact Exec.step h

/-! ## Instructions, as steps -/

theorem fetchI_parts {C : List Byte} {pc : Nat} {i : Insn} (h : fetchI C pc = some i) :
    ∃ w, fetch C pc = some w ∧ decode w = some i := by
  simp only [fetchI, Option.bind_eq_some_iff] at h
  exact h

theorem wordOfInt_val (v : Nat) (h : v < 18446744073709551616) : (wordOfInt (Int.ofNat v)).val = v := by
  have : ((Int.ofNat v) % (2 ^ 64 : Int)).toNat = v := by
    have hp : ((2 : Int) ^ 64) = ((18446744073709551616 : Nat) : Int) := by decide
    rw [hp]
    show ((v : Int) % ((18446744073709551616 : Nat) : Int)).toNat = v
    rw [← Int.natCast_emod, Nat.mod_eq_of_lt h]
    simp
  simp only [wordOfInt, W64.ofNat, this]
  exact Nat.mod_eq_of_lt h

theorem addImm_val (a : W64) (v : Nat) (h : a.val + v < 18446744073709551616) :
    addImm a (Int.ofNat v) = a.val + v := by
  simp only [addImm, W64.add, W64.ofNat]
  rw [wordOfInt_val v (by omega)]
  exact Nat.mod_eq_of_lt h

theorem get_zero (m : Mach) : m.get 0 = W64.ofNat 0 := rfl

theorem get_set {m : Mach} {pc r y : Nat} {v : W64} (hr : r ≠ 0) :
    ({ m with pc := pc, x := m.set r v } : Mach).get y = if y = r then v else m.get y := by
  by_cases hy0 : y = 0
  · subst hy0
    simp [Mach.get, Ne.symm hr]
  · by_cases hyr : y = r
    · simp [Mach.get, Mach.set, hy0, hyr, hr]
    · simp [Mach.get, Mach.set, hy0, hyr, hr]

/-! ## Memory -/

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem store8_in (mem : Nat → Byte) (a : Nat) (v : W64) (i : Nat) (hi : i < 8)
    (ha : a + 8 < 18446744073709551616) :
    store8 mem a v (a + i) = byteOf (v.val / 256 ^ i) := by
  have e : ∀ k, k < 8 → (a + k) % 18446744073709551616 = a + k := fun k hk => Nat.mod_eq_of_lt (by omega)
  have e0 : a % 18446744073709551616 = a := Nat.mod_eq_of_lt (by omega)
  have l : ∀ k, 0 < k → (a == a + k) = false := by intro k hk; simp; omega
  have r : ∀ k, 0 < k → (a + k == a) = false := by intro k hk; simp; omega
  have c : ∀ j k, j ≠ k → (a + j == a + k) = false := by intro j k h; simp [h]
  simp only [store8, range8]
  have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [List.find?, e0, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
      e 6 (by omega), e 7 (by omega), l, r, c]

theorem store8_out (mem : Nat → Byte) (a : Nat) (v : W64) (b : Nat)
    (ha : a + 8 < 18446744073709551616) (hb : b < a ∨ a + 8 ≤ b) : store8 mem a v b = mem b := by
  have e : ∀ k, k < 8 → (a + k) % 18446744073709551616 = a + k := fun k hk => Nat.mod_eq_of_lt (by omega)
  have e0 : a % 18446744073709551616 = a := Nat.mod_eq_of_lt (by omega)
  have n : ∀ k, k < 8 → (a + k == b) = false := by intro k hk; simp; omega
  have n0 : (a == b) = false := by simp; omega
  simp only [store8, range8]
  simp [List.find?, e0, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega), n0, n 1 (by omega), n 2 (by omega), n 3 (by omega), n 4 (by omega),
    n 5 (by omega), n 6 (by omega), n 7 (by omega)]

theorem load8_val (m : Mach) (a : Nat) (ha : a + 8 < 18446744073709551616) :
    load8 m a = W64.ofNat ((m.mem a).val + 256 * ((m.mem (a + 1)).val + 256 * ((m.mem (a + 2)).val
      + 256 * ((m.mem (a + 3)).val + 256 * ((m.mem (a + 4)).val + 256 * ((m.mem (a + 5)).val
      + 256 * ((m.mem (a + 6)).val + 256 * ((m.mem (a + 7)).val + 256 * 0)))))))) := by
  have e : ∀ k, k < 8 → (a + k) % 2 ^ 64 = a + k := fun k hk =>
    Nat.mod_eq_of_lt (by show a + k < 18446744073709551616; omega)
  simp only [load8, range8, List.foldr]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega), Nat.add_zero]

/-- A word's address. -/
def slotAddr (n : Nat) : Nat := dataBase + 8 * n

/-- A store to one word leaves another word's load alone. -/
theorem load8_store_other (m : Mach) (a b : Nat) (v : W64) (ha : a + 8 < 18446744073709551616)
    (hb : b + 8 < 18446744073709551616) (hd : a + 8 ≤ b ∨ b + 8 ≤ a) :
    load8 { m with mem := store8 m.mem a v } b = load8 m b := by
  rw [load8_val _ b hb, load8_val _ b hb]
  simp only
  rw [store8_out _ a v b ha (by omega), store8_out _ a v (b + 1) ha (by omega),
    store8_out _ a v (b + 2) ha (by omega), store8_out _ a v (b + 3) ha (by omega),
    store8_out _ a v (b + 4) ha (by omega), store8_out _ a v (b + 5) ha (by omega),
    store8_out _ a v (b + 6) ha (by omega), store8_out _ a v (b + 7) ha (by omega)]

/-- A load after a store gets the word back. -/
theorem load8_store_same (m : Mach) (a : Nat) (v : W64) (ha : a + 8 < 18446744073709551616) :
    load8 { m with mem := store8 m.mem a v } a = v := by
  rw [load8_val _ a ha]
  simp only
  have h0 := store8_in m.mem a v 0 (by omega) ha
  rw [Nat.add_zero] at h0
  rw [h0, store8_in m.mem a v 1 (by omega) ha, store8_in m.mem a v 2 (by omega) ha,
    store8_in m.mem a v 3 (by omega) ha, store8_in m.mem a v 4 (by omega) ha,
    store8_in m.mem a v 5 (by omega) ha, store8_in m.mem a v 6 (by omega) ha,
    store8_in m.mem a v 7 (by omega) ha]
  apply Fin.ext
  have hv : v.val < 18446744073709551616 := v.isLt
  simp only [W64.ofNat, byteOf, Nat.reducePow]
  have := bytes_sum _ hv
  have h1 : v.val / 1 = v.val := Nat.div_one _
  rw [h1]
  omega

/-- The machine's invariant: the base register, and each slot's word in memory. -/
def Inv (m : Mach) (t : Slots) : Prop :=
  m.get 7 = W64.ofNat dataBase ∧ ∀ n, n < wordsMax → load8 m (slotAddr n) = t n

theorem inData_slot (n i : Nat) (hn : n < wordsMax) (hi : i < 8) : inData (slotAddr n + i) = true := by
  have hn' : n < 256 := hn
  have hd : dataBase = 131072 := rfl
  have hs : dataSize = 4096 := rfl
  have h1 : dataBase ≤ slotAddr n + i := by simp only [slotAddr]; omega
  have h2 : slotAddr n + i < dataBase + dataSize := by simp only [slotAddr]; omega
  simp [inData, h1, h2]

theorem addrs8_slot {n : Nat} (hn : n < wordsMax) {x : Nat} (hx : x ∈ addrs8 (slotAddr n)) :
    inData x = true := by
  simp only [addrs8, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have : wordsMax = 256 := rfl
  have hl : slotAddr n + i < 18446744073709551616 := by simp only [slotAddr, dataBase]; omega
  rw [Nat.mod_eq_of_lt (by show slotAddr n + i < 18446744073709551616; exact hl)]
  exact inData_slot n i hn hi

/-! ## Expressions -/

def mE : SExpr → Nat → List Micro
  | .lit _, pc => [(pc, [])]
  | .slot n, pc => [(pc, [.addr (Int.ofNat (slotAddr n))])]
  | .add a b, pc => mE a pc ++ mE b (pc + 4 * sE a) ++ [(pc + 4 * (sE a + sE b), [])]

/-- The list of instructions at `pc`. -/
def At (C : List Byte) (pc : Nat) (L : List Insn) : Prop :=
  ∀ j, j < L.length → fetchI C (pc + 4 * j) = some (L.getD j .ecall)

theorem At.left {C : List Byte} {pc : Nat} {a b : List Insn} (h : At C pc (a ++ b)) : At C pc a := by
  intro j hj
  have := h j (by simp; omega)
  rwa [gD_left _ hj] at this

theorem At.right {C : List Byte} {pc : Nat} {a b : List Insn} (h : At C pc (a ++ b)) :
    At C (pc + 4 * a.length) b := by
  intro j hj
  have := h (a.length + j) (by simp; omega)
  rw [gD_right _ (by omega), Nat.add_sub_cancel_left] at this
  rw [Nat.add_assoc, ← Nat.mul_add]
  exact this

theorem At.head {C : List Byte} {pc : Nat} {i : Insn} {L : List Insn} (h : At C pc (i :: L)) :
    fetchI C pc = some i := h 0 (by simp)

/-- A literal's immediate, added to `x0`, is the literal. -/
theorem litImm_value (m : Mach) (w : W64) (h : w.val < 2048 ∨ 18446744073709549568 ≤ w.val) :
    W64.ofNat (addImm (m.get 0) (litImm w)) = w := by
  have hlt : w.val < 18446744073709551616 := w.isLt
  simp only [litImm]
  split
  · apply Fin.ext
    rw [get_zero, addImm_val _ _ (by simp only [W64.ofNat]; omega)]
    simp only [W64.ofNat, Nat.reducePow]
    omega
  · rename_i hge
    obtain ⟨i, hi, h0⟩ : ∃ i, i = 18446744073709551616 - w.val ∧ 0 < i := ⟨_, rfl, by omega⟩
    rw [← hi]
    have hm : (-(Int.ofNat i)) % ((2 : Int) ^ 64) = Int.ofNat w.val := by
      have hp : ((2 : Int) ^ 64) = 18446744073709551616 := by decide
      rw [hp]
      show (-(i : Int)) % 18446744073709551616 = (w.val : Int)
      omega
    apply Fin.ext
    rw [get_zero]
    simp only [addImm, W64.add, W64.ofNat, wordOfInt, hm]
    show ((0 % 2 ^ 64 + (w.val % 2 ^ 64)) % 2 ^ 64) % 2 ^ 64 = w.val
    simp only [Nat.reducePow]
    omega

/-- **An expression's code**: the value in its register, lower registers and memory untouched. -/
theorem genE_exec {C : List Byte} {en : Env} : ∀ (e : SExpr) (d : Nat) (m : Mach) (t : Slots),
    okE e d = true → Inv m t → At C m.pc (genE e d) →
    ∃ m', Exec C en (mE e m.pc) m m' ∧ m'.pc = m.pc + 4 * sE e ∧ m'.mem = m.mem ∧
      m'.get (8 + d) = evalS e t ∧ ∀ y, y < 8 + d → m'.get y = m.get y
  | .lit w, d, m, t, hok, _, hat => by
    simp only [okE, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨w', hf, hd⟩ := fetchI_parts (hat.head)
    have hs : Rv.step C en m = .next [] { m with pc := m.pc + 4, x := m.set (8 + d) w } := by
      have hv : W64.ofNat (addImm (m.get 0) (litImm w)) = w := litImm_value m w hok.1
      simp only [Rv.step, hf, hd, hv]
    refine ⟨_, Exec.step hs, rfl, rfl, ?_, ?_⟩
    · rw [get_set (by omega)]; simp [evalS]
    · intro y hy
      rw [get_set (by omega)]
      simp [show y ≠ 8 + d by omega]
  | .slot n, d, m, t, hok, hinv, hat => by
    simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨w', hf, hd⟩ := fetchI_parts (hat.head)
    have hmax : wordsMax = 256 := rfl
    have ha : addImm (m.get 7) (Int.ofNat (8 * n)) = slotAddr n := by
      rw [hinv.1, addImm_val _ _ (by simp only [W64.ofNat, dataBase]; omega)]
      simp only [W64.ofNat, dataBase, slotAddr]
    have hall : (addrs8 (slotAddr n)).all (canRead C en) = true := by
      rw [List.all_eq_true]
      intro x hx
      simp [canRead, addrs8_slot hok.1 hx]
    have hs : Rv.step C en m =
        .next [.addr (Int.ofNat (slotAddr n))]
          { m with pc := m.pc + 4, x := m.set (8 + d) (load8 m (slotAddr n)) } := by
      simp only [Rv.step, hf, hd, ha, hall, ↓reduceIte]
    refine ⟨_, Exec.step hs, rfl, rfl, ?_, ?_⟩
    · rw [get_set (by omega)]; simp [evalS, hinv.2 n hok.1]
    · intro y hy
      rw [get_set (by omega)]
      simp [show y ≠ 8 + d by omega]
  | .add a b, d, m, t, hok, hinv, hat => by
    simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hoa, hob⟩, hd24⟩ := hok
    simp only [genE] at hat
    have hab := hat.left
    have hadd := hat.right
    obtain ⟨m₁, e₁, p₁, mem₁, v₁, low₁⟩ := genE_exec a d m t hoa hinv hab.left
    have hinv₁ : Inv m₁ t := by
      refine ⟨by rw [low₁ 7 (by omega)]; exact hinv.1, fun n hn => ?_⟩
      have : load8 m₁ (slotAddr n) = load8 m (slotAddr n) := by simp only [load8, mem₁]
      rw [this]; exact hinv.2 n hn
    have hb : At C m₁.pc (genE b (d + 1)) := by
      rw [p₁, ← genE_length a d]
      exact hab.right
    obtain ⟨m₂, e₂, p₂, mem₂, v₂, low₂⟩ := genE_exec b (d + 1) m₁ t hob hinv₁ hb
    have hpc : m₂.pc = m.pc + 4 * (sE a + sE b) := by rw [p₂, p₁]; omega
    have hat3 : fetchI C m₂.pc = some (.add (8 + d) (8 + d) (8 + d + 1)) := by
      have := hadd.head
      simp only [List.length_append, genE_length] at this
      rw [hpc]
      rw [show m.pc + 4 * (sE a + sE b) = m.pc + 4 * (sE a + sE b) from rfl]
      exact this
    obtain ⟨w', hf, hd⟩ := fetchI_parts hat3
    have hs : Rv.step C en m₂ = .next [] { m₂ with pc := m₂.pc + 4, x := m₂.set (8 + d) (W64.add (m₂.get (8 + d)) (m₂.get (8 + d + 1))) } := by
      simp only [Rv.step, hf, hd]
    have e₃ := Exec.step hs
    refine ⟨_, ((e₁.trans (by rw [p₁] at e₂; exact e₂)).trans (by
      rw [hpc] at e₃
      exact e₃)), ?_, ?_, ?_, ?_⟩
    · simp only [sE]; omega
    · simp only; rw [mem₂, mem₁]
    · rw [get_set (by omega)]
      have h1 : m₂.get (8 + d) = evalS a t := by rw [low₂ (8 + d) (by omega)]; exact v₁
      have h2 : m₂.get (8 + d + 1) = evalS b t := v₂
      simp [evalS, h1, h2]
    · intro y hy
      rw [get_set (by omega)]
      simp only [show y ≠ 8 + d by omega, ↓reduceIte]
      rw [low₂ y (by omega), low₁ y hy]

/-! ## Commands: what the machine shows, computed from the slots alone -/

/-- A target frame: a command at a PC, or the jump at the end of a branch's first arm. -/
inductive TF where
  | cmd (c : SCmd) (pc : Nat)
  | jmp (pc tgt : Nat)

def pushT : SCmd → Nat → List TF → List TF
  | .seq a b, pc, k => pushT a pc (pushT b (pc + 4 * sC a) k)
  | c, pc, k => .cmd c pc :: k

def mC : SCmd → Nat
  | .skip | .set _ _ => 1
  | .seq a b => 1 + mC a + mC b
  | .ite _ a b => 2 + mC a + mC b

def mK : List TF → Nat
  | [] => 0
  | .cmd c _ :: k => mC c + mK k
  | .jmp _ _ :: k => 1 + mK k

theorem mC_pos : ∀ c, 0 < mC c
  | .skip | .set _ _ => by simp [mC]
  | .seq _ _ | .ite _ _ _ => by simp only [mC]; omega

theorem mK_push : ∀ (c : SCmd) (pc : Nat) (k : List TF), mK (pushT c pc k) ≤ mC c + mK k
  | .seq a b, pc, k => by
    have h1 := mK_push a pc (pushT b (pc + 4 * sC a) k)
    have h2 := mK_push b (pc + 4 * sC a) k
    simp only [pushT, mC]; omega
  | .skip, _, _ | .set _ _, _, _ | .ite _ _ _, _, _ => by simp [pushT, mK]

/-- **Every micro-step left, and the final slots.** Nothing here reads the machine or its environment. -/
def walk : Nat → List TF → Slots → List Micro × Slots
  | 0, _, t => ([], t)
  | _ + 1, [], t => ([], t)
  | N + 1, .jmp p _ :: k, t => ((p, []) :: (walk N k t).1, (walk N k t).2)
  | N + 1, .cmd c pc :: k, t =>
    match c with
    | .skip => ((pc, []) :: (walk N k t).1, (walk N k t).2)
    | .set n e =>
      (mE e pc ++ [(pc + 4 * sE e, [.addr (Int.ofNat (slotAddr n))])] ++ (walk N k (updS t n (evalS e t))).1,
        (walk N k (updS t n (evalS e t))).2)
    | .seq a b => walk N (pushT a pc (pushT b (pc + 4 * sC a) k)) t
    | .ite e a b =>
      if (evalS e t).val ≠ 0 then
        (mE e pc ++ [(pc + 4 * sE e, [])] ++
          (walk N (pushT a (pc + 4 * (sE e + 1)) (.jmp (pc + 4 * (sE e + 1 + sC a)) (pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)) t).1,
         (walk N (pushT a (pc + 4 * (sE e + 1)) (.jmp (pc + 4 * (sE e + 1 + sC a)) (pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)) t).2)
      else
        (mE e pc ++ [(pc + 4 * sE e, [])] ++ (walk N (pushT b (pc + 4 * (sE e + 1 + sC a + 1)) k) t).1,
         (walk N (pushT b (pc + 4 * (sE e + 1 + sC a + 1)) k) t).2)

/-- The frames' code is where they say, and they are compiled. -/
def FOk (C : List Byte) : List TF → Prop
  | [] => True
  | .cmd c pc :: k => okC c = true ∧ At C pc (genC c) ∧ FOk C k
  | .jmp p q :: k => fetchI C p = some (.beq 0 0 (Int.ofNat (q - p))) ∧ p ≤ q ∧ q - p < 4096 ∧ FOk C k

/-- The frames run in order, ending at `f`. -/
def Chain : Nat → List TF → Nat → Prop
  | pc, [], f => pc = f
  | pc, .cmd c q :: k, f => q = pc ∧ Chain (pc + 4 * sC c) k f
  | pc, .jmp p q :: k, f => p = pc ∧ Chain q k f

theorem push_fok {C : List Byte} : ∀ (c : SCmd) (pc : Nat) (k : List TF), okC c = true →
    At C pc (genC c) → FOk C k → FOk C (pushT c pc k)
  | .seq a b, pc, k, hc, hat, hk => by
    simp only [okC, Bool.and_eq_true] at hc
    simp only [genC] at hat
    have hr := hat.right
    rw [genC_length] at hr
    exact push_fok a pc _ hc.1 hat.left (push_fok b _ k hc.2 hr hk)
  | .skip, _, _, hc, hat, hk | .set _ _, _, _, hc, hat, hk | .ite _ _ _, _, _, hc, hat, hk => ⟨hc, hat, hk⟩

theorem push_chain : ∀ (c : SCmd) (pc : Nat) (k : List TF) (f : Nat), Chain (pc + 4 * sC c) k f →
    Chain pc (pushT c pc k) f
  | .seq a b, pc, k, f, h => by
    apply push_chain a pc
    apply push_chain b
    have : pc + 4 * sC a + 4 * sC b = pc + 4 * sC (.seq a b) := by simp only [sC]; omega
    rw [this]; exact h
  | .skip, _, _, _, h | .set _ _, _, _, _, h | .ite _ _ _, _, _, _, h => ⟨rfl, h⟩

theorem fetchI_bound {C : List Byte} {pc : Nat} {i : Insn} (h : fetchI C pc = some i) :
    pc + 4 ≤ codeBase + C.length := by
  obtain ⟨w, hf, _⟩ := fetchI_parts h
  simp only [fetch] at hf
  split at hf
  · rename_i hc; omega
  · cases hf

theorem Inv.mono_mem {m m' : Mach} {t : Slots} (h : Inv m t) (h7 : m'.get 7 = m.get 7) (hm : m'.mem = m.mem) :
    Inv m' t :=
  ⟨by rw [h7]; exact h.1, fun n hn => by
    have : load8 m' (slotAddr n) = load8 m (slotAddr n) := by simp only [load8, hm]
    rw [this]; exact h.2 n hn⟩

/-- **The machine plays what `walk` computes**, whatever its environment and its other registers hold. -/
theorem walk_exec {C : List Byte} {en : Env} (hC : C.length ≤ 3000) (f : Nat) :
    ∀ (N : Nat) (k : List TF) (t : Slots) (m : Mach), mK k ≤ N → FOk C k → Chain m.pc k f → Inv m t →
      ∃ m', Exec C en (walk N k t).1 m m' ∧ m'.pc = f ∧ Inv m' (walk N k t).2 := by
  intro N
  induction N with
  | zero =>
    intro k t m hN _ hch hinv
    cases k with
    | nil => exact ⟨m, Exec.nil _ _ _, hch, hinv⟩
    | cons x k =>
      exfalso
      cases x with
      | cmd c pc => have := mC_pos c; simp only [mK] at hN; omega
      | jmp p q => simp only [mK] at hN; omega
  | succ N ih =>
    intro k t m hN hok hch hinv
    cases k with
    | nil => exact ⟨m, Exec.nil _ _ _, hch, hinv⟩
    | cons x k =>
      cases x with
      | jmp p q =>
        obtain ⟨hf, hle, hlt, hok'⟩ := hok
        obtain ⟨hp, hch'⟩ := hch
        simp only [mK] at hN
        subst hp
        obtain ⟨w', hf', hd'⟩ := fetchI_parts hf
        have hb := fetchI_bound hf
        have hcb : codeBase = 0x100b0 := rfl
        have ha : addImm (W64.ofNat m.pc) (Int.ofNat (q - m.pc)) = q := by
          have hv : (W64.ofNat m.pc).val = m.pc := Nat.mod_eq_of_lt (by show m.pc < 18446744073709551616; omega)
          rw [addImm_val _ _ (by rw [hv]; omega), hv]; omega
        have hs : Rv.step C en m = .next [] { m with pc := q } := by
          simp only [Rv.step, hf', hd', ↓reduceIte, ha]
        obtain ⟨m', e', p', i'⟩ := ih k t { m with pc := q } (by omega) hok' hch' (Inv.mono_mem hinv rfl rfl)
        exact ⟨m', (Exec.step hs).trans e', p', i'⟩
      | cmd c pc =>
        obtain ⟨hoc, hat, hok'⟩ := hok
        obtain ⟨hp, hch'⟩ := hch
        subst hp
        simp only [mK] at hN
        cases c with
        | skip =>
          obtain ⟨w', hf', hd'⟩ := fetchI_parts hat.head
          have hs : Rv.step C en m = .next [] { m with pc := m.pc + 4, x := m.set 0 (W64.ofNat (addImm (m.get 0) (Int.ofNat 0))) } := by
            simp only [Rv.step, hf', hd']
          simp only [mC] at hN
          obtain ⟨m', e', p', i'⟩ := ih k t { m with pc := m.pc + 4, x := m.set 0 (W64.ofNat (addImm (m.get 0) (Int.ofNat 0))) }
            (by omega) hok' hch' (Inv.mono_mem hinv (by simp [Mach.get, Mach.set]) rfl)
          exact ⟨m', (Exec.step hs).trans e', p', i'⟩
        | set n e =>
          simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
          simp only [genC] at hat
          have hmax : wordsMax = 256 := rfl
          obtain ⟨m₁, e₁, p₁, mem₁, v₁, low₁⟩ := genE_exec (en := en) e 0 m t hoc.2 hinv hat.left
          have hsd := hat.right.head
          rw [genE_length, ← p₁] at hsd
          obtain ⟨w', hf', hd'⟩ := fetchI_parts hsd
          have h7 : m₁.get 7 = W64.ofNat dataBase := by rw [low₁ 7 (by omega)]; exact hinv.1
          have ha : addImm (m₁.get 7) (Int.ofNat (8 * n)) = slotAddr n := by
            rw [h7, addImm_val _ _ (by simp only [W64.ofNat, dataBase]; omega)]
            simp only [W64.ofNat, dataBase, slotAddr]
          have hall : (addrs8 (slotAddr n)).all (canWrite C en) = true := by
            rw [List.all_eq_true]
            intro x hx
            simp [canWrite, addrs8_slot hoc.1 hx]
          have hs : Rv.step C en m₁ = .next [.addr (Int.ofNat (slotAddr n))]
              { m₁ with pc := m₁.pc + 4, mem := store8 m₁.mem (slotAddr n) (m₁.get 8) } := by
            simp only [Rv.step, hf', hd', ha, hall, ↓reduceIte]
          have hval : m₁.get 8 = evalS e t := v₁
          have hA : ∀ j, j < wordsMax → slotAddr j + 8 < 18446744073709551616 := by
            intro j hj; simp only [slotAddr, dataBase]; omega
          have hinv' : Inv { m₁ with pc := m₁.pc + 4, mem := store8 m₁.mem (slotAddr n) (m₁.get 8) }
              (updS t n (evalS e t)) := by
            refine ⟨h7, fun j hj => ?_⟩
            by_cases hjn : j = n
            · subst hjn
              have := load8_store_same m₁ (slotAddr j) (m₁.get 8) (hA j hj)
              simp only [load8] at this ⊢
              simp only [updS, ↓reduceIte, ← hval]
              exact this
            · have hne := load8_store_other m₁ (slotAddr n) (slotAddr j) (m₁.get 8) (hA n hoc.1) (hA j hj)
                (by simp only [slotAddr]; omega)
              simp only [load8] at hne ⊢
              simp only [updS, hjn, ↓reduceIte]
              rw [hne]
              have : load8 m₁ (slotAddr j) = load8 m (slotAddr j) := by simp only [load8, mem₁]
              simp only [load8] at this
              rw [this]
              have h2 := hinv.2 j hj
              simp only [load8] at h2
              exact h2
          simp only [mC] at hN
          have hch2 : Chain (m₁.pc + 4) k f := by
            rw [p₁]
            simp only [sC] at hch'
            rw [show m.pc + 4 * sE e + 4 = m.pc + 4 * (sE e + 1) by omega]
            exact hch'
          obtain ⟨m', e', p', i'⟩ := ih k (updS t n (evalS e t)) _ (by omega) hok' hch2 hinv'
          have hx := Exec.stepAt hs p₁
          exact ⟨m', (e₁.trans hx).trans e', p', i'⟩
        | seq a b =>
          simp only [okC, Bool.and_eq_true] at hoc
          simp only [genC] at hat
          have hr := hat.right
          rw [genC_length] at hr
          have hk := mK_push a m.pc (pushT b (m.pc + 4 * sC a) k)
          have hk2 := mK_push b (m.pc + 4 * sC a) k
          simp only [mC] at hN
          exact ih _ t m (by omega)
            (push_fok a _ _ hoc.1 hat.left (push_fok b _ _ hoc.2 hr hok'))
            (push_chain a _ _ _ (push_chain b _ _ _ (by
              simp only [sC] at hch'
              rw [show m.pc + 4 * sC a + 4 * sC b = m.pc + 4 * (sC a + sC b) by omega]
              exact hch'))) hinv
        | ite e a b =>
          simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
          obtain ⟨⟨⟨⟨ho1, ho2⟩, ho3⟩, ho4⟩, ho5⟩ := hoc
          simp only [genC] at hat
          obtain ⟨m₁, e₁, p₁, mem₁, v₁, low₁⟩ := genE_exec (en := en) e 0 m t ho1 hinv hat.left.left.left.left
          have hL : ∀ {X : List Insn} {i : Insn}, (X ++ [i]).length = X.length + 1 := by intro X i; simp
          have atB := hat.left.left.left.right.head
          rw [genE_length, ← p₁] at atB
          have atA := hat.left.left.right
          simp only [List.length_append, genE_length, List.length_cons, List.length_nil, Nat.zero_add] at atA
          have atJ := hat.left.right.head
          simp only [List.length_append, genE_length, genC_length, List.length_cons, List.length_nil, Nat.zero_add] at atJ
          have atE := hat.right
          simp only [List.length_append, genE_length, genC_length, List.length_cons, List.length_nil, Nat.zero_add] at atE
          obtain ⟨w', hf', hd'⟩ := fetchI_parts atB
          have hinv₁ : Inv m₁ t := Inv.mono_mem hinv (low₁ 7 (by omega)) mem₁
          have hval : m₁.get 8 = evalS e t := v₁
          have hcb : codeBase = 0x100b0 := rfl
          have hb := fetchI_bound atB
          simp only [mC] at hN
          have hsplit : m₁.get 8 = m₁.get 0 ↔ ¬ (evalS e t).val ≠ 0 := by
            rw [hval, get_zero]
            constructor
            · intro h hne; apply hne; rw [h]; rfl
            · intro h
              apply Fin.ext
              have h0 : (evalS e t).val = 0 := by simpa using h
              rw [h0]; rfl
          by_cases hg : (evalS e t).val ≠ 0
          · have hne : m₁.get 8 ≠ m₁.get 0 := fun h => (hsplit.mp h) hg
            have hs : Rv.step C en m₁ = .next [] { m₁ with pc := m₁.pc + 4 } := by
              simp only [Rv.step, hf', hd', hne, ↓reduceIte]
            have hk := mK_push a (m.pc + 4 * (sE e + 1)) (.jmp (m.pc + 4 * (sE e + 1 + sC a)) (m.pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)
            simp only [mK] at hk
            have hfrm : FOk C (pushT a (m.pc + 4 * (sE e + 1)) (.jmp (m.pc + 4 * (sE e + 1 + sC a)) (m.pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)) := by
              refine push_fok a _ _ ho2 atA ⟨?_, by omega, by omega, hok'⟩
              rw [show m.pc + 4 * (sE e + 1 + sC a + 1 + sC b) - (m.pc + 4 * (sE e + 1 + sC a)) = 4 * (sC b + 1) by omega]
              exact atJ
            have hchn : Chain (m₁.pc + 4) (pushT a (m.pc + 4 * (sE e + 1)) (.jmp (m.pc + 4 * (sE e + 1 + sC a)) (m.pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)) f := by
              rw [p₁, show m.pc + 4 * sE e + 4 = m.pc + 4 * (sE e + 1) by omega]
              refine push_chain a _ _ _ ⟨by omega, ?_⟩
              simp only [sC] at hch'
              exact hch'
            obtain ⟨m', e', p', i'⟩ := ih _ t { m₁ with pc := m₁.pc + 4 } (by omega) hfrm hchn (Inv.mono_mem hinv₁ rfl rfl)
            have hx := Exec.stepAt hs p₁
            simp only [walk, hg, ne_eq, not_false_eq_true, ↓reduceIte]
            exact ⟨m', (e₁.trans hx).trans e', p', i'⟩
          · have heq : m₁.get 8 = m₁.get 0 := hsplit.mpr hg
            have hv : (W64.ofNat m₁.pc).val = m₁.pc := Nat.mod_eq_of_lt (by show m₁.pc < 18446744073709551616; omega)
            have ha : addImm (W64.ofNat m₁.pc) (Int.ofNat (4 * (sC a + 2))) = m₁.pc + 4 * (sC a + 2) := by
              rw [addImm_val _ _ (by rw [hv]; omega), hv]
            have hs : Rv.step C en m₁ = .next [] { m₁ with pc := m₁.pc + 4 * (sC a + 2) } := by
              simp only [Rv.step, hf', hd', heq, ↓reduceIte, ha]
            have hk := mK_push b (m.pc + 4 * (sE e + 1 + sC a + 1)) k
            have hchn : Chain (m₁.pc + 4 * (sC a + 2)) (pushT b (m.pc + 4 * (sE e + 1 + sC a + 1)) k) f := by
              rw [p₁, show m.pc + 4 * sE e + 4 * (sC a + 2) = m.pc + 4 * (sE e + 1 + sC a + 1) by omega]
              refine push_chain b _ _ _ ?_
              simp only [sC] at hch'
              rw [show m.pc + 4 * (sE e + 1 + sC a + 1) + 4 * sC b = m.pc + 4 * (sE e + 1 + sC a + 1 + sC b) by omega]
              exact hch'
            obtain ⟨m', e', p', i'⟩ := ih _ t { m₁ with pc := m₁.pc + 4 * (sC a + 2) } (by omega)
              (push_fok b _ _ ho3 atE hok') hchn (Inv.mono_mem hinv₁ rfl rfl)
            have hx := Exec.stepAt hs p₁
            simp only [walk, hg, ne_eq, ↓reduceIte]
            exact ⟨m', (e₁.trans hx).trans e', p', i'⟩

/-! ## The source shows the same path -/

/-- Source frames and target frames: the same commands, with the target's jumps in between. -/
inductive Corr : List SFrame → List TF → Prop where
  | nil : Corr [] []
  | cmd {ks : List SFrame} {k : List TF} {c : SCmd} {q : List Nat} {pc : Nat} :
      Corr ks k → Corr ((c, q) :: ks) (.cmd c pc :: k)
  | jmp {ks : List SFrame} {k : List TF} {p t : Nat} : Corr ks k → Corr ks (.jmp p t :: k)

theorem Corr.push : ∀ (c : SCmd) (q : List Nat) (pc : Nat) {ks : List SFrame} {k : List TF},
    Corr ks k → Corr (pushS c q ks) (pushT c pc k)
  | .seq a b, q, pc, _, _, h => Corr.push a _ _ (Corr.push b _ _ h)
  | .skip, _, _, _, _, h | .set _ _, _, _, _, _, h | .ite _ _ _, _, _, _, _, h => Corr.cmd h

/-- **The source finishes, returning the word `walk` ends with.** -/
theorem walk_src (ret : SExpr) : ∀ (N : Nat) (k : List TF) (ks : List SFrame) (t : Slots) (N' : Nat),
    mK k ≤ N → mK k ≤ N' → Corr ks k →
    (runS ret N' ks t).out = .done ∧ (runS ret N' ks t).ev = [retEv (evalS ret (walk N k t).2)] := by
  intro N
  induction N with
  | zero =>
    intro k ks t N' hN _ hc
    cases hc with
    | nil => cases N' <;> exact ⟨rfl, rfl⟩
    | @cmd _ _ c _ _ _ => have := mC_pos c; simp only [mK] at hN; omega
    | jmp _ => simp only [mK] at hN; omega
  | succ N ih =>
    intro k ks t N' hN hN' hc
    cases hc with
    | nil => cases N' <;> exact ⟨rfl, rfl⟩
    | jmp h =>
      simp only [mK] at hN hN'
      exact ih _ ks t N' (by omega) (by omega) h
    | @cmd ks k c q pc h =>
      simp only [mK] at hN hN'
      have hp := mC_pos c
      obtain ⟨M, rfl⟩ : ∃ M, N' = M + 1 := ⟨N' - 1, by omega⟩
      cases c with
      | skip =>
        simp only [mC] at hN hN'
        exact ih k ks t M (by omega) (by omega) h
      | set n e =>
        simp only [mC] at hN hN'
        exact ih k ks _ M (by omega) (by omega) h
      | seq a b =>
        simp only [mC] at hN hN'
        have h1 := mK_push a pc (pushT b (pc + 4 * sC a) k)
        have h2 := mK_push b (pc + 4 * sC a) k
        exact ih _ _ t M (by omega) (by omega) (Corr.push a _ _ (Corr.push b _ _ h))
      | ite e a b =>
        simp only [mC] at hN hN'
        by_cases hg : (evalS e t).val ≠ 0
        · have h1 := mK_push a (pc + 4 * (sE e + 1)) (.jmp (pc + 4 * (sE e + 1 + sC a)) (pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)
          simp only [mK] at h1
          simp only [runS, walk, hg, ne_eq, not_false_eq_true, ↓reduceIte]
          exact ih _ _ t M (by omega) (by omega) (Corr.push a _ _ (Corr.jmp h))
        · have h1 := mK_push b (pc + 4 * (sE e + 1 + sC a + 1)) k
          simp only [runS, walk, hg, ↓reduceIte]
          exact ih _ _ t M (by omega) (by omega) (Corr.push b _ _ h)

/-- **Equal source leakage, equal micro-steps.** This is `det`'s content: the machine's PCs and addresses follow from
    the branch bits the source already shows. -/
theorem walk_same (ret : SExpr) : ∀ (N : Nat) (k : List TF) (ks : List SFrame) (t t' : Slots) (N' : Nat),
    mK k ≤ N → mK k ≤ N' → Corr ks k → (runS ret N' ks t).lk = (runS ret N' ks t').lk →
    (walk N k t).1 = (walk N k t').1 := by
  intro N
  induction N with
  | zero => intro k ks t t' N' _ _ _ _; rfl
  | succ N ih =>
    intro k ks t t' N' hN hN' hc hl
    cases hc with
    | nil => rfl
    | jmp h =>
      simp only [mK] at hN hN'
      simp only [walk, List.cons.injEq, true_and]
      exact ih _ ks t t' N' (by omega) (by omega) h hl
    | @cmd ks k c q pc h =>
      simp only [mK] at hN hN'
      have hp := mC_pos c
      obtain ⟨M, rfl⟩ : ∃ M, N' = M + 1 := ⟨N' - 1, by omega⟩
      cases c with
      | skip =>
        simp only [mC] at hN hN'
        simp only [runS, tick, List.nil_append, List.cons.injEq, true_and] at hl
        simp only [walk, List.cons.injEq, true_and]
        exact ih k ks t t' M (by omega) (by omega) h hl
      | set n e =>
        simp only [mC] at hN hN'
        simp only [runS, tick, List.nil_append, List.cons.injEq, true_and] at hl
        simp only [walk]
        rw [ih k ks _ _ M (by omega) (by omega) h hl]
      | seq a b =>
        simp only [mC] at hN hN'
        have h1 := mK_push a pc (pushT b (pc + 4 * sC a) k)
        have h2 := mK_push b (pc + 4 * sC a) k
        simp only [runS] at hl
        simp only [walk]
        exact ih _ _ t t' M (by omega) (by omega) (Corr.push a _ _ (Corr.push b _ _ h)) hl
      | ite e a b =>
        simp only [mC] at hN hN'
        have h1 := mK_push a (pc + 4 * (sE e + 1)) (.jmp (pc + 4 * (sE e + 1 + sC a)) (pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)
        simp only [mK] at h1
        have h2 := mK_push b (pc + 4 * (sE e + 1 + sC a + 1)) k
        by_cases hg : (evalS e t).val ≠ 0 <;> by_cases hg' : (evalS e t').val ≠ 0
        · simp only [runS, hg, hg', ne_eq, not_false_eq_true, ↓reduceIte, tick, List.cons_append, List.nil_append,
            List.cons.injEq, true_and] at hl
          simp only [walk, hg, hg', ne_eq, not_false_eq_true, ↓reduceIte]
          rw [ih _ _ t t' M (by omega) (by omega) (Corr.push a _ _ (Corr.jmp h)) hl]
        · simp [runS, hg, hg', tick] at hl
        · simp [runS, hg, hg', tick] at hl
        · simp only [runS, hg, hg', ↓reduceIte, tick, List.cons_append, List.nil_append,
            List.cons.injEq, true_and] at hl
          simp only [walk, hg, hg', ↓reduceIte]
          rw [ih _ _ t t' M (by omega) (by omega) (Corr.push b _ _ h) hl]

theorem mE_length : ∀ (e : SExpr) (pc : Nat), (mE e pc).length = sE e
  | .lit _, _ | .slot _, _ => rfl
  | .add a b, pc => by simp only [mE, sE, List.length_append, mE_length a, mE_length b]; rfl

/-- Every frame's command is at most `L` instructions. -/
def FS (L : Nat) : List TF → Prop
  | [] => True
  | .cmd c _ :: k => sC c ≤ L ∧ FS L k
  | .jmp _ _ :: k => FS L k

/-- How many jumps are waiting. -/
def jc : List TF → Nat
  | [] => 0
  | .cmd _ _ :: k => jc k
  | .jmp _ _ :: k => 1 + jc k

theorem push_fs {L : Nat} : ∀ (c : SCmd) (pc : Nat) (k : List TF), sC c ≤ L → FS L k → FS L (pushT c pc k)
  | .seq a b, pc, k, h, hk => by
    simp only [sC] at h
    exact push_fs a _ _ (by omega) (push_fs b _ _ (by omega) hk)
  | .skip, _, _, h, hk | .set _ _, _, _, h, hk | .ite _ _ _, _, _, h, hk => ⟨h, hk⟩

theorem jc_push : ∀ (c : SCmd) (pc : Nat) (k : List TF), jc (pushT c pc k) = jc k
  | .seq a b, pc, k => by simp only [pushT, jc_push a, jc_push b]
  | .skip, _, _ | .set _ _, _, _ | .ite _ _ _, _, _ => rfl

/-- **The instructions are bounded by the source's cost**: a step of cost one becomes at most `L` instructions. -/
theorem walk_len (ret : SExpr) (L : Nat) : ∀ (N : Nat) (k : List TF) (ks : List SFrame) (t : Slots) (N' : Nat),
    mK k ≤ N → mK k ≤ N' → Corr ks k → FS L k →
    (walk N k t).1.length ≤ L * (runS ret N' ks t).cost + jc k := by
  intro N
  induction N with
  | zero => intro k ks t N' _ _ _ _; simp [walk]
  | succ N ih =>
    intro k ks t N' hN hN' hc hs
    cases hc with
    | nil => simp [walk, jc]
    | jmp h =>
      simp only [mK] at hN hN'
      have := ih _ ks t N' (by omega) (by omega) h hs
      simp only [walk, List.length_cons, jc]
      omega
    | @cmd ks k c q pc h =>
      simp only [mK] at hN hN'
      have hp := mC_pos c
      obtain ⟨M, rfl⟩ : ∃ M, N' = M + 1 := ⟨N' - 1, by omega⟩
      obtain ⟨hs1, hs2⟩ := hs
      cases c with
      | skip =>
        simp only [mC] at hN hN'
        simp only [sC] at hs1
        have := ih k ks t M (by omega) (by omega) h hs2
        simp only [walk, runS, tick, List.length_cons, jc, Nat.mul_add, Nat.mul_one]
        omega
      | set n e =>
        simp only [mC] at hN hN'
        simp only [sC] at hs1
        have := ih k ks (updS t n (evalS e t)) M (by omega) (by omega) h hs2
        simp only [walk, runS, tick, List.length_append, List.length_cons, List.length_nil, mE_length, jc,
          Nat.mul_add, Nat.mul_one]
        omega
      | seq a b =>
        simp only [mC] at hN hN'
        simp only [sC] at hs1
        have h1 := mK_push a pc (pushT b (pc + 4 * sC a) k)
        have h2 := mK_push b (pc + 4 * sC a) k
        have := ih _ _ t M (by omega) (by omega) (Corr.push a (q ++ [0]) pc (Corr.push b (q ++ [1]) (pc + 4 * sC a) h))
          (push_fs a _ _ (by omega) (push_fs b _ _ (by omega) hs2))
        rw [jc_push, jc_push] at this
        simpa only [walk, runS, jc] using this
      | ite e a b =>
        simp only [mC] at hN hN'
        simp only [sC] at hs1
        by_cases hg : (evalS e t).val ≠ 0
        · have h1 := mK_push a (pc + 4 * (sE e + 1)) (.jmp (pc + 4 * (sE e + 1 + sC a)) (pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)
          simp only [mK] at h1
          have := ih _ _ t M (by omega) (by omega) (Corr.push a (q ++ [0]) (pc + 4 * (sE e + 1)) (Corr.jmp (p := pc + 4 * (sE e + 1 + sC a)) (t := pc + 4 * (sE e + 1 + sC a + 1 + sC b)) h))
            (push_fs a _ _ (by omega) hs2)
          rw [jc_push] at this
          simp only [jc] at this
          simp only [walk, runS, hg, ne_eq, not_false_eq_true, ↓reduceIte, tick, List.length_append, List.length_cons,
            List.length_nil, mE_length, jc]
          rw [Nat.mul_add L 1 _, Nat.mul_one]
          omega
        · have h1 := mK_push b (pc + 4 * (sE e + 1 + sC a + 1)) k
          have := ih _ _ t M (by omega) (by omega) (Corr.push b (q ++ [1]) (pc + 4 * (sE e + 1 + sC a + 1)) h)
            (push_fs b _ _ (by omega) hs2)
          rw [jc_push] at this
          simp only [walk, runS, hg, ↓reduceIte, tick, List.length_append, List.length_cons,
            List.length_nil, mE_length, jc]
          rw [Nat.mul_add L 1 _, Nat.mul_one]
          omega

/-! ## The whole program -/

def genP (p : SProg) : List Insn :=
  [.lui 7 0x20] ++ genC p.body ++ genE p.ret 0 ++
    [.add 10 8 0, .addi 17 0 (Int.ofNat 93), .ecall]

def okP (p : SProg) : Bool :=
  okC p.body && okE p.ret 0 && decide (4 * (genP p).length ≤ 3000)

def startPc : Nat := codeBase + 4
def retPc (p : SProg) : Nat := startPc + 4 * sC p.body
def pcE (p : SProg) : Nat := retPc p + 4 * sE p.ret + 8
def k0 (p : SProg) : List TF := pushT p.body startPc []

/-- **Every micro-step of a run**, from the input bytes alone. -/
def allM (p : SProg) (t : Slots) : List Micro :=
  [(codeBase, [])] ++ (walk (mC p.body) (k0 p) t).1 ++ mE p.ret (retPc p) ++
    [(retPc p + 4 * sE p.ret, []), (retPc p + 4 * sE p.ret + 4, [])]

def retW (p : SProg) (t : Slots) : W64 := evalS p.ret (walk (mC p.body) (k0 p) t).2

def exitF (w : W64) (pc : Nat) : Nat → Beh
  | 0 => fuelB
  | _ + 1 => { ev := [retEv w], lk := [.step [pc]], cost := 1, out := .done }

theorem genP_length (p : SProg) : (genP p).length = 1 + sC p.body + sE p.ret + 3 := by
  simp only [genP, List.length_append, genC_length, genE_length, List.length_cons, List.length_nil]

theorem init_inv {C : List Byte} {d : Nat → Byte} {e : Env} (hC : C.length ≤ 3000) (v : W64)
    (hv : v = W64.ofNat dataBase) :
    Inv { (init C d e) with pc := codeBase + 4, x := (init C d e).set 7 v } (wordAt d) := by
  have hcb : codeBase = 0x100b0 := rfl
  have hdb : dataBase = 0x20000 := rfl
  refine ⟨by rw [get_set (by omega)]; simp [hv], fun n hn => ?_⟩
  have hn' : n < 256 := hn
  have hA : slotAddr n + 8 < 18446744073709551616 := by simp only [slotAddr]; omega
  rw [load8_val _ _ hA]
  have hm : ∀ i, i < 8 → (init C d e).mem (slotAddr n + i) = d (8 * n + i) := by
    intro i hi
    have h1 : inCode C (slotAddr n + i) = false := by
      have : ¬ (codeBase ≤ slotAddr n + i ∧ slotAddr n + i < codeBase + C.length) := by
        simp only [slotAddr]; omega
      simp [inCode]; simp only [slotAddr]; omega
    have h2 := inData_slot n i hn hi
    have h3 : slotAddr n + i - dataBase = 8 * n + i := by simp only [slotAddr]; omega
    simp only [init, h1, h2, Bool.false_eq_true, ↓reduceIte, h3]
  have h0 := hm 0 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [h0, hm 1 (by omega), hm 2 (by omega), hm 3 (by omega), hm 4 (by omega), hm 5 (by omega),
    hm 6 (by omega), hm 7 (by omega), wordAt]
  apply congrArg W64.ofNat
  omega

theorem k0_bound' (p : SProg) : mK (k0 p) ≤ mC p.body := by
  have := mK_push p.body startPc []
  simpa [mK, k0] using this

theorem lui_value : wordOfInt (sext 32 (0x20 * 2 ^ 12)) = W64.ofNat dataBase := by decide

/-- The entry instruction sets the base register and leaves the slots as the input bytes say. -/
theorem entry_exec {C : List Byte} {d : Nat → Byte} {e : Env} (hC : C.length ≤ 3000)
    (hl : fetchI C codeBase = some (.lui 7 0x20)) :
    ∃ m₁, Exec C e [(codeBase, [])] (init C d e) m₁ ∧ m₁.pc = codeBase + 4 ∧ Inv m₁ (wordAt d) := by
  obtain ⟨w₀, hf₀, hd₀⟩ := fetchI_parts hl
  have hs₀ : Rv.step C e (init C d e) =
      .next [] { (init C d e) with pc := codeBase + 4, x := (init C d e).set 7 (wordOfInt (sext 32 (0x20 * 2 ^ 12))) } := by
    have : (init C d e).pc = codeBase := rfl
    simp only [Rv.step, this, hf₀, hd₀]
  exact ⟨_, Exec.step hs₀, rfl, init_inv hC _ lui_value⟩

/-- The value after `add x, y, x0` is `y`. -/
theorem add_zero_w (v : W64) : W64.add v (W64.ofNat 0) = v := by
  apply Fin.ext
  have hlt : v.val < 18446744073709551616 := v.isLt
  simp only [W64.add, W64.ofNat, Nat.reducePow, Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt hlt

/-- **The exit**: the result into `a0`, the syscall number into `a7`, and the `ecall`. -/
theorem exit_exec {C : List Byte} {e : Env} {m : Mach} {pc : Nat} (hp : m.pc = pc)
    (h0 : fetchI C pc = some (.add 10 8 0)) (h1 : fetchI C (pc + 4) = some (.addi 17 0 (Int.ofNat 93)))
    (h2 : fetchI C (pc + 8) = some .ecall) :
    ∃ m₅, Exec C e [(pc, []), (pc + 4, [])] m m₅ ∧ ∀ k, Rv.run C e k m₅ = exitF (m.get 8) (pc + 8) k := by
  subst hp
  obtain ⟨w₄, hf₄, hd₄⟩ := fetchI_parts h0
  obtain ⟨w₅, hf₅, hd₅⟩ := fetchI_parts h1
  obtain ⟨w₆, hf₆, hd₆⟩ := fetchI_parts h2
  let m₄ : Mach := { m with pc := m.pc + 4, x := m.set 10 (W64.add (m.get 8) (m.get 0)) }
  have hs₄ : Rv.step C e m = .next [] m₄ := by simp only [Rv.step, hf₄, hd₄, m₄]
  let m₅ : Mach := { m₄ with pc := m₄.pc + 4, x := m₄.set 17 (W64.ofNat (addImm (m₄.get 0) (Int.ofNat 93))) }
  have hs₅ : Rv.step C e m₄ = .next [] m₅ := by
    have : m₄.pc = m.pc + 4 := rfl
    simp only [Rv.step, this, hf₅, hd₅, m₅]
  have p₅ : m₅.pc = m.pc + 8 := rfl
  have h17 : m₅.get 17 = sysExit := by
    simp only [m₅]
    rw [get_set (by omega)]
    simp only [↓reduceIte, get_zero]
    rfl
  have h10 : m₅.get 10 = m.get 8 := by
    simp only [m₅]
    rw [get_set (by omega)]
    simp only [show (10 : Nat) ≠ 17 by omega, ↓reduceIte, m₄]
    rw [get_set (by omega)]
    simp only [↓reduceIte, get_zero]
    exact add_zero_w _
  refine ⟨m₅, (Exec.step hs₄).trans (Exec.stepAt hs₅ rfl), fun k => ?_⟩
  cases k with
  | zero => rfl
  | succ k =>
    have hst : Rv.step C e m₅ = .exit (m.get 8) := by
      simp only [Rv.step, p₅, hf₆, hd₆, h17, ↓reduceIte, h10]
    simp only [Rv.run, hst, p₅]
    rfl

/-- What compiled code looks like, found by position. -/
structure Laid (C : List Byte) (p : SProg) : Prop where
  size : C.length ≤ 3000
  lui : fetchI C codeBase = some (.lui 7 0x20)
  body : At C startPc (genC p.body)
  res : At C (retPc p) (genE p.ret 0)
  x0 : fetchI C (retPc p + 4 * sE p.ret) = some (.add 10 8 0)
  x1 : fetchI C (retPc p + 4 * sE p.ret + 4) = some (.addi 17 0 (Int.ofNat 93))
  x2 : fetchI C (retPc p + 4 * sE p.ret + 8) = some .ecall

theorem genP_good {p : SProg} (hb : okC p.body = true) (hr : okE p.ret 0 = true) : ∀ i ∈ genP p, Good i := by
  intro i hi
  simp only [genP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((hi | hi) | hi) | (hi | hi | hi)
  · subst hi; exact good_lui (by omega) (by omega)
  · exact genC_good _ hb i hi
  · exact genE_good _ _ hr i hi
  · subst hi; exact good_add (by omega) (by omega) (by omega)
  · subst hi; exact good_addi (by omega) (by omega) (by omega)
  · subst hi; exact good_ecall

theorem laid {p : SProg} (hb : okC p.body = true) (hr : okE p.ret 0 = true)
    (hlen : 4 * (genP p).length ≤ 3000) : Laid (code (genP p)) p := by
  have hat : At (code (genP p)) codeBase (genP p) := fun j hj => fetchI_code (genP_good hb hr) hj
  simp only [genP] at hat
  have atP := hat.left.left
  have atB := atP.right
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one] at atB
  have atR := hat.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, genC_length] at atR
  have atX := hat.right
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, genC_length, genE_length] at atX
  have e1 : retPc p = codeBase + 4 * (1 + sC p.body) := by simp only [retPc, startPc]; omega
  have e2 : retPc p + 4 * sE p.ret = codeBase + 4 * (1 + sC p.body + sE p.ret) := by rw [e1]; omega
  refine ⟨by rw [code_length]; exact hlen, atP.left.head, atB, by rw [e1]; exact atR, ?_, ?_, ?_⟩
  · rw [e2]; exact atX 0 (by simp)
  · rw [e2]; exact atX 1 (by simp)
  · rw [e2]; exact atX 2 (by simp)

/-- **The one equation, given the layout.** -/
theorem run_eq_laid {C : List Byte} {p : SProg} (hl : Laid C p) (hb : okC p.body = true)
    (hr : okE p.ret 0 = true) (n : Nat) (d : Nat → Byte) (e : Env) :
    Rv.run C e n (init C d e) = playApp (allM p (wordAt d)) (exitF (retW p (wordAt d)) (pcE p)) n := by
  obtain ⟨m₁, e₁, p₁, i₁⟩ := entry_exec (d := d) (e := e) hl.size hl.lui
  have hfrm : FOk C (k0 p) := push_fok _ _ _ hb hl.body trivial
  have hch : Chain m₁.pc (k0 p) (retPc p) := by
    rw [p₁]; exact push_chain _ _ _ _ rfl
  obtain ⟨m₂, e₂, p₂, i₂⟩ := walk_exec (en := e) hl.size (retPc p) (mC p.body) (k0 p) (wordAt d) m₁
    (k0_bound' p) hfrm hch i₁
  obtain ⟨m₃, e₃, p₃, _, v₃, _⟩ := genE_exec (en := e) p.ret 0 m₂ _ hr i₂ (by rw [p₂]; exact hl.res)
  rw [p₂] at e₃ p₃
  obtain ⟨m₅, e₅, hexit⟩ := exit_exec (e := e) p₃ hl.x0 hl.x1 hl.x2
  have hval : m₃.get 8 = retW p (wordAt d) := v₃
  rw [hval] at hexit
  have hE : Exec C e (allM p (wordAt d)) (init C d e) m₅ := ((e₁.trans e₂).trans e₃).trans e₅
  rw [hE n]
  have : (fun k => Rv.run C e k m₅) = exitF (retW p (wordAt d)) (pcE p) := funext hexit
  rw [this]

/-- **The one equation.** At every fuel, whatever the environment, the compiled program shows `allM` played up to that
    fuel, then the exit. -/
theorem run_eq {p : SProg} (hok : okP p = true) (n : Nat) (d : Nat → Byte) (e : Env) :
    Rv.run (code (genP p)) e n (init (code (genP p)) d e) =
      playApp (allM p (wordAt d)) (exitF (retW p (wordAt d)) (pcE p)) n := by
  simp only [okP, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact run_eq_laid (laid hok.1.1 hok.1.2 hok.2) hok.1.1 hok.1.2 n d e

/-- **The environment cannot show.** -/
theorem compiled_ignores_env {p : SProg} (hok : okP p = true) (n : Nat) (d : Nat → Byte) (e e' : Env) :
    Rv.run (code (genP p)) e n (init (code (genP p)) d e) =
      Rv.run (code (genP p)) e' n (init (code (genP p)) d e') := by
  rw [run_eq hok, run_eq hok]

/-! ## What a played run shows -/

theorem play_ev (w : W64) (pc : Nat) : ∀ (L : List Micro) (n : Nat),
    (playApp L (exitF w pc) n).ev = [] ∨ (playApp L (exitF w pc) n).ev = [retEv w]
  | [], 0 => Or.inl rfl
  | [], _ + 1 => Or.inr rfl
  | _ :: _, 0 => Or.inl rfl
  | _ :: L, n + 1 => play_ev w pc L n

theorem play_cost (w : W64) (pc : Nat) : ∀ (L : List Micro) (n : Nat),
    (playApp L (exitF w pc) n).cost ≤ L.length + 1
  | [], 0 => by simp [playApp, exitF, fuelB]
  | [], _ + 1 => by simp [playApp, exitF]
  | _ :: _, 0 => by simp [playApp, fuelB]
  | x :: L, n + 1 => by
    have := play_cost w pc L n
    simp only [playApp, tickM, List.length_cons]
    omega

theorem play_fin (w : W64) (pc : Nat) : ∀ (L : List Micro) (n : Nat), L.length < n →
    (playApp L (exitF w pc) n).out = .done ∧ (playApp L (exitF w pc) n).ev = [retEv w]
  | [], 0, h => by simp at h
  | [], _ + 1, _ => ⟨rfl, rfl⟩
  | _ :: _, 0, h => by simp at h
  | _ :: L, n + 1, h => play_fin w pc L n (by simpa using h)

theorem play_out (w : W64) (pc : Nat) : ∀ (L : List Micro) (n : Nat),
    (playApp L (exitF w pc) n).out ≠ .fuel →
    (playApp L (exitF w pc) n).out = .done ∧ (playApp L (exitF w pc) n).ev = [retEv w]
  | [], 0, h => absurd rfl h
  | [], _ + 1, _ => ⟨rfl, rfl⟩
  | _ :: _, 0, h => absurd rfl h
  | _ :: L, n + 1, h => play_out w pc L n h

/-- An observer sees the same of two runs with the same micro-steps, if it sees the same of their results. -/
theorem play_view (f : Observer) {w w' : W64} (pc : Nat)
    (hf : [retEv w].filter (fun e => f e.chan) = [retEv w'].filter (fun e => f e.chan)) :
    ∀ (L : List Micro) (n : Nat), (playApp L (exitF w pc) n).view f = (playApp L (exitF w' pc) n).view f
  | [], 0 => rfl
  | [], _ + 1 => by
    show Beh.mk ([retEv w].filter (fun e => f e.chan)) _ _ _ = Beh.mk ([retEv w'].filter (fun e => f e.chan)) _ _ _
    rw [hf]
    rfl
  | _ :: _, 0 => rfl
  | x :: L, n + 1 => by
    have h := play_view f pc hf L n
    have he := congrArg Beh.ev h
    have hl := congrArg Beh.lk h
    have hc := congrArg Beh.cost h
    have ho := congrArg Beh.out h
    simp only [Beh.view] at he hl hc ho
    simp only [playApp, tickM, Beh.view, he, hl, hc, ho]

/-! ## The pass -/

/-- The code's length in instructions. A source step becomes at most this many. -/
def codeLen (p : SProg) : Nat := (genP p).length

/-- The transformers: a budget of `c` becomes `L * c + L`, and every target fuel looks at the finished source run.
    **That constant fuel works only because the slice has no loops.** -/
def xf (p : SProg) : Xform where
  lk l := l
  cost c := codeLen p * c + codeLen p
  fuel _ := mC p.body
  costMono a b h := by
    have := Nat.mul_le_mul_left (codeLen p) h
    omega

def compR (p : SProg) : Except String (List Byte × Xform) :=
  if okP p then .ok (code (genP p), xf p) else .error "the program does not fit the slice's instructions"

theorem compR_ok {p : SProg} {p' : List Byte} {t : Xform} (h : compR p = .ok (p', t)) :
    okP p = true ∧ p' = code (genP p) ∧ t = xf p := by
  simp only [compR] at h
  split at h
  · rename_i hk
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨hk, h.1.symm, h.2.symm⟩
  · cases h

/-- The source run at the fuel where it has finished. -/
def srcRun (p : SProg) (d : Nat → Byte) : Beh := runS p.ret (mC p.body) (pushS p.body [] []) (wordAt d)

theorem k0_bound (p : SProg) : mK (k0 p) ≤ mC p.body := by
  have := mK_push p.body startPc []
  simpa [mK, k0] using this

theorem k0_corr (p : SProg) : Corr (pushS p.body [] []) (k0 p) := Corr.push _ _ _ Corr.nil

theorem src_done (p : SProg) (d : Nat → Byte) :
    (srcRun p d).out = .done ∧ (srcRun p d).ev = [retEv (retW p (wordAt d))] :=
  walk_src p.ret _ _ _ _ _ (k0_bound p) (k0_bound p) (k0_corr p)

/-- The source at any fuel is a prefix of its finished run, and finished runs are that run. -/
theorem src_any (p : SProg) (d : Nat → Byte) (n : Nat) :
    (runS p.ret n (pushS p.body [] []) (wordAt d)).ev <+: (srcRun p d).ev ∧
    ((runS p.ret n (pushS p.body [] []) (wordAt d)).out ≠ .fuel →
      runS p.ret n (pushS p.body [] []) (wordAt d) = srcRun p d) := by
  rcases Nat.le_total n (mC p.body) with h | h
  · have hx := runS_ext p.ret n (mC p.body) (pushS p.body [] []) (wordAt d) h
    exact ⟨hx.2.1, hx.1⟩
  · have hx := runS_ext p.ret (mC p.body) n (pushS p.body [] []) (wordAt d) h
    have hd : (srcRun p d).out ≠ .fuel := by rw [(src_done p d).1]; simp
    have he := hx.1 hd
    exact ⟨by rw [← he]; exact List.prefix_refl _, fun _ => he.symm⟩

theorem allM_len (p : SProg) (t : Slots) :
    (allM p t).length = 1 + (walk (mC p.body) (k0 p) t).1.length + sE p.ret + 2 := by
  simp only [allM, List.length_append, mE_length, List.length_cons, List.length_nil]

theorem k0_fs (p : SProg) : FS (codeLen p) (k0 p) := by
  refine push_fs _ _ _ ?_ trivial
  simp only [codeLen, genP_length]; omega

/-- **Slots to machine bytes**: one step becomes many, and the machine has an environment. -/
def rvPass (P : Nat → Bool) : PassCert (slotLang Env P) (rvLang P) where
  comp := compR
  enc i := i
  enc_adm _ h := h
  cover u hu := ⟨u, hu, rfl⟩
  low_cover u u' hu hu' hl := ⟨u, u', hu, hu', hl, rfl, rfl⟩
  ev_sim p p' t h m i _ := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    show (Rv.run _ i.2 m (init _ i.1 i.2)).ev <+: (srcRun p i.1).ev
    rw [run_eq hok, (src_done p i.1).2]
    rcases play_ev (retW p (wordAt i.1)) (pcE p) (allM p (wordAt i.1)) m with he | he <;> rw [he]
    · exact List.nil_prefix
    · exact List.prefix_refl _
  cost_sim p p' t h m i _ := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    show (Rv.run _ i.2 m (init _ i.1 i.2)).cost ≤ codeLen p * (srcRun p i.1).cost + codeLen p
    rw [run_eq hok]
    have h1 := play_cost (retW p (wordAt i.1)) (pcE p) (allM p (wordAt i.1)) m
    have h2 := walk_len p.ret (codeLen p) _ (k0 p) (pushS p.body [] []) (wordAt i.1) (mC p.body)
      (k0_bound p) (k0_bound p) (k0_corr p) (k0_fs p)
    have h3 : jc (k0 p) = 0 := by simp [k0, jc_push, jc]
    have h4 : codeLen p = 1 + sC p.body + sE p.ret + 3 := genP_length p
    have h6 : (allM p (wordAt i.1)).length = 1 + (walk (mC p.body) (k0 p) (wordAt i.1)).1.length + sE p.ret + 2 :=
      allM_len p _
    rw [h6] at h1
    rw [h3] at h2
    have h5 : (runS p.ret (mC p.body) (pushS p.body [] []) (wordAt i.1)).cost = (srcRun p i.1).cost := rfl
    rw [h5] at h2
    omega
  det p p' t h f m i i' _ _ he := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    have he' : (srcRun p i.1).view f = (srcRun p i'.1).view f := he
    have hlk : (srcRun p i.1).lk = (srcRun p i'.1).lk :=
      (congrArg Beh.lk he' : (Beh.view f _).lk = (Beh.view f _).lk)
    have hev := congrArg Beh.ev he'
    simp only [Beh.view] at hev
    rw [(src_done p i.1).2, (src_done p i'.1).2] at hev
    have hw := walk_same p.ret _ _ _ (wordAt i.1) (wordAt i'.1) _ (k0_bound p) (k0_bound p) (k0_corr p) hlk
    have hall : allM p (wordAt i.1) = allM p (wordAt i'.1) := by simp only [allM, hw]
    show (Rv.run _ i.2 m (init _ i.1 i.2)).view f = (Rv.run _ i'.2 m (init _ i'.1 i'.2)).view f
    rw [run_eq hok, run_eq hok, hall]
    exact play_view f _ hev _ m
  progress p p' t h n i _ hf := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    have he := (src_any p i.1 n).2 hf
    obtain ⟨h1, h2⟩ := play_fin (retW p (wordAt i.1)) (pcE p) (allM p (wordAt i.1)) _ (Nat.lt_succ_self _)
    refine ⟨(allM p (wordAt i.1)).length + 1, ?_, ?_⟩
    · show (Rv.run _ i.2 _ (init _ i.1 i.2)).out = (runS p.ret n (pushS p.body [] []) (wordAt i.1)).out
      rw [run_eq hok, he, h1, (src_done p i.1).1]
    · show (Rv.run _ i.2 _ (init _ i.1 i.2)).ev = (runS p.ret n (pushS p.body [] []) (wordAt i.1)).ev
      rw [run_eq hok, he, h2, (src_done p i.1).2]
  catch_up p p' t h n i _ := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    obtain ⟨_, h2⟩ := play_fin (retW p (wordAt i.1)) (pcE p) (allM p (wordAt i.1)) _ (Nat.lt_succ_self _)
    refine ⟨(allM p (wordAt i.1)).length + 1, ?_⟩
    show (runS p.ret n (pushS p.body [] []) (wordAt i.1)).ev <+: (Rv.run _ i.2 _ (init _ i.1 i.2)).ev
    rw [run_eq hok, h2, ← (src_done p i.1).2]
    exact (src_any p i.1 n).1
  reflect p p' t h m i _ hf := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    have hf' : (playApp (allM p (wordAt i.1)) (exitF (retW p (wordAt i.1)) (pcE p)) m).out ≠ .fuel := by
      rw [← run_eq hok]; exact hf
    obtain ⟨h1, h2⟩ := play_out _ _ _ _ hf'
    refine ⟨mC p.body, ?_, ?_⟩
    · show (srcRun p i.1).out = (Rv.run _ i.2 m (init _ i.1 i.2)).out
      rw [run_eq hok, h1, (src_done p i.1).1]
    · show (srcRun p i.1).ev = (Rv.run _ i.2 m (init _ i.1 i.2)).ev
      rw [run_eq hok, h2, (src_done p i.1).2]

/-! ## The pipeline -/

/-- **Source to machine bytes**: two certified passes, chained. -/
def pipeline (P : Nat → Bool) : PassCert (sliceLang Env P) (rvLang P) :=
  (slotPass Env P).seq (rvPass P)

/-- **What the checker accepts, compiled, carries `rel` and the transformed budget on the machine**, by the kernel's
    transfers alone. No proof here is about either certificate. -/
theorem slice_carries {P : Nat → Bool} {p : Prog} {k : Nat} {C : List Byte} {t : Xform}
    (hc : sliceCheck P p = some k) (hcomp : (pipeline P).comp p = .ok (C, t)) :
    Cert.rel (rvLang P) C ∧ Cert.bound (rvLang P) (t.cost k) C :=
  ⟨(pipeline P).rel_transfer hcomp (sliceCheck_rel hc), (pipeline P).bound_transfer hcomp (sliceCheck_bound hc)⟩

/-! ## Witnesses -/

theorem clean_fits : fits clean = true := by decide
theorem clean_ok : okP (compile clean) = true := by decide

theorem clean_pipeline :
    (pipeline sec0).comp clean = .ok (code (genP (compile clean)), Xform.id.then (xf (compile clean))) := by
  show (match comp clean with
    | .error e => .error e
    | .ok (p', t) => match compR p' with
      | .error e => .error e
      | .ok (p'', u) => .ok (p'', t.then u) : Except String (List Byte × Xform)) = _
  rw [clean_comp]
  have : compR (compile clean) = .ok (code (genP (compile clean)), xf (compile clean)) := by
    simp [compR, clean_ok]
  simp only [this]
  rfl

/-- **`clean`, on the machine.** For every byte pattern in the secret word and every environment. -/
theorem clean_on_machine :
    Cert.rel (rvLang sec0) (code (genP (compile clean))) ∧
    Cert.bound (rvLang sec0) ((Xform.id.then (xf (compile clean))).cost 4) (code (genP (compile clean))) :=
  slice_carries clean_checks clean_pipeline

/-- **The compiled `clean` computes what the source does**, on the machine, by evaluation. -/
theorem clean_runs_on_machine :
    (Rv.run (code (genP (compile clean))) env0 200
      (init (code (genP (compile clean))) (encBytes (inp 5 3)) env0)).ev = [Rv.retEv (W64.ofNat 6)]
  ∧ (Rv.run (code (genP (compile clean))) env0 200
      (init (code (genP (compile clean))) (encBytes (inp 5 3)) env0)).out = .done := by
  decide

/-- An environment that holds a lot, and maps a lot. -/
def envBusy : Env where
  reg r := W64.ofNat (r + 77)
  mem _ := byteOf 99
  rd _ := true
  wr _ := true

/-- **Concretely, a busy environment changes nothing**, on the same bytes. -/
theorem clean_ignores_busy_env (n : Nat) :
    Rv.run (code (genP (compile clean))) envBusy n (init (code (genP (compile clean))) (encBytes (inp 5 3)) envBusy) =
      Rv.run (code (genP (compile clean))) env0 n (init (code (genP (compile clean))) (encBytes (inp 5 3)) env0) :=
  compiled_ignores_env clean_ok n _ _ _

/-- **Refused**: a literal too large for the slice's instructions. -/
theorem large_literal_refused :
    okP { body := .skip, ret := .lit (W64.ofNat 2048) } = false := by decide

/-- **Refused**: a slot beyond the instructions' reach. -/
theorem high_slot_refused :
    okP { body := .skip, ret := .slot 256 } = false := by decide

/-- **And `rel` on the machine is not vacuous**: the refused `secretRet`, compiled the same way, leaks there. -/
theorem secretRet_machine_leaks :
    ¬ Cert.rel (rvLang sec0) (code (genP (compile secretRet))) := by
  intro h
  have hl : (rvLang sec0).lowIn (encBytes (inp 5 1), env0) (encBytes (inp 6 1), env0) := by
    intro off hoff
    show encBytes (inp 5 1) off = encBytes (inp 6 1) off
    have hk : off / 8 ≠ 0 := by
      intro h0; rw [h0] at hoff; simp [sec0] at hoff
    simp [encBytes, inp, hk]
  have ha : ∀ a b, (rvLang sec0).Adm (encBytes (inp a b), env0) := by
    intro a b off hoff
    have hb : Rv.inBytes = 512 := rfl
    have h8 : cap ≤ off / 8 := by have : cap = 64 := rfl; omega
    show byteOf ((inp a b (off / 8)).val / 256 ^ (off % 8)) = byteOf 0
    rw [inp_adm a b _ h8]
    simp [W64.ofNat]
  have := h 200 _ _ (ha 5 1) (ha 6 1) hl
  revert this; decide

end LCore.Slice.Lower
