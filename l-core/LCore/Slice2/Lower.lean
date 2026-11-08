/-
  VS-2 step 6: slots to machine bytes, over loops and the array. **This is where the kill rule is judged.**

  `t.fuel m = m`, where VS-1 had a constant. A run may never finish, so VS-1's finite list of micro-steps cannot hold it. Instead, one lemma on the machine itself: from a good state, a frame's `chunk`
  takes the machine to the next good state. A chunk is computed from the frame and the slots alone, so the environment cannot appear in it.
-/
import LCore.Slice2.Slots
import LCore.Slice.Lower

namespace LCore.Slice2.Lower

open Slice (W64 Expr Store upd eval retEv cap tick tick_ext Ext sec0 inp)
open Slice.Rv
open Slice.Slots (SExpr evalS updS encBytes wordAt)
open Slice.Lower (Good good_lui good_addi good_add good_ld good_sd good_beq good_ecall bits_ofNat sext_small div_field fetchI fetchI_parts fetchI_code fetchI_bound
  At Micro tickM fuelB playApp playApp_append Exec Exec.nil Exec.trans Exec.step Exec.stepAt addImm_val wordOfInt_val get_zero get_set store8_in store8_out load8_val slotAddr
  load8_store_same load8_store_other Inv inData_slot addrs8_slot mE genE sE okE genE_length genE_good genE_exec mE_length wordsMax exitF entry_exec exit_exec code_length Inv.mono_mem play_view)
open Slots (SCmd SProg SFrame pushS runS slotLang arrBase)

/-! ## The two instruction forms the first slice did not need -/

theorem good_andi {rd rs i : Nat} (hd : rd < 32) (hs : rs < 32) (hi : i < 2048) :
    Good (.andi rd rs (Int.ofNat i)) := by
  have hw : encode (.andi rd rs (Int.ofNat i)) = i * 1048576 + rs * 32768 + 28672 + rd * 128 + 0x13 := by
    show bits (Int.ofNat i) 12 * 2 ^ 20 + rs * 2 ^ 15 + 7 * 2 ^ 12 + rd * 2 ^ 7 + 0x13 = _
    rw [bits_ofNat i 12 (by simp only [Nat.reducePow]; omega)]
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : i * 1048576 + rs * 32768 + 28672 + rd * 128 + 0x13 = W
  have h1 : W % 128 = 0x13 := by omega
  have h2 : rdOf W = rd := by simp only [rdOf, Nat.reducePow]; omega
  have h3 : rs1Of W = rs := by simp only [rs1Of, Nat.reducePow]; omega
  have h4 : f3Of W = 7 := by simp only [f3Of, Nat.reducePow]; omega
  have h5 : W / 2 ^ 20 = i := by simp only [Nat.reducePow]; omega
  have h6 : sext 12 i = Int.ofNat i := sext_small (by show i < 2048; omega)
  simp [decode, h1, h2, h3, h4, h5, h6]

theorem beq_neg_fields (h b a l t : Nat) (hl : l < 16) (ht : t < 2) :
    (h * 262144 + b * 8192 + a * 256 + l * 2 + t) % 2 = t ∧ (h * 131072 + b * 4096 + a * 128 + l) % 16 = l := by
  omega

set_option maxRecDepth 20000 in
/-- **A backward branch**, which the first slice never compiled. -/
theorem good_beq_back {a b i : Nat} (ha : a < 32) (hb : b < 32) (h0 : 0 < i) (hi : i ≤ 4096) (he : i % 2 = 0) :
    Good (.beq a b (-(Int.ofNat i))) := by
  obtain ⟨v, hv, hv1, hv2⟩ : ∃ v, v = 8192 - i ∧ 4096 ≤ v ∧ v < 8192 := ⟨_, rfl, by omega, by omega⟩
  have hbits : bits (-(Int.ofNat i)) 13 = v := by
    simp only [bits, Nat.reducePow]
    have : (-(Int.ofNat i)) % ((2 : Int) ^ 13) = Int.ofNat v := by
      have hp : ((2 : Int) ^ 13) = 8192 := by decide
      rw [hp]
      show (-(i : Int)) % 8192 = (v : Int)
      omega
    rw [this]; rfl
  obtain ⟨lo, hi', t, hir, hl, hh, ht⟩ : ∃ lo hi' t, v = 2 * lo + 32 * hi' + 2048 * t + 4096 ∧ lo < 16 ∧ hi' < 64 ∧ t < 2 :=
    ⟨v / 2 % 16, v / 32 % 64, v / 2048 % 2, by omega, by omega, by omega, by omega⟩
  have e1 : v / 4096 % 2 = 1 := by omega
  have e2 : v / 32 % 64 = hi' := by omega
  have e3 : v / 2 % 16 = lo := by omega
  have e4 : v / 2048 % 2 = t := by omega
  have hw : encode (.beq a b (-(Int.ofNat i))) =
      2147483648 + hi' * 33554432 + b * 1048576 + a * 32768 + lo * 256 + t * 128 + 0x63 := by
    show (bits (-(Int.ofNat i)) 13 / 4096 % 2) * 2 ^ 31 + (bits (-(Int.ofNat i)) 13 / 32 % 64) * 2 ^ 25 + b * 2 ^ 20
      + a * 2 ^ 15 + (bits (-(Int.ofNat i)) 13 / 2 % 16) * 2 ^ 8 + (bits (-(Int.ofNat i)) 13 / 2048 % 2) * 2 ^ 7 + 0x63 = _
    rw [hbits, e1, e2, e3, e4]
  refine ⟨?_, by rw [hw]; omega⟩
  rw [hw]
  generalize hW : 2147483648 + hi' * 33554432 + b * 1048576 + a * 32768 + lo * 256 + t * 128 + 0x63 = W
  have h1 : W % 128 = 0x63 := by omega
  have h3 : rs1Of W = a := by
    simp only [rs1Of, Nat.reducePow]
    rw [div_field (65536 + hi' * 1024 + b * 32 + a) (lo * 256 + t * 128 + 0x63) (by omega) (by omega)]; omega
  have h4 : rs2Of W = b := by
    simp only [rs2Of, Nat.reducePow]
    rw [div_field (2048 + hi' * 32 + b) (a * 32768 + lo * 256 + t * 128 + 0x63) (by omega) (by omega)]; omega
  have h5 : f3Of W = 0 := by
    simp only [f3Of, Nat.reducePow]
    rw [div_field (524288 + hi' * 8192 + b * 256 + a * 8) (lo * 256 + t * 128 + 0x63) (by omega) (by omega)]; omega
  have h6 : (W / 2 ^ 31) * 4096 + (W / 2 ^ 7 % 2) * 2048 + (W / 2 ^ 25 % 64) * 32 + (W / 2 ^ 8 % 16) * 2 = v := by
    have p31 : (2 : Nat) ^ 31 = 2147483648 := rfl
    have p7 : (2 : Nat) ^ 7 = 128 := rfl
    have p25 : (2 : Nat) ^ 25 = 33554432 := rfl
    have p8 : (2 : Nat) ^ 8 = 256 := rfl
    rw [p31, p7, p25, p8,
      div_field 1 (hi' * 33554432 + b * 1048576 + a * 32768 + lo * 256 + t * 128 + 0x63) (by omega) (by omega),
      div_field (16777216 + hi' * 262144 + b * 8192 + a * 256 + lo * 2 + t) 0x63 (by omega) (by omega),
      div_field (64 + hi') (b * 1048576 + a * 32768 + lo * 256 + t * 128 + 0x63) (by omega) (by omega),
      div_field (8388608 + hi' * 131072 + b * 4096 + a * 128 + lo) (t * 128 + 0x63) (by omega) (by omega)]
    have f1 : (16777216 + hi' * 262144 + b * 8192 + a * 256 + lo * 2 + t) % 2 = t := by omega
    have f2 : (8388608 + hi' * 131072 + b * 4096 + a * 128 + lo) % 16 = lo := by omega
    have f3 : (64 + hi') % 64 = hi' := by omega
    rw [f1, f2, f3]
    omega
  have h7 : sext 13 v = -(Int.ofNat i) := by
    simp only [sext]
    rw [if_pos (by show 4096 ≤ v; omega)]
    show (v : Int) - ((2 ^ 13 : Nat) : Int) = -(i : Int)
    simp only [Nat.reducePow]
    omega
  simp only [decode, h1, h3, h4, h5, h6, h7, ↓reduceIte]

/-- Adding a negative immediate, when the result does not wrap. -/
theorem addImm_back (a : W64) (i : Nat) (h0 : 0 < i) (hi : i ≤ a.val) : addImm a (-(Int.ofNat i)) = a.val - i := by
  have hlt : a.val < 18446744073709551616 := a.isLt
  have hw : (wordOfInt (-(Int.ofNat i))).val = 18446744073709551616 - i := by
    have hp : ((2 : Int) ^ 64) = 18446744073709551616 := by decide
    have hm : (-(Int.ofNat i)) % ((2 : Int) ^ 64) = Int.ofNat (18446744073709551616 - i) := by
      rw [hp]
      show (-(i : Int)) % 18446744073709551616 = ((18446744073709551616 - i : Nat) : Int)
      omega
    simp only [wordOfInt, W64.ofNat, hm]
    show (18446744073709551616 - i) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by show 18446744073709551616 - i < 18446744073709551616; omega)
  simp only [addImm, W64.add, W64.ofNat, hw]
  show (a.val + (18446744073709551616 - i)) % 18446744073709551616 = _
  omega

/-- `andi` with 63 is the array's mask. -/
theorem and_63 (v : W64) : (W64.and v (wordOfInt (Int.ofNat 63))).val = idx v := by
  have hw : (wordOfInt (Int.ofNat 63)).val = 63 := wordOfInt_val 63 (by omega)
  simp only [W64.and, W64.ofNat, hw, idx]
  have hm : v.val &&& 63 = v.val % 64 := Nat.and_two_pow_sub_one_eq_mod v.val 6
  rw [hm]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt v.val (show 64 > 0 by omega); show v.val % 64 < 2 ^ 64; omega)

/-! ## Word arithmetic for the index -/

theorem ofNat_val {n : Nat} (h : n < 18446744073709551616) : (W64.ofNat n).val = n := Nat.mod_eq_of_lt h

theorem add_ofNat {a b : Nat} (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (h : a + b < 18446744073709551616) : W64.add (W64.ofNat a) (W64.ofNat b) = W64.ofNat (a + b) := by
  simp only [W64.add, ofNat_val ha, ofNat_val hb]

/-! ## The code -/

def sC : SCmd → Nat
  | .skip => 1
  | .set _ e => sE e + 1
  | .seq a b => sC a + sC b
  | .ite e a b => sE e + 1 + sC a + 1 + sC b
  | .loop e b => sE e + 1 + sC b + 1
  | .load _ e => sE e + 5 + 2
  | .loadB _ _ e => sE e + 4
  | .store e v => sE e + 5 + sE v + 1

/-- The masked index's address, in `x8`. -/
def genIdx (e : SExpr) : List Insn :=
  genE e 0 ++ [.andi 8 8 (Int.ofNat 63), .add 8 8 8, .add 8 8 8, .add 8 8 8, .add 8 8 7]

def genC : SCmd → List Insn
  | .skip => [.addi 0 0 (Int.ofNat 0)]
  | .set n e => genE e 0 ++ [.sd 8 7 (Int.ofNat (8 * n))]
  | .seq a b => genC a ++ genC b
  | .ite e a b =>
    genE e 0 ++ [.beq 8 0 (Int.ofNat (4 * (sC a + 2)))] ++ genC a ++ [.beq 0 0 (Int.ofNat (4 * (sC b + 1)))] ++ genC b
  | .loop e b =>
    genE e 0 ++ [.beq 8 0 (Int.ofNat (4 * (sC b + 2)))] ++ genC b ++ [.beq 0 0 (-(Int.ofNat (4 * (sE e + 1 + sC b))))]
  | .load x e => genIdx e ++ [.ld 8 8 (Int.ofNat 512), .sd 8 7 (Int.ofNat (8 * x))]
  | .loadB x ws e =>
    genE e 0 ++ [.andi 8 8 (Int.ofNat (8 * ws.length - 1)), .add 8 8 7, .lbu 8 8 (Int.ofNat (8 * ws.headD 0)), .sd 8 7 (Int.ofNat (8 * x))]
  | .store e v => genIdx e ++ genE v 1 ++ [.sd 9 8 (Int.ofNat 512)]

/-- A byte array's length, in words, for which the mask `8 * len - 1` is the index modulo its bytes. -/
def maskOK (len : Nat) : Bool := len == 1 || len == 2 || len == 4 || len == 8

def okC : SCmd → Bool
  | .skip => true
  | .set n e => decide (n < wordsMax) && okE e 0
  | .seq a b => okC a && okC b
  | .ite e a b => okE e 0 && okC a && okC b && decide (sC a + 2 < 1024) && decide (sC b + 1 < 1024)
  | .loop e b => okE e 0 && okC b && decide (sC b + 2 < 1024) && decide (sE e + 1 + sC b < 1024)
  | .load x e => decide (x < wordsMax) && okE e 0
  | .loadB x ws e => decide (x < wordsMax) && okE e 0 && decide (ws = List.range' (ws.headD 0) ws.length) && maskOK ws.length &&
      decide (ws.headD 0 + ws.length ≤ 64)
  | .store e v => okE e 0 && okE v 1

theorem genIdx_length (e : SExpr) : (genIdx e).length = sE e + 5 := by
  simp only [genIdx, List.length_append, genE_length, List.length_cons, List.length_nil]

theorem genC_length : ∀ c : SCmd, (genC c).length = sC c
  | .skip => rfl
  | .set n e => by simp only [genC, sC, List.length_append, genE_length]; rfl
  | .seq a b => by simp only [genC, sC, List.length_append, genC_length a, genC_length b]
  | .ite e a b => by simp only [genC, sC, List.length_append, genE_length, genC_length a, genC_length b]; rfl
  | .loop e b => by simp only [genC, sC, List.length_append, genE_length, genC_length b]; rfl
  | .load x e => by simp only [genC, sC, List.length_append, genIdx_length]; rfl
  | .loadB x ws e => by simp only [genC, sC, List.length_append, genE_length, List.length_cons, List.length_nil]
  | .store e v => by simp only [genC, sC, List.length_append, genIdx_length, genE_length]; rfl

theorem genIdx_good (e : SExpr) (h : okE e 0 = true) : ∀ i ∈ genIdx e, Good i := by
  intro i hi
  simp only [genIdx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi | hi
  · exact genE_good e 0 h i hi
  · subst hi; exact good_andi (by omega) (by omega) (by omega)
  all_goals (subst hi; exact good_add (by omega) (by omega) (by omega))

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
  | .loop e b, h, i, hi => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [genC, List.mem_append, List.mem_singleton] at hi
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rcases hi with ((hi | hi) | hi) | hi
    · exact genE_good e 0 h1 i hi
    · subst hi; exact good_beq (by omega) (by omega) (by omega) (by omega)
    · exact genC_good b h2 i hi
    · subst hi
      exact good_beq_back (by omega) (by omega) (by omega) (by omega) (by omega)
  | .load x e, h, i, hi => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h
    have hm : wordsMax = 256 := rfl
    simp only [genC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi
    · exact genIdx_good e h.2 i hi
    · subst hi; exact good_ld (by omega) (by omega) (by omega)
    · subst hi; exact good_sd (by omega) (by omega) (by omega)
  | .loadB x ws e, h, i, hi => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hx, he⟩, _⟩, hm⟩, hb⟩ := h
    have hmax : wordsMax = 256 := rfl
    have hlen : ws.length ≤ 8 := by simp only [maskOK, Bool.or_eq_true, beq_iff_eq] at hm; omega
    simp only [genC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi | hi | hi
    · exact genE_good e 0 he i hi
    · subst hi; exact good_andi (by omega) (by omega) (by omega)
    · subst hi; exact Slice.Lower.good_add (by omega) (by omega) (by omega)
    · subst hi; exact Slice.Lower.good_lbu (by omega) (by omega) (by omega)
    · subst hi; exact good_sd (by omega) (by omega) (by omega)
  | .store e v, h, i, hi => by
    simp only [okC, Bool.and_eq_true] at h
    simp only [genC, List.mem_append, List.mem_singleton] at hi
    rcases hi with (hi | hi) | hi
    · exact genIdx_good e h.1 i hi
    · exact genE_good v 1 h.2 i hi
    · subst hi; exact good_sd (by omega) (by omega) (by omega)

/-! ## Single instructions -/

section steps
variable {C : List Byte} {en : Env} {m : Mach}

theorem step_add {rd a b : Nat} (h : fetchI C m.pc = some (.add rd a b)) :
    Slice.Rv.step C en m = .next [] { m with pc := m.pc + 4, x := m.set rd (W64.add (m.get a) (m.get b)) } := by
  obtain ⟨w, hf, hd⟩ := fetchI_parts h
  simp only [Slice.Rv.step, hf, hd]

theorem step_andi {rd a : Nat} {i : Int} (h : fetchI C m.pc = some (.andi rd a i)) :
    Slice.Rv.step C en m = .next [] { m with pc := m.pc + 4, x := m.set rd (W64.and (m.get a) (wordOfInt i)) } := by
  obtain ⟨w, hf, hd⟩ := fetchI_parts h
  simp only [Slice.Rv.step, hf, hd]

theorem step_addi {rd a : Nat} {i : Int} (h : fetchI C m.pc = some (.addi rd a i)) :
    Slice.Rv.step C en m = .next [] { m with pc := m.pc + 4, x := m.set rd (W64.ofNat (addImm (m.get a) i)) } := by
  obtain ⟨w, hf, hd⟩ := fetchI_parts h
  simp only [Slice.Rv.step, hf, hd]

theorem step_beq {a b : Nat} {i : Int} (h : fetchI C m.pc = some (.beq a b i)) :
    Slice.Rv.step C en m = .next [] { m with pc := if m.get a = m.get b then addImm (W64.ofNat m.pc) i else m.pc + 4 } := by
  obtain ⟨w, hf, hd⟩ := fetchI_parts h
  simp only [Slice.Rv.step, hf, hd]

/-- A load at a slot's word: inside the data segment, whatever the environment. -/
theorem step_ld {rd a n : Nat} {i : Int} (h : fetchI C m.pc = some (.ld rd a i)) (hn : n < wordsMax)
    (ha : addImm (m.get a) i = slotAddr n) :
    Slice.Rv.step C en m = .next [.addr (Int.ofNat (slotAddr n))]
      { m with pc := m.pc + 4, x := m.set rd (load8 m (slotAddr n)) } := by
  obtain ⟨w, hf, hd⟩ := fetchI_parts h
  have hall : (addrs8 (slotAddr n)).all (canRead C en) = true := by
    rw [List.all_eq_true]
    intro x hx
    simp [canRead, addrs8_slot hn hx]
  simp only [Slice.Rv.step, hf, hd, ha, hall, ↓reduceIte]

/-- A store at a slot's word: inside the data segment, whatever the environment. -/
theorem step_sd {rv a n : Nat} {i : Int} (h : fetchI C m.pc = some (.sd rv a i)) (hn : n < wordsMax)
    (ha : addImm (m.get a) i = slotAddr n) :
    Slice.Rv.step C en m = .next [.addr (Int.ofNat (slotAddr n))]
      { m with pc := m.pc + 4, mem := store8 m.mem (slotAddr n) (m.get rv) } := by
  obtain ⟨w, hf, hd⟩ := fetchI_parts h
  have hall : (addrs8 (slotAddr n)).all (canWrite C en) = true := by
    rw [List.all_eq_true]
    intro x hx
    simp [canWrite, addrs8_slot hn hx]
  simp only [Slice.Rv.step, hf, hd, ha, hall, ↓reduceIte]

end steps

/-- Fetch an instruction at a known position. -/
theorem At.get {C : List Byte} {pc q j : Nat} {L : List Insn} {i : Insn} (h : At C pc L) (hl : j < L.length)
    (hj : L.getD j .ecall = i) (hq : q = pc + 4 * j) : fetchI C q = some i := by
  rw [hq, ← hj]; exact h j hl

/-! ## The index -/

def mIdx (e : SExpr) (pc : Nat) : List Micro :=
  mE e pc ++ [(pc + 4 * sE e, []), (pc + 4 * sE e + 4, []), (pc + 4 * sE e + 8, []), (pc + 4 * sE e + 12, []), (pc + 4 * sE e + 16, [])]

/-- **The index's code**: `x8` holds the array word's address less 512, and `x7` and memory are untouched. -/
theorem idx_exec {C : List Byte} {en : Env} (e : SExpr) (m : Mach) (t : Slice.Slots.Slots)
    (hok : okE e 0 = true) (hinv : Inv m t) (hat : At C m.pc (genIdx e)) :
    ∃ m', Exec C en (mIdx e m.pc) m m' ∧ m'.pc = m.pc + 4 * (sE e + 5) ∧ m'.mem = m.mem ∧
      m'.get 7 = m.get 7 ∧ m'.get 8 = W64.ofNat (dataBase + 8 * idx (evalS e t)) := by
  have atE := Slice.Lower.At.left (a := genE e 0) hat
  have atT : At C (m.pc + 4 * sE e) [.andi 8 8 (Int.ofNat 63), .add 8 8 8, .add 8 8 8, .add 8 8 8, .add 8 8 7] := by
    have := Slice.Lower.At.right (a := genE e 0) hat
    rwa [genE_length] at this
  obtain ⟨m₁, e₁, p₁, mem₁, v₁, low₁⟩ := genE_exec (en := en) e 0 m t hok hinv atE
  have h7₁ : m₁.get 7 = m.get 7 := low₁ 7 (by omega)
  have hi : idx (evalS e t) < 64 := Slots.idx_lt _
  generalize hI : idx (evalS e t) = i at hi ⊢
  have hv₁ : m₁.get 8 = evalS e t := v₁
  have hb : dataBase = 0x20000 := rfl
  have fa : fetchI C m₁.pc = some (.andi 8 8 (Int.ofNat 63)) := At.get atT (j := 0) (by simp) rfl (by rw [p₁]; omega)
  let m₂ : Mach := { m₁ with pc := m₁.pc + 4, x := m₁.set 8 (W64.and (m₁.get 8) (wordOfInt (Int.ofNat 63))) }
  have s₂ : Slice.Rv.step C en m₁ = .next [] m₂ := step_andi fa
  have v₂ : m₂.get 8 = W64.ofNat i := by
    simp only [m₂]
    rw [get_set (by omega)]
    simp only [↓reduceIte, hv₁]
    apply Fin.ext
    rw [and_63, hI, ofNat_val (by omega)]
  have p₂ : m₂.pc = m.pc + 4 * sE e + 4 := by simp only [m₂, p₁]
  have l₂ : ∀ y, y < 8 → m₂.get y = m₁.get y := by
    intro y hy; simp only [m₂]; rw [get_set (by omega)]; simp [show y ≠ 8 by omega]
  have dbl : ∀ (n q : Nat) (M : Mach), M.get 8 = W64.ofNat n → n < 1000000 → M.pc = q → fetchI C q = some (.add 8 8 8) →
      ∃ M', Slice.Rv.step C en M = .next [] M' ∧ M'.pc = q + 4 ∧ M'.mem = M.mem ∧ M'.get 8 = W64.ofNat (n + n) ∧ ∀ y, y < 8 → M'.get y = M.get y := by
    intro n q M hM hn hq hf
    refine ⟨_, step_add (hq ▸ hf), by simp [hq], rfl, ?_, ?_⟩
    · rw [get_set (by omega)]
      simp only [↓reduceIte, hM]
      exact add_ofNat (by omega) (by omega) (by omega)
    · intro y hy; rw [get_set (by omega)]; simp [show y ≠ 8 by omega]
  obtain ⟨m₃, s₃, p₃, mem₃, v₃, l₃⟩ := dbl i _ m₂ v₂ (by omega) p₂ (At.get atT (j := 1) (by simp) rfl (by omega))
  obtain ⟨m₄, s₄, p₄, mem₄, v₄, l₄⟩ := dbl (i + i) _ m₃ v₃ (by omega) p₃ (At.get atT (j := 2) (by simp) rfl (by omega))
  obtain ⟨m₅, s₅, p₅, mem₅, v₅, l₅⟩ := dbl (i + i + (i + i)) _ m₄ v₄ (by omega) p₄ (At.get atT (j := 3) (by simp) rfl (by omega))
  have hm7 : m₅.get 7 = W64.ofNat dataBase := by
    rw [l₅ 7 (by omega), l₄ 7 (by omega), l₃ 7 (by omega), l₂ 7 (by omega), h7₁]; exact hinv.1
  have f₆ : fetchI C m₅.pc = some (.add 8 8 7) := At.get atT (j := 4) (by simp) rfl (by rw [p₅])
  let m₆ : Mach := { m₅ with pc := m₅.pc + 4, x := m₅.set 8 (W64.add (m₅.get 8) (m₅.get 7)) }
  have s₆ : Slice.Rv.step C en m₅ = .next [] m₆ := step_add f₆
  refine ⟨m₆, ?_, ?_, ?_, ?_, ?_⟩
  · have a₂ := Exec.stepAt s₂ (show m₁.pc = m.pc + 4 * sE e from p₁)
    have a₃ := Exec.stepAt s₃ (show m₂.pc = m.pc + 4 * sE e + 4 from p₂)
    have a₄ := Exec.stepAt s₄ (show m₃.pc = m.pc + 4 * sE e + 8 by rw [p₃])
    have a₅ := Exec.stepAt s₅ (show m₄.pc = m.pc + 4 * sE e + 12 by rw [p₄])
    have a₆ := Exec.stepAt s₆ (show m₅.pc = m.pc + 4 * sE e + 16 by rw [p₅])
    exact e₁.trans (a₂.trans (a₃.trans (a₄.trans (a₅.trans a₆))))
  · show m₅.pc + 4 = _
    rw [p₅]; omega
  · show m₅.mem = _
    rw [mem₅, mem₄, mem₃]
    show m₁.mem = _
    exact mem₁
  · show ({ m₅ with pc := m₅.pc + 4, x := m₅.set 8 (W64.add (m₅.get 8) (m₅.get 7)) } : Mach).get 7 = _
    rw [get_set (by omega)]
    simp only [show (7 : Nat) ≠ 8 by omega, ↓reduceIte]
    rw [hm7]; exact hinv.1.symm
  · show ({ m₅ with pc := m₅.pc + 4, x := m₅.set 8 (W64.add (m₅.get 8) (m₅.get 7)) } : Mach).get 8 = _
    rw [get_set (by omega)]
    simp only [↓reduceIte, v₅, hm7]
    rw [add_ofNat (by omega) (by simp only [hb]; omega) (by simp only [hb]; omega)]
    apply congrArg W64.ofNat
    omega

/-! ## Commands, one at a time, on the machine -/

/-- The address of array word `i`. -/
def arrAddr (i : Nat) : Nat := slotAddr (arrBase + i)

theorem inv_store {m : Mach} {t : Slice.Slots.Slots} (hinv : Inv m t) {n : Nat} (hn : n < wordsMax) (q : Nat) (v : W64) :
    Inv { m with pc := q, mem := store8 m.mem (slotAddr n) v } (updS t n v) := by
  have hmax : wordsMax = 256 := rfl
  have hA : ∀ j, j < wordsMax → slotAddr j + 8 < 18446744073709551616 := by
    intro j hj; simp only [slotAddr, dataBase]; omega
  refine ⟨hinv.1, fun j hj => ?_⟩
  by_cases hjn : j = n
  · subst hjn
    have := load8_store_same m (slotAddr j) v (hA j hj)
    simp only [load8] at this ⊢
    simp only [updS, ↓reduceIte]
    exact this
  · have hne := load8_store_other m (slotAddr n) (slotAddr j) v (hA n hn) (hA j hj)
      (by simp only [slotAddr]; omega)
    simp only [load8] at hne ⊢
    simp only [updS, hjn, ↓reduceIte]
    rw [hne]
    have h2 := hinv.2 j hj
    simp only [load8] at h2
    exact h2

theorem addImm_slot {m : Mach} (h7 : m.get 7 = W64.ofNat dataBase) {n : Nat} (hn : n < wordsMax) :
    addImm (m.get 7) (Int.ofNat (8 * n)) = slotAddr n := by
  have hmax : wordsMax = 256 := rfl
  have hb : dataBase = 0x20000 := rfl
  rw [h7, addImm_val _ _ (by rw [ofNat_val (by omega)]; omega), ofNat_val (by omega)]
  rfl

theorem addImm_arr {m : Mach} {i : Nat} (hi : i < 64) (h8 : m.get 8 = W64.ofNat (dataBase + 8 * i)) :
    addImm (m.get 8) (Int.ofNat 512) = arrAddr i := by
  have hb : dataBase = 0x20000 := rfl
  have hA : arrBase = 64 := rfl
  rw [h8, addImm_val _ _ (by rw [ofNat_val (by omega)]; omega), ofNat_val (by omega)]
  simp only [arrAddr, slotAddr, hA]
  omega

theorem arr_lt {i : Nat} (hi : i < 64) : arrBase + i < wordsMax := by
  have hA : arrBase = 64 := rfl
  have hm : wordsMax = 256 := rfl
  omega

/-- **`set`.** -/
theorem exec_set {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {n : Nat} {e : SExpr} (hn : n < wordsMax)
    (hok : okE e 0 = true) (hinv : Inv m t) (hat : At C m.pc (genE e 0 ++ [.sd 8 7 (Int.ofNat (8 * n))])) :
    ∃ m', Exec C en (mE e m.pc ++ [(m.pc + 4 * sE e, [.addr (Int.ofNat (slotAddr n))])]) m m' ∧
      m'.pc = m.pc + 4 * (sE e + 1) ∧ Inv m' (updS t n (evalS e t)) := by
  obtain ⟨m₁, e₁, p₁, mem₁, v₁, low₁⟩ := genE_exec (en := en) e 0 m t hok hinv (Slice.Lower.At.left hat)
  have h7 : m₁.get 7 = W64.ofNat dataBase := by rw [low₁ 7 (by omega)]; exact hinv.1
  have hsd : fetchI C m₁.pc = some (.sd 8 7 (Int.ofNat (8 * n))) := by
    have h := (Slice.Lower.At.right hat).head
    rwa [genE_length, ← p₁] at h
  have hs := step_sd (en := en) hsd hn (addImm_slot h7 hn)
  have hinv₁ : Inv m₁ t := Inv.mono_mem hinv (low₁ 7 (by omega)) mem₁
  have hv : m₁.get 8 = evalS e t := v₁
  have hI := inv_store hinv₁ hn (m₁.pc + 4) (m₁.get 8)
  rw [hv] at hI hs
  exact ⟨_, e₁.trans (Exec.stepAt hs p₁), by simp only [p₁]; omega, hI⟩

/-- **`x := a[e]`.** -/
theorem exec_load {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {x : Nat} {e : SExpr} (hx : x < wordsMax)
    (hok : okE e 0 = true) (hinv : Inv m t)
    (hat : At C m.pc (genIdx e ++ [.ld 8 8 (Int.ofNat 512), .sd 8 7 (Int.ofNat (8 * x))])) :
    ∃ m', Exec C en (mIdx e m.pc ++ [(m.pc + 4 * (sE e + 5), [.addr (Int.ofNat (arrAddr (idx (evalS e t))))]),
        (m.pc + 4 * (sE e + 5) + 4, [.addr (Int.ofNat (slotAddr x))])]) m m' ∧
      m'.pc = m.pc + 4 * (sE e + 5 + 2) ∧ Inv m' (updS t x (t (arrBase + idx (evalS e t)))) := by
  obtain ⟨m₁, e₁, p₁, mem₁, h7₁, v₁⟩ := idx_exec (en := en) e m t hok hinv (Slice.Lower.At.left hat)
  have hi : idx (evalS e t) < 64 := Slots.idx_lt _
  have hinv₁ : Inv m₁ t := Inv.mono_mem hinv h7₁ mem₁
  have atT : At C m₁.pc [.ld 8 8 (Int.ofNat 512), .sd 8 7 (Int.ofNat (8 * x))] := by
    have := Slice.Lower.At.right hat
    rwa [genIdx_length, ← p₁] at this
  have s₁ := step_ld (en := en) (n := arrBase + idx (evalS e t)) atT.head (arr_lt hi) (addImm_arr hi v₁)
  have hload : load8 m₁ (slotAddr (arrBase + idx (evalS e t))) = t (arrBase + idx (evalS e t)) := hinv₁.2 _ (arr_lt hi)
  rw [hload] at s₁
  let m₂ : Mach := { m₁ with pc := m₁.pc + 4, x := m₁.set 8 (t (arrBase + idx (evalS e t))) }
  have h7₂ : m₂.get 7 = W64.ofNat dataBase := by
    simp only [m₂]; rw [get_set (by omega)]
    simp only [show (7 : Nat) ≠ 8 by omega, ↓reduceIte]; exact hinv₁.1
  have hv₂ : m₂.get 8 = t (arrBase + idx (evalS e t)) := by
    simp only [m₂]; rw [get_set (by omega)]; simp
  have hinv₂ : Inv m₂ t := Inv.mono_mem hinv₁ (by rw [h7₂]; exact hinv₁.1.symm) rfl
  have f₂ : fetchI C m₂.pc = some (.sd 8 7 (Int.ofNat (8 * x))) := At.get atT (j := 1) (by simp) rfl (by simp only [m₂])
  have s₂ := step_sd (en := en) f₂ hx (addImm_slot h7₂ hx)
  have hI := inv_store hinv₂ hx (m₂.pc + 4) (m₂.get 8)
  rw [hv₂] at hI s₂
  refine ⟨_, e₁.trans ((Exec.stepAt s₁ p₁).trans (Exec.stepAt s₂ (show m₂.pc = m.pc + 4 * (sE e + 5) + 4 by simp only [m₂, p₁]))), ?_, hI⟩
  simp only [m₂, p₁]; omega

/-- Peeling one base-256 digit. -/
theorem digS (b r j : Nat) (hb : b < 256) : (b + 256 * r) / 256 ^ (j + 1) % 256 = r / 256 ^ j % 256 := by
  rw [Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
    Nat.div_eq_of_lt hb, Nat.zero_add]

theorem dig0 (b r : Nat) (hb : b < 256) : (b + 256 * r) / 256 ^ 0 % 256 = b := by
  rw [Nat.pow_zero, Nat.div_one]; omega

/-- **Byte `j` of a word in memory is the memory byte** at its address plus `j`. -/
theorem load8_byte (m : Mach) (a j : Nat) (ha : a + 8 < 18446744073709551616) (hj : j < 8) :
    (load8 m a).val / 256 ^ j % 256 = (m.mem (a + j)).val := by
  rw [Slice.Lower.load8_val m a ha]
  have b0 := (m.mem a).isLt
  have b1 := (m.mem (a + 1)).isLt
  have b2 := (m.mem (a + 2)).isLt
  have b3 := (m.mem (a + 3)).isLt
  have b4 := (m.mem (a + 4)).isLt
  have b5 := (m.mem (a + 5)).isLt
  have b6 := (m.mem (a + 6)).isLt
  have b7 := (m.mem (a + 7)).isLt
  simp only [W64.ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (b := 18446744073709551616)]
  rotate_left
  · omega
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  · rw [dig0 _ _ b0]; rfl
  · rw [digS _ _ _ b0, dig0 _ _ b1]
  · rw [digS _ _ _ b0, digS _ _ _ b1, dig0 _ _ b2]
  · rw [digS _ _ _ b0, digS _ _ _ b1, digS _ _ _ b2, dig0 _ _ b3]
  · rw [digS _ _ _ b0, digS _ _ _ b1, digS _ _ _ b2, digS _ _ _ b3, dig0 _ _ b4]
  · rw [digS _ _ _ b0, digS _ _ _ b1, digS _ _ _ b2, digS _ _ _ b3, digS _ _ _ b4, dig0 _ _ b5]
  · rw [digS _ _ _ b0, digS _ _ _ b1, digS _ _ _ b2, digS _ _ _ b3, digS _ _ _ b4, digS _ _ _ b5, dig0 _ _ b6]
  · rw [digS _ _ _ b0, digS _ _ _ b1, digS _ _ _ b2, digS _ _ _ b3, digS _ _ _ b4, digS _ _ _ b5, digS _ _ _ b6, dig0 _ _ b7]
  · omega

/-- **The mask is the index modulo the array's bytes**, for the lengths `maskOK` allows. -/
theorem mask_mod (v : W64) {len : Nat} (hm : maskOK len = true) :
    (W64.and v (wordOfInt (Int.ofNat (8 * len - 1)))).val = v.val % (8 * len) := by
  simp only [maskOK, Bool.or_eq_true, beq_iff_eq] at hm
  have hlt : v.val % (8 * len) < 2 ^ 64 := by
    have := Nat.mod_lt v.val (show 0 < 8 * len by omega); omega
  rcases hm with ((rfl | rfl) | rfl) | rfl
  all_goals
    simp only [W64.and, W64.ofNat]
    rw [wordOfInt_val _ (by omega)]
  · rw [show 8 * 1 - 1 = 2 ^ 3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt hlt
  · rw [show 8 * 2 - 1 = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt hlt
  · rw [show 8 * 4 - 1 = 2 ^ 5 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt hlt
  · rw [show 8 * 8 - 1 = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt hlt

/-- A byte load inside the data segment, whatever the environment. -/
theorem step_lbu {C : List Byte} {en : Env} {m : Mach} {rd a : Nat} {i : Int} {addr : Nat} (h : fetchI C m.pc = some (.lbu rd a i))
    (ha : addImm (m.get a) i = addr) (hd : inData addr = true) :
    Slice.Rv.step C en m = .next [.addr (Int.ofNat addr)] { m with pc := m.pc + 4, x := m.set rd (W64.ofNat (m.mem addr).val) } := by
  obtain ⟨w, hf, hdc⟩ := fetchI_parts h
  have hr : canRead C en addr = true := by simp [canRead, hd]
  simp only [Slice.Rv.step, hf, hdc, ha, hr, ↓reduceIte]

/-- **`x := names[e]`**: the index, masked, plus the data segment's base, one `lbu`, and a store into `x`'s slot. -/
theorem exec_loadB {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {x b len : Nat} {e : SExpr}
    (hx : x < wordsMax) (hok : okE e 0 = true) (hm : maskOK len = true) (hb : b + len ≤ 64) (hinv : Inv m t)
    (hat : At C m.pc (genC (.loadB x (List.range' b len) e))) :
    ∃ m', Exec C en (mE e m.pc ++ [(m.pc + 4 * sE e, []), (m.pc + 4 * sE e + 4, []),
        (m.pc + 4 * sE e + 8, [.addr (Int.ofNat (dataBase + 8 * b + Slots.bidxS (List.range' b len) (evalS e t)))]),
        (m.pc + 4 * sE e + 12, [.addr (Int.ofNat (slotAddr x))])]) m m' ∧
      m'.pc = m.pc + 4 * (sE e + 4) ∧
      Inv m' (updS t x (Slots.byteAtS t (List.range' b len) (Slots.bidxS (List.range' b len) (evalS e t)))) := by
  have hlen : 0 < len ∧ len ≤ 8 := by simp only [maskOK, Bool.or_eq_true, beq_iff_eq] at hm; omega
  have hhead : (List.range' b len).headD 0 = b := by
    obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
    simp [List.range'_succ]
  have hlen' : (List.range' b len).length = len := List.length_range'
  simp only [genC, hhead, hlen'] at hat
  have atE := Slice.Lower.At.left (a := genE e 0) hat
  have atT : At C (m.pc + 4 * sE e) [.andi 8 8 (Int.ofNat (8 * len - 1)), .add 8 8 7, .lbu 8 8 (Int.ofNat (8 * b)), .sd 8 7 (Int.ofNat (8 * x))] := by
    have := Slice.Lower.At.right (a := genE e 0) hat
    rwa [genE_length] at this
  obtain ⟨m₁, e₁, p₁, mem₁, v₁, low₁⟩ := genE_exec (en := en) e 0 m t hok hinv atE
  have h7₁ : m₁.get 7 = W64.ofNat dataBase := by rw [low₁ 7 (by omega)]; exact hinv.1
  have hv₁ : m₁.get 8 = evalS e t := v₁
  generalize hI : Slots.bidxS (List.range' b len) (evalS e t) = i
  have hi : i < 8 * len := by
    rw [← hI]; simp only [Slots.bidxS, hlen']; exact Nat.mod_lt _ (by omega)
  have hdb : dataBase = 0x20000 := rfl
  -- andi
  have fa : fetchI C m₁.pc = some (.andi 8 8 (Int.ofNat (8 * len - 1))) := At.get atT (j := 0) (by simp) rfl (by rw [p₁]; omega)
  let m₂ : Mach := { m₁ with pc := m₁.pc + 4, x := m₁.set 8 (W64.and (m₁.get 8) (wordOfInt (Int.ofNat (8 * len - 1)))) }
  have s₂ : Slice.Rv.step C en m₁ = .next [] m₂ := step_andi fa
  have v₂ : m₂.get 8 = W64.ofNat i := by
    simp only [m₂]
    rw [get_set (by omega)]
    simp only [↓reduceIte, hv₁]
    apply Fin.ext
    rw [mask_mod _ hm, ← hI, ofNat_val (by omega)]
    simp only [Slots.bidxS, hlen']
  have l₂ : ∀ y, y < 8 → m₂.get y = m₁.get y := by
    intro y hy; simp only [m₂]; rw [get_set (by omega)]; simp [show y ≠ 8 by omega]
  -- add 8 8 7
  have f₃ : fetchI C m₂.pc = some (.add 8 8 7) := At.get atT (j := 1) (by simp) rfl (by simp only [m₂, p₁])
  let m₃ : Mach := { m₂ with pc := m₂.pc + 4, x := m₂.set 8 (W64.add (m₂.get 8) (m₂.get 7)) }
  have s₃ : Slice.Rv.step C en m₂ = .next [] m₃ := step_add f₃
  have v₃ : m₃.get 8 = W64.ofNat (i + dataBase) := by
    simp only [m₃]
    rw [get_set (by omega)]
    simp only [↓reduceIte, v₂, l₂ 7 (by omega), h7₁]
    exact add_ofNat (by omega) (by omega) (by omega)
  have l₃ : ∀ y, y < 8 → m₃.get y = m₁.get y := by
    intro y hy; simp only [m₃]; rw [get_set (by omega)]; simp [show y ≠ 8 by omega, l₂ y hy]
  -- lbu
  have f₄ : fetchI C m₃.pc = some (.lbu 8 8 (Int.ofNat (8 * b))) := At.get atT (j := 2) (by simp) rfl (by simp only [m₃, m₂, p₁] <;> omega)
  have haddr : addImm (m₃.get 8) (Int.ofNat (8 * b)) = dataBase + 8 * b + i := by
    rw [v₃, addImm_val _ _ (by rw [ofNat_val (by omega)]; omega), ofNat_val (by omega)]; omega
  have hin : inData (dataBase + 8 * b + i) = true := by
    have : wordsMax = 256 := rfl
    have hs : dataSize = 4096 := rfl
    simp only [inData, Bool.and_eq_true, decide_eq_true_eq]; omega
  have s₄ := step_lbu (en := en) f₄ haddr hin
  let m₄ : Mach := { m₃ with pc := m₃.pc + 4, x := m₃.set 8 (W64.ofNat (m₃.mem (dataBase + 8 * b + i)).val) }
  have h7₄ : m₄.get 7 = W64.ofNat dataBase := by
    simp only [m₄]; rw [get_set (by omega)]; simp only [show (7 : Nat) ≠ 8 by omega, ↓reduceIte, l₃ 7 (by omega), h7₁]
  have mem₄ : m₄.mem = m.mem := by simp only [m₄, m₃, m₂, mem₁]
  have hinv₄ : Inv m₄ t := Inv.mono_mem hinv (by rw [h7₄]; exact hinv.1.symm) mem₄
  -- the byte is the slot word's
  have hw : i / 8 < len := by omega
  have hbyte : Slots.byteAtS t (List.range' b len) i = W64.ofNat (m.mem (dataBase + 8 * b + i)).val := by
    simp only [Slots.byteAtS, List.getElem?_range' hw, Nat.one_mul, byteOfWord]
    have hsl : b + i / 8 < wordsMax := by have : wordsMax = 256 := rfl; omega
    rw [← hinv.2 _ hsl]
    rw [load8_byte m _ (i % 8) (by simp only [slotAddr]; omega) (Nat.mod_lt _ (by omega))]
    have hA : slotAddr (b + i / 8) + i % 8 = dataBase + 8 * b + i := by simp only [slotAddr]; omega
    rw [hA]
  have hv₄ : m₄.get 8 = Slots.byteAtS t (List.range' b len) i := by
    simp only [m₄]; rw [get_set (by omega)]
    simp only [↓reduceIte, hbyte, m₃, m₂, mem₁]
  -- sd
  have f₅ : fetchI C m₄.pc = some (.sd 8 7 (Int.ofNat (8 * x))) := At.get atT (j := 3) (by simp) rfl (by simp only [m₄, m₃, m₂, p₁] <;> omega)
  have s₅ := step_sd (en := en) f₅ hx (addImm_slot h7₄ hx)
  have hI5 := inv_store hinv₄ hx (m₄.pc + 4) (m₄.get 8)
  rw [hv₄] at hI5 s₅
  refine ⟨_, e₁.trans ((Exec.stepAt s₂ p₁).trans ((Exec.stepAt s₃ (by simp only [m₂, p₁])).trans
    ((Exec.stepAt s₄ (by simp only [m₃, m₂, p₁] <;> omega)).trans (Exec.stepAt s₅ (by simp only [m₄, m₃, m₂, p₁] <;> omega))))), ?_, hI5⟩
  simp only [m₄, m₃, m₂, p₁]; omega

/-- **`a[e] := v`.** -/
theorem exec_store {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {e v : SExpr}
    (hok : okE e 0 = true) (hov : okE v 1 = true) (hinv : Inv m t)
    (hat : At C m.pc (genIdx e ++ genE v 1 ++ [.sd 9 8 (Int.ofNat 512)])) :
    ∃ m', Exec C en (mIdx e m.pc ++ mE v (m.pc + 4 * (sE e + 5)) ++
        [(m.pc + 4 * (sE e + 5) + 4 * sE v, [.addr (Int.ofNat (arrAddr (idx (evalS e t))))])]) m m' ∧
      m'.pc = m.pc + 4 * (sE e + 5 + sE v + 1) ∧ Inv m' (updS t (arrBase + idx (evalS e t)) (evalS v t)) := by
  have at1 := Slice.Lower.At.left hat
  obtain ⟨m₁, e₁, p₁, mem₁, h7₁, v₁⟩ := idx_exec (en := en) e m t hok hinv (Slice.Lower.At.left at1)
  have hi : idx (evalS e t) < 64 := Slots.idx_lt _
  have hinv₁ : Inv m₁ t := Inv.mono_mem hinv h7₁ mem₁
  have at2 : At C m₁.pc (genE v 1) := by
    have := Slice.Lower.At.right at1
    rwa [genIdx_length, ← p₁] at this
  obtain ⟨m₂, e₂, p₂, mem₂, v₂, low₂⟩ := genE_exec (en := en) v 1 m₁ t hov hinv₁ at2
  have hinv₂ : Inv m₂ t := Inv.mono_mem hinv₁ (low₂ 7 (by omega)) mem₂
  have h8 : m₂.get 8 = W64.ofNat (dataBase + 8 * idx (evalS e t)) := by rw [low₂ 8 (by omega)]; exact v₁
  have hv : m₂.get 9 = evalS v t := v₂
  have f₃ : fetchI C m₂.pc = some (.sd 9 8 (Int.ofNat 512)) := by
    have h := (Slice.Lower.At.right hat).head
    simp only [List.length_append, genIdx_length, genE_length] at h
    rw [p₂, p₁]
    rw [show m.pc + 4 * (sE e + 5) + 4 * sE v = m.pc + 4 * (sE e + 5 + sE v) by omega]
    exact h
  have s₃ := step_sd (en := en) (n := arrBase + idx (evalS e t)) f₃ (arr_lt hi) (addImm_arr hi h8)
  have hI := inv_store hinv₂ (arr_lt hi) (m₂.pc + 4) (m₂.get 9)
  rw [hv] at hI s₃
  have e₂' : Exec C en (mE v (m.pc + 4 * (sE e + 5))) m₁ m₂ := by rw [← p₁]; exact e₂
  have hpc : m₂.pc = m.pc + 4 * (sE e + 5) + 4 * sE v := by rw [p₂, p₁]
  refine ⟨_, ((e₁.trans e₂').trans (Exec.stepAt s₃ hpc)), ?_, hI⟩
  simp only [hpc]; omega

/-- **A guard and its branch**: forward if the guard is zero. -/
theorem exec_guard {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {e : SExpr} {off : Nat}
    (hC : C.length ≤ 3000) (hoff : off < 4096) (hok : okE e 0 = true) (hinv : Inv m t)
    (hat : At C m.pc (genE e 0 ++ [.beq 8 0 (Int.ofNat off)])) :
    ∃ m', Exec C en (mE e m.pc ++ [(m.pc + 4 * sE e, [])]) m m' ∧ Inv m' t ∧
      m'.pc = (if (evalS e t).val ≠ 0 then m.pc + 4 * (sE e + 1) else m.pc + 4 * sE e + off) := by
  obtain ⟨m₁, e₁, p₁, mem₁, v₁, low₁⟩ := genE_exec (en := en) e 0 m t hok hinv (Slice.Lower.At.left hat)
  have hinv₁ : Inv m₁ t := Inv.mono_mem hinv (low₁ 7 (by omega)) mem₁
  have hb : fetchI C m₁.pc = some (.beq 8 0 (Int.ofNat off)) := by
    have h := (Slice.Lower.At.right hat).head
    rwa [genE_length, ← p₁] at h
  have hbd := fetchI_bound hb
  have hcb : codeBase = 0x100b0 := rfl
  have hs := step_beq (en := en) hb
  have hv : m₁.get 8 = evalS e t := v₁
  have hpv : (W64.ofNat m₁.pc).val = m₁.pc := ofNat_val (by omega)
  have ha : addImm (W64.ofNat m₁.pc) (Int.ofNat off) = m₁.pc + off := by
    rw [addImm_val _ _ (by rw [hpv]; omega), hpv]
  refine ⟨_, e₁.trans (Exec.stepAt hs p₁), Inv.mono_mem hinv₁ rfl rfl, ?_⟩
  by_cases hg : (evalS e t).val ≠ 0
  · have hne : m₁.get 8 ≠ m₁.get 0 := by
      rw [hv, get_zero]
      intro h; apply hg; rw [h]; rfl
    simp only [hne, hg, ne_eq, not_false_eq_true, ↓reduceIte, p₁]
    omega
  · have heq : m₁.get 8 = m₁.get 0 := by
      rw [hv, get_zero]
      apply Fin.ext
      have h0 : (evalS e t).val = 0 := by simpa using hg
      rw [h0]; rfl
    show (if m₁.get 8 = m₁.get 0 then addImm (W64.ofNat m₁.pc) (Int.ofNat off) else m₁.pc + 4) = _
    rw [if_pos heq, ha, if_neg hg, p₁]

end LCore.Slice2.Lower
