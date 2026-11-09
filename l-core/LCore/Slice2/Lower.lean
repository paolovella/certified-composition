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
  | .loop e b =>
    -- CAP-01 4b: a body past `beq`'s reach takes the long form, three instructions at the head and a `jal` back
    if decide (sC b + 2 < 1024) && decide (sE e + 1 + sC b < 1024) then sE e + 1 + sC b + 1 else sE e + 3 + sC b + 1
  | .load _ e => sE e + 5 + 2
  | .loadB _ _ e => sE e + 4
  | .store e v => sE e + 5 + sE v + 1
  | .storeB _ e v => sE e + 2 + sE v + 1
  | .emitB _ => 5

/-- **Does a loop take the short form**, a `beq` each way: its body and its back edge within `beq`'s ±4 KB. -/
def shortLoop (e : SExpr) (b : SCmd) : Bool := decide (sC b + 2 < 1024) && decide (sE e + 1 + sC b < 1024)

theorem sC_loop (e : SExpr) (b : SCmd) :
    sC (.loop e b) = if shortLoop e b then sE e + 1 + sC b + 1 else sE e + 3 + sC b + 1 := rfl

/-- **A `jal x0, i` that decodes to itself**, checked per program by `decide`, as `litPlan` checks literals (CAP-01). -/
def jalOk (i : Int) : Bool :=
  decide (decode (encode (.jal 0 i)) = some (.jal 0 i)) && decide (encode (.jal 0 i) < 4294967296)

/-- The long loop's three jumps: over the far jump, to the exit, and back to the head. -/
def longOk (e : SExpr) (b : SCmd) : Bool :=
  jalOk (Int.ofNat 8) && jalOk (Int.ofNat (4 * (sC b + 2))) && jalOk (-(Int.ofNat (4 * (sE e + 3 + sC b))))

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
    if shortLoop e b then
      genE e 0 ++ [.beq 8 0 (Int.ofNat (4 * (sC b + 2)))] ++ genC b ++ [.beq 0 0 (-(Int.ofNat (4 * (sE e + 1 + sC b))))]
    else
      genE e 0 ++ [.beq 8 0 (Int.ofNat 8), .jal 0 (Int.ofNat 8), .jal 0 (Int.ofNat (4 * (sC b + 2)))] ++ genC b ++
        [.jal 0 (-(Int.ofNat (4 * (sE e + 3 + sC b))))]
  | .load x e => genIdx e ++ [.ld 8 8 (Int.ofNat 512), .sd 8 7 (Int.ofNat (8 * x))]
  | .loadB x ws e =>
    genE e 0 ++ [.andi 8 8 (Int.ofNat (8 * ws.length - 1)), .add 8 8 7, .lbu 8 8 (Int.ofNat (8 * ws.headD 0)), .sd 8 7 (Int.ofNat (8 * x))]
  | .store e v => genIdx e ++ genE v 1 ++ [.sd 9 8 (Int.ofNat 512)]
  | .storeB ws e v =>
    genE e 0 ++ [.andi 8 8 (Int.ofNat (8 * ws.length - 1)), .add 8 8 7] ++ genE v 1 ++ [.sb 9 8 (Int.ofNat (8 * ws.headD 0))]
  | .emitB ws =>
    [.addi 10 0 (Int.ofNat 1), .addi 11 7 (Int.ofNat (8 * ws.headD 0)), .addi 12 0 (Int.ofNat (8 * ws.length)), .addi 17 0 (Int.ofNat 64), .ecall]

/-- A byte array's length, in words, for which the mask `8 * len - 1` is the index modulo its bytes. -/
def maskOK (len : Nat) : Bool := len == 1 || len == 2 || len == 4 || len == 8

def okC : SCmd → Bool
  | .skip => true
  | .set n e => decide (n < wordsMax) && okE e 0
  | .seq a b => okC a && okC b
  | .ite e a b => okE e 0 && okC a && okC b && decide (sC a + 2 < 1024) && decide (sC b + 1 < 1024)
  | .loop e b => okE e 0 && okC b && (shortLoop e b || longOk e b)
  | .load x e => decide (x < wordsMax) && okE e 0
  | .loadB x ws e => decide (x < wordsMax) && okE e 0 && decide (ws = List.range' (ws.headD 0) ws.length) && maskOK ws.length &&
      decide (ws.headD 0 + ws.length ≤ 64)
  | .store e v => okE e 0 && okE v 1
  | .storeB ws e v => okE e 0 && okE v 1 && decide (ws = List.range' (ws.headD 0) ws.length) && maskOK ws.length &&
      decide (ws.headD 0 + ws.length ≤ 64)
  | .emitB ws => decide (ws = List.range' (ws.headD 0) ws.length) && decide (0 < ws.length) && decide (ws.length ≤ 8) &&
      decide (ws.headD 0 + ws.length ≤ 64)

theorem genIdx_length (e : SExpr) : (genIdx e).length = sE e + 5 := by
  simp only [genIdx, List.length_append, genE_length, List.length_cons, List.length_nil]

theorem genC_length : ∀ c : SCmd, (genC c).length = sC c
  | .skip => rfl
  | .set n e => by simp only [genC, sC, List.length_append, genE_length]; rfl
  | .seq a b => by simp only [genC, sC, List.length_append, genC_length a, genC_length b]
  | .ite e a b => by simp only [genC, sC, List.length_append, genE_length, genC_length a, genC_length b]; rfl
  | .loop e b => by
    rw [sC_loop]
    simp only [genC]
    split
    · simp only [List.length_append, genE_length, genC_length b]; rfl
    · simp only [List.length_append, genE_length, genC_length b, List.length_cons, List.length_nil]
  | .load x e => by simp only [genC, sC, List.length_append, genIdx_length]; rfl
  | .loadB x ws e => by simp only [genC, sC, List.length_append, genE_length, List.length_cons, List.length_nil]
  | .store e v => by simp only [genC, sC, List.length_append, genIdx_length, genE_length]; rfl
  | .storeB ws e v => by simp only [genC, sC, List.length_append, genE_length, List.length_cons, List.length_nil]
  | .emitB ws => rfl

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
    simp only [okC, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h34⟩ := h
    simp only [genC] at hi
    split at hi
    · rename_i hs
      simp only [shortLoop, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with ((hi | hi) | hi) | hi
      · exact genE_good e 0 h1 i hi
      · subst hi; exact good_beq (by omega) (by omega) (by omega) (by omega)
      · exact genC_good b h2 i hi
      · subst hi
        exact good_beq_back (by omega) (by omega) (by omega) (by omega) (by omega)
    · rename_i hs
      have hl : longOk e b = true := by
        rcases h34 with h | h
        · exact absurd h hs
        · exact h
      have jal_good : ∀ j : Int, jalOk j = true → Good (.jal 0 j) := by
        intro j hj
        simp only [jalOk, Bool.and_eq_true] at hj
        exact ⟨of_decide_eq_true hj.1, of_decide_eq_true hj.2⟩
      simp only [longOk, Bool.and_eq_true] at hl
      obtain ⟨⟨k1, k2⟩, k3⟩ := hl
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with ((hi | hi | hi | hi) | hi) | hi
      · exact genE_good e 0 h1 i hi
      · subst hi; exact good_beq (by omega) (by omega) (by omega) (by omega)
      · subst hi; exact jal_good _ k1
      · subst hi; exact jal_good _ k2
      · exact genC_good b h2 i hi
      · subst hi; exact jal_good _ k3
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
  | .storeB ws e v, h, i, hi => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨he, hv⟩, _⟩, hm⟩, hb⟩ := h
    have hlen : ws.length ≤ 8 := by simp only [maskOK, Bool.or_eq_true, beq_iff_eq] at hm; omega
    simp only [genC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((hi | hi | hi) | hi) | hi
    · exact genE_good e 0 he i hi
    · subst hi; exact good_andi (by omega) (by omega) (by omega)
    · subst hi; exact Slice.Lower.good_add (by omega) (by omega) (by omega)
    · exact genE_good v 1 hv i hi
    · subst hi; exact Slice.Lower.good_sb (by omega) (by omega) (by omega)
  | .emitB ws, h, i, hi => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨_, _⟩, hl⟩, hb⟩ := h
    simp only [genC, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi | hi | hi
    all_goals subst hi
    · exact good_addi (by omega) (by omega) (by omega)
    · exact good_addi (by omega) (by omega) (by omega)
    · exact good_addi (by omega) (by omega) (by omega)
    · exact good_addi (by omega) (by omega) (by omega)
    · exact Slice.Lower.good_ecall

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

/-- A `jal x0, i`: a jump, no link (CAP-01 4b). -/
theorem step_jal0 {C : List Byte} {en : Env} {m : Mach} {i : Int} (h : fetchI C m.pc = some (.jal 0 i)) :
    Slice.Rv.step C en m = .next [] { m with pc := addImm (W64.ofNat m.pc) i } := by
  obtain ⟨w, hf, hd⟩ := fetchI_parts h
  simp only [Slice.Rv.step, hf, hd]
  rfl

/-- **A guard and its branch**: forward if the guard is zero. -/
theorem exec_guard {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {e : SExpr} {off : Nat}
    (hC : C.length ≤ 65360) (hoff : off < 4096) (hok : okE e 0 = true) (hinv : Inv m t)
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

/-! ## RC-02: a byte store, and `write` as an event -/

/-- Events, in front of a run's. -/
def addEv (evs : List Ev) (r : Beh) : Beh := { r with ev := evs ++ r.ev }

/-- **From `m` the machine plays `c`, emitting `evs` at its last micro-step, and arrives at `m'`.** With no events it is `Exec`. -/
def ExecE (C : List Byte) (en : Env) (c : List Micro) (evs : List Ev) (m m' : Mach) : Prop :=
  ∀ n, Slice.Rv.run C en n m = playApp c (fun k => addEv evs (Slice.Rv.run C en k m')) n

theorem ExecE.ofExec {C : List Byte} {en : Env} {c : List Micro} {m m' : Mach} (h : Exec C en c m m') : ExecE C en c [] m m' :=
  fun n => h n

theorem ExecE.pre {C : List Byte} {en : Env} {a b : List Micro} {evs : List Ev} {m m₁ m₂ : Mach}
    (h₁ : Exec C en a m m₁) (h₂ : ExecE C en b evs m₁ m₂) : ExecE C en (a ++ b) evs m m₂ := by
  intro n
  rw [playApp_append, h₁ n]
  have : (fun k => Slice.Rv.run C en k m₁) = playApp b (fun k => addEv evs (Slice.Rv.run C en k m₂)) := funext h₂
  rw [this]

/-- One step that emits an event. -/
theorem ExecE.out {C : List Byte} {en : Env} {m m' : Mach} {v : Ev} {l : List Lk} (h : Slice.Rv.step C en m = .out v l m') :
    ExecE C en [(m.pc, l)] [v] m m' := by
  intro n
  cases n with
  | zero => rfl
  | succ k => simp only [Slice.Rv.run, h]; rfl

/-- A byte store inside the data segment, whatever the environment. -/
theorem step_sb {C : List Byte} {en : Env} {m : Mach} {rv a : Nat} {i : Int} {addr : Nat} (h : fetchI C m.pc = some (.sb rv a i))
    (ha : addImm (m.get a) i = addr) (hd : inData addr = true) :
    Slice.Rv.step C en m = .next [.addr (Int.ofNat addr)]
      { m with pc := m.pc + 4, mem := fun b => if b = addr then byteOf (m.get rv).val else m.mem b } := by
  obtain ⟨w, hf, hdc⟩ := fetchI_parts h
  have hw : canWrite C en addr = true := by simp [canWrite, hd]
  simp only [Slice.Rv.step, hf, hdc, ha, hw, ↓reduceIte]

theorem foldr8_congr {f g : Nat → Nat} (h : ∀ i, i < 8 → f i = g i) :
    (List.range 8).foldr (fun i acc => f i + 256 * acc) 0 = (List.range 8).foldr (fun i acc => g i + 256 * acc) 0 := by
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [hr, List.foldr]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega),
    h 7 (by omega)]

/-- **A byte store at byte `j` of slot `n` is `setByte` on that slot's word**, and leaves the other slots alone. -/
theorem inv_storeB {m : Mach} {t : Slice.Slots.Slots} (hinv : Inv m t) {n j : Nat} (hn : n < wordsMax) (hj : j < 8) (q : Nat) (v : W64) :
    Inv { m with pc := q, mem := fun b => if b = slotAddr n + j then byteOf v.val else m.mem b }
      (updS t n (setByte (t n) j v)) := by
  have hmax : wordsMax = 256 := rfl
  have hA : ∀ k, k < wordsMax → slotAddr k + 8 < 18446744073709551616 := by
    intro k hk; simp only [slotAddr, dataBase]; omega
  refine ⟨hinv.1, fun k hk => ?_⟩
  have hmod : ∀ i, i < 8 → (slotAddr k + i) % 2 ^ 64 = slotAddr k + i := fun i hi =>
    Nat.mod_eq_of_lt (by have := hA k hk; omega)
  by_cases hkn : k = n
  · subst hkn
    have hu : updS t k (setByte (t k) j v) k = setByte (t k) j v := by simp [updS]
    rw [hu]
    unfold load8 setByte
    refine congrArg W64.ofNat (foldr8_congr fun i hi => ?_)
    simp only
    rw [hmod i hi]
    by_cases hij : i = j
    · subst hij; simp [byteOf]
    · have hne : slotAddr k + i ≠ slotAddr k + j := by omega
      simp only [hne, ↓reduceIte, hij]
      rw [← hinv.2 k hk, load8_byte m _ i (hA k hk) hi]
  · have hu : updS t n (setByte (t n) j v) k = t k := by simp [updS, hkn]
    rw [hu, ← hinv.2 k hk]
    unfold load8
    refine congrArg W64.ofNat (foldr8_congr fun i hi => ?_)
    have hne : slotAddr k + i ≠ slotAddr n + j := by
      simp only [slotAddr]; omega
    simp only
    rw [hmod i hi]
    simp [hne]

/-- **`names[e] := v`**: the index, masked, plus the data segment's base; the value; one `sb`. -/
theorem exec_storeB {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {b len : Nat} {e v : SExpr}
    (hok : okE e 0 = true) (hov : okE v 1 = true) (hm : maskOK len = true) (hb : b + len ≤ 64) (hinv : Inv m t)
    (hat : At C m.pc (genC (.storeB (List.range' b len) e v))) :
    ∃ m', Exec C en (mE e m.pc ++ [(m.pc + 4 * sE e, []), (m.pc + 4 * sE e + 4, [])] ++ mE v (m.pc + 4 * sE e + 8) ++
        [(m.pc + 4 * sE e + 8 + 4 * sE v, [.addr (Int.ofNat (dataBase + 8 * b + Slots.bidxS (List.range' b len) (evalS e t)))])]) m m' ∧
      m'.pc = m.pc + 4 * (sE e + 2 + sE v + 1) ∧
      Inv m' (Slots.storeAtS t (List.range' b len) (Slots.bidxS (List.range' b len) (evalS e t)) (evalS v t)) := by
  have hlen : 0 < len ∧ len ≤ 8 := by simp only [maskOK, Bool.or_eq_true, beq_iff_eq] at hm; omega
  have hhead : (List.range' b len).headD 0 = b := by
    obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
    simp [List.range'_succ]
  have hlen' : (List.range' b len).length = len := List.length_range'
  simp only [genC, hhead, hlen'] at hat
  have at3 := Slice.Lower.At.left hat
  have at2 := Slice.Lower.At.left at3
  have atE := Slice.Lower.At.left at2
  have atT : At C (m.pc + 4 * sE e) [.andi 8 8 (Int.ofNat (8 * len - 1)), .add 8 8 7] := by
    have := Slice.Lower.At.right at2
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
  have p₃ : m₃.pc = m.pc + 4 * sE e + 8 := by simp only [m₃, m₂, p₁]
  have mem₃ : m₃.mem = m.mem := by simp only [m₃, m₂, mem₁]
  have hinv₃ : Inv m₃ t := Inv.mono_mem hinv (by rw [l₃ 7 (by omega), h7₁]; exact hinv.1.symm) mem₃
  -- the value
  have atV : At C m₃.pc (genE v 1) := by
    have := Slice.Lower.At.right at3
    rw [p₃]
    simp only [List.length_append, genE_length, List.length_cons, List.length_nil] at this
    have e2 : m.pc + 4 * (sE e + (1 + 1)) = m.pc + 4 * sE e + 8 := by omega
    rwa [e2] at this
  obtain ⟨m₄, e₄, p₄, mem₄, v₄, low₄⟩ := genE_exec (en := en) v 1 m₃ t hov hinv₃ atV
  have h8₄ : m₄.get 8 = W64.ofNat (i + dataBase) := by rw [low₄ 8 (by omega)]; exact v₃
  have h9₄ : m₄.get 9 = evalS v t := v₄
  -- sb
  have atS : At C (m₃.pc + 4 * sE v) [.sb 9 8 (Int.ofNat (8 * b))] := by
    have := Slice.Lower.At.right hat
    rw [p₃]
    simp only [List.length_append, genE_length, List.length_cons, List.length_nil] at this
    have e2 : m.pc + 4 * (sE e + (1 + 1) + sE v) = m.pc + 4 * sE e + 8 + 4 * sE v := by omega
    rwa [e2] at this
  have f₅ : fetchI C m₄.pc = some (.sb 9 8 (Int.ofNat (8 * b))) := At.get atS (j := 0) (by simp) rfl (by rw [p₄]; omega)
  have haddr : addImm (m₄.get 8) (Int.ofNat (8 * b)) = dataBase + 8 * b + i := by
    rw [h8₄, addImm_val _ _ (by rw [ofNat_val (by omega)]; omega), ofNat_val (by omega)]; omega
  have hin : inData (dataBase + 8 * b + i) = true := by
    have hs : dataSize = 4096 := rfl
    simp only [inData, Bool.and_eq_true, decide_eq_true_eq]; omega
  have s₅ := step_sb (en := en) f₅ haddr hin
  have hw : i / 8 < len := by omega
  have hsl : b + i / 8 < wordsMax := by have : wordsMax = 256 := rfl; omega
  have hA : dataBase + 8 * b + i = slotAddr (b + i / 8) + i % 8 := by simp only [slotAddr]; omega
  have hinv₄ : Inv m₄ t := Inv.mono_mem hinv₃ (by rw [low₄ 7 (by omega)]) mem₄
  have hI5 := inv_storeB hinv₄ hsl (Nat.mod_lt i (by omega)) (m₄.pc + 4) (m₄.get 9)
  have hst : Slots.storeAtS t (List.range' b len) i (evalS v t) = updS t (b + i / 8) (setByte (t (b + i / 8)) (i % 8) (evalS v t)) := by
    simp only [Slots.storeAtS, List.getElem?_range' hw, Nat.one_mul]
  rw [← hA, h9₄] at hI5
  rw [h9₄] at s₅
  refine ⟨_, ((e₁.trans ((Exec.stepAt s₂ p₁).trans (Exec.stepAt s₃ (by simp only [m₂, p₁])))).trans
    (by rw [p₃] at e₄; exact e₄)).trans (Exec.stepAt s₅ (by rw [p₄, p₃])), ?_, ?_⟩
  · simp only; rw [p₄, p₃]; omega
  · rw [hst]; exact hI5

/-- The bytes of `len` consecutive words from word `b`, word by word, are the bytes from `8 * b`, in order. -/
theorem flat_range (g : Nat → Nat) : ∀ (len b : Nat),
    (List.range' b len).flatMap (fun w => (List.range 8).map (fun j => g (8 * w + j))) = (List.range (8 * len)).map (fun i => g (8 * b + i))
  | 0, _ => by simp
  | n + 1, b => by
    rw [List.range'_succ, List.flatMap_cons, flat_range g n (b + 1), show 8 * (n + 1) = 8 + 8 * n by omega, List.range_add,
      List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    congr 1
    omega

theorem flatMap_congr_mem {α β : Type} {F G : α → List β} : ∀ {l : List α}, (∀ x ∈ l, F x = G x) → l.flatMap F = l.flatMap G
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self, flatMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- **The bytes a `write` of slots `b` to `b + len - 1` reads are the slots' bytes.** -/
theorem out_bytes {m : Mach} {t : Slice.Slots.Slots} (hinv : Inv m t) {b len : Nat} (hb : b + len ≤ 64) :
    (List.range (8 * len)).map (fun i => (m.mem (dataBase + 8 * b + i)).val) = Slots.outBytesS t (List.range' b len) := by
  have hmax : wordsMax = 256 := rfl
  simp only [Slots.outBytesS]
  rw [flatMap_congr_mem (G := fun w => (List.range 8).map (fun j => (fun x => (m.mem (dataBase + x)).val) (8 * w + j)))]
  · rw [flat_range (fun x => (m.mem (dataBase + x)).val) len b]
    apply List.map_congr_left
    intro i _
    show (m.mem (dataBase + 8 * b + i)).val = (m.mem (dataBase + (8 * b + i))).val
    rw [Nat.add_assoc]
  · intro w hw
    have hw' : w < b + len := (List.mem_range'_1.mp hw).2
    apply List.map_congr_left
    intro j hj
    have hj' : j < 8 := List.mem_range.mp hj
    rw [← hinv.2 w (by omega), load8_byte m _ j (by simp only [slotAddr, dataBase]; omega) hj']
    simp only [slotAddr]
    congr 2
    omega

/-- Reading a register after a write: the written one, or the old value. -/
theorem get_upd_same (mm : Mach) (q r : Nat) (v : W64) (hr : r ≠ 0) : ({ mm with pc := q, x := mm.set r v } : Mach).get r = v := by
  rw [get_set hr]; simp

theorem get_upd_other (mm : Mach) (q r : Nat) (v : W64) {y : Nat} (hr : r ≠ 0) (hy : y ≠ r) :
    ({ mm with pc := q, x := mm.set r v } : Mach).get y = mm.get y := by
  rw [get_set hr]; simp [hy]

theorem addi0 (k : Nat) (hk : k < 2048) : W64.ofNat (addImm (W64.ofNat 0) (Int.ofNat k)) = W64.ofNat k := by
  rw [addImm_val _ _ (by rw [ofNat_val (by omega)]; omega), ofNat_val (by omega), Nat.zero_add]

/-- **`emitB`**: `a0 := 1`, `a1 := ` the first slot's address, `a2 := ` the bytes, `a7 := 64`, and the `ecall`, which emits them. -/
theorem exec_emitB {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {b len : Nat}
    (hl0 : 0 < len) (hl : len ≤ 8) (hb : b + len ≤ 64) (hinv : Inv m t) (hat : At C m.pc (genC (.emitB (List.range' b len)))) :
    ∃ m', ExecE C en [(m.pc, []), (m.pc + 4, []), (m.pc + 8, []), (m.pc + 12, []),
        (m.pc + 16, (List.range (8 * len)).map fun i => .addr (Int.ofNat (dataBase + 8 * b + i)))]
        [.emit "out" (Slots.outBytesS t (List.range' b len))] m m' ∧
      m'.pc = m.pc + 20 ∧ Inv m' t := by
  have hlen' : (List.range' b len).length = len := List.length_range'
  have hhead : (List.range' b len).headD 0 = b := by
    obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
    simp [List.range'_succ]
  simp only [genC, hlen', hhead] at hat
  have hdb : dataBase = 0x20000 := rfl
  have h7 : m.get 7 = W64.ofNat dataBase := hinv.1
  -- a0 := 1
  let m₁ : Mach := { m with pc := m.pc + 4, x := m.set 10 (W64.ofNat (addImm (m.get 0) (Int.ofNat 1))) }
  have s₁ : Slice.Rv.step C en m = .next [] m₁ := step_addi (At.get hat (j := 0) (by simp) rfl (by omega))
  have r₁10 : m₁.get 10 = W64.ofNat 1 := by rw [get_upd_same _ _ _ _ (by omega), get_zero, addi0 1 (by omega)]
  have r₁7 : m₁.get 7 = W64.ofNat dataBase := by rw [get_upd_other _ _ _ _ (by omega) (by omega), h7]
  -- a1 := x7 + 8b
  let m₂ : Mach := { m₁ with pc := m₁.pc + 4, x := m₁.set 11 (W64.ofNat (addImm (m₁.get 7) (Int.ofNat (8 * b)))) }
  have s₂ : Slice.Rv.step C en m₁ = .next [] m₂ := step_addi (At.get hat (j := 1) (by simp) rfl (by simp only [m₁]))
  have hdv : (W64.ofNat dataBase).val = dataBase := ofNat_val (by rw [hdb]; omega)
  have r₂11 : (m₂.get 11).val = dataBase + 8 * b := by
    rw [get_upd_same _ _ _ _ (by omega), r₁7, addImm_val (W64.ofNat dataBase) (8 * b) (by rw [hdv, hdb]; omega), hdv,
      ofNat_val (by rw [hdb]; omega)]
  have r₂10 : m₂.get 10 = W64.ofNat 1 := by rw [get_upd_other _ _ _ _ (by omega) (by omega), r₁10]
  -- a2 := 8 len
  let m₃ : Mach := { m₂ with pc := m₂.pc + 4, x := m₂.set 12 (W64.ofNat (addImm (m₂.get 0) (Int.ofNat (8 * len)))) }
  have s₃ : Slice.Rv.step C en m₂ = .next [] m₃ := step_addi (At.get hat (j := 2) (by simp) rfl (by simp only [m₂, m₁]))
  have r₃12 : m₃.get 12 = W64.ofNat (8 * len) := by rw [get_upd_same _ _ _ _ (by omega), get_zero, addi0 _ (by omega)]
  have r₃11 : (m₃.get 11).val = dataBase + 8 * b := by rw [get_upd_other _ _ _ _ (by omega) (by omega), r₂11]
  have r₃10 : m₃.get 10 = W64.ofNat 1 := by rw [get_upd_other _ _ _ _ (by omega) (by omega), r₂10]
  -- a7 := 64
  let m₄ : Mach := { m₃ with pc := m₃.pc + 4, x := m₃.set 17 (W64.ofNat (addImm (m₃.get 0) (Int.ofNat 64))) }
  have s₄ : Slice.Rv.step C en m₃ = .next [] m₄ := step_addi (At.get hat (j := 3) (by simp) rfl (by simp only [m₃, m₂, m₁]))
  have g17 : m₄.get 17 = sysWrite := by rw [get_upd_same _ _ _ _ (by omega), get_zero, addi0 64 (by omega)]; rfl
  have g12 : m₄.get 12 = W64.ofNat (8 * len) := by rw [get_upd_other _ _ _ _ (by omega) (by omega), r₃12]
  have g11 : (m₄.get 11).val = dataBase + 8 * b := by rw [get_upd_other _ _ _ _ (by omega) (by omega), r₃11]
  have g10 : m₄.get 10 = W64.ofNat 1 := by rw [get_upd_other _ _ _ _ (by omega) (by omega), r₃10]
  have g7 : m₄.get 7 = W64.ofNat dataBase := by
    rw [get_upd_other _ _ _ _ (by omega) (by omega), get_upd_other _ _ _ _ (by omega) (by omega),
      get_upd_other _ _ _ _ (by omega) (by omega), r₁7]
  have p₄ : m₄.pc = m.pc + 16 := by simp only [m₄, m₃, m₂, m₁]
  have mem₄ : m₄.mem = m.mem := rfl
  have g12v : (m₄.get 12).val = 8 * len := by rw [g12, ofNat_val (by omega)]
  -- the ecall
  have f₅ : fetchI C m₄.pc = some .ecall := At.get hat (j := 4) (by simp) rfl (by rw [p₄])
  obtain ⟨w, hf, hd⟩ := fetchI_parts f₅
  have hne : ¬ (m₄.get 17 = sysExit) := by rw [g17]; decide
  have has : ((List.range (m₄.get 12).val).map fun i => ((m₄.get 11).val + i) % 2 ^ 64) =
      (List.range (8 * len)).map fun i => dataBase + 8 * b + i := by
    rw [g12v, g11]
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.mp hi
    exact Nat.mod_eq_of_lt (by omega)
  have hall : (((List.range (m₄.get 12).val).map fun i => ((m₄.get 11).val + i) % 2 ^ 64).all (canRead C en)) = true := by
    rw [has, List.all_eq_true]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have := List.mem_range.mp hi
    have hs : dataSize = 4096 := rfl
    have hin : inData (dataBase + 8 * b + i) = true := by
      simp only [inData, Bool.and_eq_true, decide_eq_true_eq]; omega
    simp [canRead, hin]
  have hsz : (m₄.get 12).val ≤ dataSize := by
    have hs : dataSize = 4096 := rfl
    rw [g12v, hs]; omega
  have hcond : m₄.get 10 = W64.ofNat 1 ∧ (m₄.get 12).val ≤ dataSize ∧
      (((List.range (m₄.get 12).val).map fun i => ((m₄.get 11).val + i) % 2 ^ 64).all (canRead C en)) = true :=
    ⟨g10, hsz, hall⟩
  let m₅ : Mach := { m₄ with pc := m₄.pc + 4, x := m₄.set 10 (m₄.get 12) }
  have s₅ : Slice.Rv.step C en m₄ = .out (.emit "out" (Slots.outBytesS t (List.range' b len)))
      ((List.range (8 * len)).map fun i => .addr (Int.ofNat (dataBase + 8 * b + i))) m₅ := by
    simp only [Slice.Rv.step, hf, hd, hne, g17, ↓reduceIte, sysWriteStep]
    rw [if_pos hcond, has, List.map_map, List.map_map, ← out_bytes hinv hb, mem₄]
    rfl
  have hinv₅ : Inv m₅ t := Inv.mono_mem hinv (by rw [get_upd_other _ _ _ _ (by omega) (by omega), g7, h7]) rfl
  refine ⟨m₅, ?_, by simp only [m₅, p₄], hinv₅⟩
  have q₂ : m₂.pc = m.pc + 8 := by show m.pc + 4 + 4 = m.pc + 8; omega
  have q₃ : m₃.pc = m.pc + 12 := by show m.pc + 4 + 4 + 4 = m.pc + 12; omega
  have e := ExecE.pre ((Exec.step s₁).trans ((Exec.stepAt (q := m.pc + 4) s₂ rfl).trans ((Exec.stepAt (q := m.pc + 8) s₃ q₂).trans
    (Exec.stepAt (q := m.pc + 12) s₄ q₃)))) (ExecE.out s₅)
  rw [p₄] at e
  exact e

end LCore.Slice2.Lower
