/-
  VS-1 step 5: variables to slots, the first pass whose input changes form.

  The source's input is words by position. The target's is the data segment's bytes. So `cover` and `low_cover` really
  decode: every byte pattern, including two inputs differing inside one word, must be the encoding of a source input.
  Input `k` lives at slot `k` and locals start at slot 64, so `enc` needs no program and no table is hidden in the target
  program, which is how `P1` avoids the question.

  **What this judges.** The half of F3's kill rule about a changed input, and it holds. `E` is still passive: this
  language does not read it. The other half is step 6's, on the machine.

  It is a lockstep pass, so it says nothing yet about one step becoming many. That is also step 6.
-/
import LCore.Slice.Source
import LCore.Slice.Rv

namespace LCore.Slice.Slots

open Rv (Byte byteOf)

/-! ## The target language -/

inductive SExpr where
  | lit  : W64 → SExpr
  | slot : Nat → SExpr
  | add  : SExpr → SExpr → SExpr
  deriving DecidableEq, Repr

inductive SCmd where
  | skip : SCmd
  | set  : Nat → SExpr → SCmd
  | seq  : SCmd → SCmd → SCmd
  | ite  : SExpr → SCmd → SCmd → SCmd
  deriving DecidableEq, Repr

structure SProg where
  body : SCmd
  ret  : SExpr
  deriving DecidableEq, Repr

abbrev Slots := Nat → W64

def updS (t : Slots) (n : Nat) (v : W64) : Slots := fun m => if m = n then v else t m

def evalS : SExpr → Slots → W64
  | .lit w, _   => w
  | .slot n, t  => t n
  | .add a b, t => W64.add (evalS a t) (evalS b t)

abbrev SFrame := SCmd × List Nat

def pushS : SCmd → List Nat → List SFrame → List SFrame
  | .seq a b, p, k => pushS a (p ++ [0]) (pushS b (p ++ [1]) k)
  | c, p, k => (c, p) :: k

def runS (ret : SExpr) : Nat → List SFrame → Slots → Beh
  | _, [], t => { ev := [retEv (evalS ret t)], lk := [], cost := 0, out := .done }
  | 0, _ :: _, _ => { ev := [], lk := [], cost := 0, out := .fuel }
  | n + 1, (c, p) :: k, t =>
    match c with
    | .skip => tick [] p (runS ret n k t)
    | .set x e => tick [] p (runS ret n k (updS t x (evalS e t)))
    | .seq a b => runS ret n (pushS a (p ++ [0]) (pushS b (p ++ [1]) k)) t
    | .ite e a b =>
      if (evalS e t).val ≠ 0 then tick [.branch true] p (runS ret n (pushS a (p ++ [0]) k) t)
      else tick [.branch false] p (runS ret n (pushS b (p ++ [1]) k) t)

/-- The word at slot `k`: eight bytes, little-endian. -/
def wordAt (d : Nat → Byte) (k : Nat) : W64 :=
  W64.ofNat ((d (8 * k)).val + 256 * (d (8 * k + 1)).val + 65536 * (d (8 * k + 2)).val
    + 16777216 * (d (8 * k + 3)).val + 4294967296 * (d (8 * k + 4)).val
    + 1099511627776 * (d (8 * k + 5)).val + 281474976710656 * (d (8 * k + 6)).val
    + 72057594037927936 * (d (8 * k + 7)).val)

/-- **The slot language.** Its input is the data segment's bytes, with the rest of the segment zero. -/
def slotLang (E : Type) (P : Nat → Bool) : Lang where
  Prog  := SProg
  In    := (Nat → Byte) × E
  lowIn i i' := ∀ off, P (off / 8) = false → i.1 off = i'.1 off
  run n p i := runS p.ret n (pushS p.body [] []) (wordAt i.1)
  Adm i := ∀ off, Rv.inBytes ≤ off → i.1 off = byteOf 0

/-! ## Lawful -/

theorem runS_ext (ret : SExpr) : ∀ (n n' : Nat) (k : List SFrame) (t : Slots), n ≤ n' →
    Ext (runS ret n k t) (runS ret n' k t) := by
  intro n
  induction n with
  | zero =>
    intro n' k t _
    cases k with
    | nil => cases n' <;> exact Ext.refl _
    | cons f k => exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ m ih =>
    intro n' k t hle
    obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases k with
    | nil => exact Ext.refl _
    | cons f k =>
      obtain ⟨c, p⟩ := f
      cases c with
      | skip => exact tick_ext _ _ (ih m' _ t hm)
      | set x e => exact tick_ext _ _ (ih m' _ _ hm)
      | seq a b => exact ih m' _ t hm
      | ite e a b =>
        simp only [runS]
        split
        · exact tick_ext _ _ (ih m' _ t hm)
        · exact tick_ext _ _ (ih m' _ t hm)

def NoSeqS (k : List SFrame) : Prop := ∀ f ∈ k, ∀ a b, f.1 ≠ .seq a b

theorem pushS_noSeq : ∀ (c : SCmd) (p : List Nat) (k : List SFrame), NoSeqS k → NoSeqS (pushS c p k)
  | .seq a b, p, k, h => pushS_noSeq a _ _ (pushS_noSeq b _ k h)
  | .skip, _, k, h | .set _ _, _, k, h | .ite _ _ _, _, k, h => by
    intro f hf a b
    simp only [pushS, List.mem_cons] at hf
    rcases hf with rfl | hf
    · simp
    · exact h f hf a b

theorem runS_diverge (ret : SExpr) : ∀ (n : Nat) (k : List SFrame) (t : Slots), NoSeqS k →
    (runS ret n k t).out = .fuel → n ≤ (runS ret n k t).cost := by
  intro n
  induction n with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ m ih =>
    intro k t hk hf
    cases k with
    | nil => simp [runS] at hf
    | cons f k =>
      obtain ⟨c, p⟩ := f
      have hk' : NoSeqS k := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      cases c with
      | skip =>
        simp only [runS, tick] at hf ⊢
        have := ih k t hk' hf; omega
      | set x e =>
        simp only [runS, tick] at hf ⊢
        have := ih k _ hk' hf; omega
      | seq a b => exact absurd rfl (hk _ List.mem_cons_self a b)
      | ite e a b =>
        simp only [runS] at hf ⊢
        split at hf
        · rename_i hg; rw [if_pos hg]; simp only [tick] at hf ⊢
          have := ih _ t (pushS_noSeq _ _ _ hk') hf; omega
        · rename_i hg; rw [if_neg hg]; simp only [tick] at hf ⊢
          have := ih _ t (pushS_noSeq _ _ _ hk') hf; omega

theorem slotLang_lawful (E : Type) (P : Nat → Bool) : (slotLang E P).Lawful where
  ev_mono p i n n' h := (runS_ext _ n n' _ _ h).2.1
  lk_mono p i n n' h := (runS_ext _ n n' _ _ h).2.2.1
  cost_mono p i n n' h := (runS_ext _ n n' _ _ h).2.2.2
  stable p i n n' h hf := ((runS_ext _ n n' _ _ h).1 hf).symm
  diverge p := ⟨0, fun n i h =>
    runS_diverge _ n _ _ (pushS_noSeq _ _ _ (fun _ hx => by simp at hx)) h⟩

/-! ## The encoding: words to bytes, and back -/

/-- Each input word's bytes, in place. -/
def encBytes (v : Nat → W64) : Nat → Byte :=
  fun off => byteOf ((v (off / 8)).val / 256 ^ (off % 8))

theorem bytes_sum (V : Nat) (h : V < 18446744073709551616) :
    V % 256 + 256 * (V / 256 % 256) + 65536 * (V / 65536 % 256) + 16777216 * (V / 16777216 % 256)
      + 4294967296 * (V / 4294967296 % 256) + 1099511627776 * (V / 1099511627776 % 256)
      + 281474976710656 * (V / 281474976710656 % 256)
      + 72057594037927936 * (V / 72057594037927936 % 256) = V := by
  omega

/-- **Decoding an encoding gives the word back.** -/
theorem wordAt_enc (v : Nat → W64) (k : Nat) : wordAt (encBytes v) k = v k := by
  apply Fin.ext
  have hk : ∀ j, j < 8 → (8 * k + j) / 8 = k ∧ (8 * k + j) % 8 = j := by intro j hj; omega
  have h0 : (8 * k) / 8 = k ∧ (8 * k) % 8 = 0 := by omega
  have hv : (v k).val < 18446744073709551616 := (v k).isLt
  have hs := bytes_sum _ hv
  simp only [wordAt, encBytes, W64.ofNat, h0.1, h0.2,
    (hk 1 (by omega)).1, (hk 1 (by omega)).2, (hk 2 (by omega)).1, (hk 2 (by omega)).2,
    (hk 3 (by omega)).1, (hk 3 (by omega)).2, (hk 4 (by omega)).1, (hk 4 (by omega)).2,
    (hk 5 (by omega)).1, (hk 5 (by omega)).2, (hk 6 (by omega)).1, (hk 6 (by omega)).2,
    (hk 7 (by omega)).1, (hk 7 (by omega)).2, byteOf, Nat.reducePow]
  have h1 : (v k).val / 1 = (v k).val := Nat.div_one _
  rw [h1, hs]
  exact Nat.mod_eq_of_lt hv

/-- The value of eight bytes, and each byte back out of it. -/
theorem sum_lt (a b c d e f g h : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (he : e < 256) (hf : f < 256) (hg : g < 256) (hh : h < 256) :
    a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * e + 1099511627776 * f + 281474976710656 * g
      + 72057594037927936 * h < 18446744073709551616 := by
  omega

/-- **Encoding a decoding gives the bytes back**, for every byte pattern. This is what `cover` is. -/
theorem enc_wordAt (d : Nat → Byte) : encBytes (wordAt d) = d := by
  funext off
  apply Fin.ext
  obtain ⟨k, hk⟩ : ∃ k, off / 8 = k := ⟨_, rfl⟩
  have hb : ∀ x, (d x).val < 256 := fun x => (d x).isLt
  have hl := sum_lt _ _ _ _ _ _ _ _ (hb (8 * k)) (hb (8 * k + 1)) (hb (8 * k + 2)) (hb (8 * k + 3))
    (hb (8 * k + 4)) (hb (8 * k + 5)) (hb (8 * k + 6)) (hb (8 * k + 7))
  have h0 := hb (8 * k); have h1 := hb (8 * k + 1); have h2 := hb (8 * k + 2)
  have h3 := hb (8 * k + 3); have h4 := hb (8 * k + 4); have h5 := hb (8 * k + 5)
  have h6 := hb (8 * k + 6); have h7 := hb (8 * k + 7)
  have hval : (wordAt d k).val = (d (8 * k)).val + 256 * (d (8 * k + 1)).val + 65536 * (d (8 * k + 2)).val
      + 16777216 * (d (8 * k + 3)).val + 4294967296 * (d (8 * k + 4)).val
      + 1099511627776 * (d (8 * k + 5)).val + 281474976710656 * (d (8 * k + 6)).val
      + 72057594037927936 * (d (8 * k + 7)).val := by
    simp only [wordAt, W64.ofNat]
    exact Nat.mod_eq_of_lt hl
  show ((wordAt d (off / 8)).val / 256 ^ (off % 8)) % 256 = (d off).val
  rw [hk, hval]
  have hcase : off % 8 = 0 ∨ off % 8 = 1 ∨ off % 8 = 2 ∨ off % 8 = 3 ∨ off % 8 = 4 ∨ off % 8 = 5 ∨
      off % 8 = 6 ∨ off % 8 = 7 := by omega
  rcases hcase with c | c | c | c | c | c | c | c
  · have e : off = 8 * k := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega
  · have e : off = 8 * k + 1 := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega
  · have e : off = 8 * k + 2 := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega
  · have e : off = 8 * k + 3 := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega
  · have e : off = 8 * k + 4 := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega
  · have e : off = 8 * k + 5 := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega
  · have e : off = 8 * k + 6 := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega
  · have e : off = 8 * k + 7 := by omega
    rw [c, e]; simp only [Nat.reducePow]; omega

/-! ## The compiler -/

def evars : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .add a b => evars a ++ evars b

def cvars : Cmd → List String
  | .skip => []
  | .assign x e => x :: evars e
  | .seq a b => cvars a ++ cvars b
  | .ite e a b => evars e ++ cvars a ++ cvars b

def allVars (p : Prog) : List String := cvars p.body ++ evars p.ret

/-- The first position of `x`. -/
def idx : List String → String → Nat
  | [], _ => 0
  | y :: ys, x => if x = y then 0 else idx ys x + 1

theorem idx_lt : ∀ {L : List String} {x : String}, x ∈ L → idx L x < L.length
  | [], _, h => by cases h
  | y :: ys, x, h => by
    simp only [idx, List.length_cons]
    split
    · omega
    · rename_i hne
      have := idx_lt (L := ys) (by simpa [hne] using h)
      omega

theorem idx_inj : ∀ {L : List String} {x z : String}, x ∈ L → z ∈ L → idx L x = idx L z → x = z
  | [], _, _, h, _, _ => by cases h
  | y :: ys, x, z, hx, hz, he => by
    simp only [idx] at he
    by_cases h1 : x = y
    · by_cases h2 : z = y
      · rw [h1, h2]
      · simp [h1, h2] at he
    · by_cases h2 : z = y
      · simp [h1, h2] at he
      · simp only [h1, h2, ↓reduceIte, Nat.add_right_cancel_iff] at he
        exact idx_inj (by simpa [h1] using hx) (by simpa [h2] using hz) he

/-- **Input `k` at slot `k`, and locals from slot 64.** -/
def slotOf (p : Prog) (x : String) : Nat :=
  if x ∈ p.inputs then idx p.inputs x else 64 + idx (allVars p) x

theorem slotOf_inj {p : Prog} (hf : p.inputs.length ≤ 64) {x z : String} (hx : x ∈ allVars p)
    (hz : z ∈ allVars p) (he : slotOf p x = slotOf p z) : x = z := by
  simp only [slotOf] at he
  by_cases h1 : x ∈ p.inputs
  · by_cases h2 : z ∈ p.inputs
    · simp only [h1, h2, ↓reduceIte] at he
      exact idx_inj h1 h2 he
    · simp only [h1, h2, ↓reduceIte] at he
      have := idx_lt h1; omega
  · by_cases h2 : z ∈ p.inputs
    · simp only [h1, h2, ↓reduceIte] at he
      have := idx_lt h2; omega
    · simp only [h1, h2, ↓reduceIte] at he
      exact idx_inj hx hz (by omega)

def cE (p : Prog) : Expr → SExpr
  | .lit w => .lit w
  | .var x => .slot (slotOf p x)
  | .add a b => .add (cE p a) (cE p b)

def cC (p : Prog) : Cmd → SCmd
  | .skip => .skip
  | .assign x e => .set (slotOf p x) (cE p e)
  | .seq a b => .seq (cC p a) (cC p b)
  | .ite e a b => .ite (cE p e) (cC p a) (cC p b)

def compile (p : Prog) : SProg := { body := cC p p.body, ret := cE p p.ret }

/-- Does it fit: 64 input words, and 512 slots in the data segment? -/
def fits (p : Prog) : Bool := decide (p.inputs.length ≤ 64) && decide (64 + (allVars p).length ≤ 512)

def comp (p : Prog) : Except String (SProg × Xform) :=
  if fits p then .ok (compile p, Xform.id) else .error "the program does not fit its data segment"

theorem comp_ok {p : Prog} {p' : SProg} {t : Xform} (h : comp p = .ok (p', t)) :
    p.inputs.length ≤ 64 ∧ p' = compile p ∧ t = Xform.id := by
  simp only [comp] at h
  split at h
  · rename_i hf
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨hf.1, h.1.symm, h.2.symm⟩
  · cases h

/-! ## The simulation -/

/-- The slots hold what the store holds, for the program's variables. -/
def Rel (p : Prog) (s : Store) (t : Slots) : Prop := ∀ x ∈ allVars p, t (slotOf p x) = s x

theorem evalS_cE {p : Prog} {s : Store} {t : Slots} (h : Rel p s t) :
    ∀ e, (∀ x ∈ evars e, x ∈ allVars p) → evalS (cE p e) t = eval e s
  | .lit _, _ => rfl
  | .var x, hv => h x (hv x (by simp [evars]))
  | .add a b, hv => by
    simp only [cE, evalS, eval]
    rw [evalS_cE h a (fun x hx => hv x (by simp [evars, hx])),
      evalS_cE h b (fun x hx => hv x (by simp [evars, hx]))]

def cF (p : Prog) (f : Frame) : SFrame := (cC p f.1, f.2)

theorem pushS_cC (p : Prog) : ∀ (c : Cmd) (q : List Nat) (k : List Frame),
    pushS (cC p c) q (k.map (cF p)) = (push c q k).map (cF p)
  | .seq a b, q, k => by
    simp only [cC, pushS, push]
    rw [pushS_cC p b, pushS_cC p a]
  | .skip, _, _ | .assign _ _, _, _ | .ite _ _ _, _, _ => rfl

/-- Every frame's variables are the program's. -/
def Cov (p : Prog) (k : List Frame) : Prop := ∀ f ∈ k, ∀ x ∈ cvars f.1, x ∈ allVars p

theorem push_cov {p : Prog} : ∀ (c : Cmd) (q : List Nat) (k : List Frame),
    (∀ x ∈ cvars c, x ∈ allVars p) → Cov p k → Cov p (push c q k)
  | .seq a b, q, k, hc, hk => by
    apply push_cov a _ _ (fun x hx => hc x (by simp [cvars, hx]))
    exact push_cov b _ _ (fun x hx => hc x (by simp [cvars, hx])) hk
  | .skip, _, k, hc, hk | .assign _ _, _, k, hc, hk | .ite _ _ _, _, k, hc, hk => by
    intro f hf
    simp only [push, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hc
    · exact hk f hf

/-- **Step for step, the compiled frames show what the source's show.** -/
theorem runS_sim {p : Prog} (hf : p.inputs.length ≤ 64)
    (hret : ∀ x ∈ evars p.ret, x ∈ allVars p) : ∀ (n : Nat) (k : List Frame) (s : Store) (t : Slots),
    Cov p k → Rel p s t → runS (cE p p.ret) n (k.map (cF p)) t = run p.ret n k s := by
  intro n
  induction n with
  | zero =>
    intro k s t _ hr
    cases k with
    | nil => simp only [List.map, runS, run, evalS_cE hr _ hret]
    | cons f k => rfl
  | succ m ih =>
    intro k s t hc hr
    cases k with
    | nil => simp only [List.map, runS, run, evalS_cE hr _ hret]
    | cons f k =>
      obtain ⟨c, q⟩ := f
      have hc0 : ∀ x ∈ cvars c, x ∈ allVars p := hc _ List.mem_cons_self
      have hk : Cov p k := fun g hg => hc g (List.mem_cons_of_mem _ hg)
      cases c with
      | skip =>
        simp only [List.map, cF, cC, runS, run]
        rw [ih k s t hk hr]
      | assign x e =>
        simp only [List.map, cF, cC, runS, run]
        have hx : x ∈ allVars p := hc0 x (by simp [cvars])
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        have hr' : Rel p (upd s x (eval e s)) (updS t (slotOf p x) (evalS (cE p e) t)) := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx; simp [updS, upd, he]
          · have hne : slotOf p y ≠ slotOf p x := fun h => hyx (slotOf_inj hf hy hx h)
            simp [updS, upd, hne, hyx, hr y hy]
        rw [← ih k _ _ hk hr']
      | seq a b =>
        have hpush := ih (push a (q ++ [0]) (push b (q ++ [1]) k)) s t
          (push_cov a _ _ (fun x hx => hc0 x (by simp [cvars, hx]))
            (push_cov b _ _ (fun x hx => hc0 x (by simp [cvars, hx])) hk)) hr
        rw [← pushS_cC, ← pushS_cC] at hpush
        simpa only [List.map, cF, cC, runS, run] using hpush
      | ite e a b =>
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        simp only [List.map, cF, cC, runS, run, he]
        split
        · have := ih (push a (q ++ [0]) k) s t
            (push_cov a _ _ (fun x hx => hc0 x (by simp [cvars, hx])) hk) hr
          rw [← pushS_cC] at this
          rw [this]
        · have := ih (push b (q ++ [1]) k) s t
            (push_cov b _ _ (fun x hx => hc0 x (by simp [cvars, hx])) hk) hr
          rw [← pushS_cC] at this
          rw [this]

theorem initFrom_mem (v : Nat → W64) : ∀ (xs : List String) (k : Nat) (x : String), x ∈ xs →
    initFrom v xs k x = v (k + idx xs x)
  | [], _, _, h => by cases h
  | y :: ys, k, x, h => by
    simp only [initFrom, idx]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ↓reduceIte]
      rw [initFrom_mem v ys (k + 1) x (by simpa [hxy] using h)]
      congr 1; omega

theorem initFrom_not_mem (v : Nat → W64) : ∀ (xs : List String) (k : Nat) (x : String), x ∉ xs →
    initFrom v xs k x = W64.ofNat 0
  | [], _, _, _ => rfl
  | y :: ys, k, x, h => by
    have hxy : x ≠ y := fun e => h (by simp [e])
    simp only [initFrom, hxy, ↓reduceIte]
    exact initFrom_not_mem v ys (k + 1) x (fun hm => h (List.mem_cons_of_mem _ hm))

/-- **The initial slots hold the initial store**, on admissible inputs: locals start at zero only there. -/
theorem init_rel {p : Prog} {v : Nat → W64} (hv : ∀ k, cap ≤ k → v k = W64.ofNat 0) :
    Rel p (initFrom v p.inputs 0) (wordAt (encBytes v)) := by
  intro x _
  rw [wordAt_enc]
  simp only [slotOf]
  by_cases hx : x ∈ p.inputs
  · simp only [hx, ↓reduceIte]
    rw [initFrom_mem v _ 0 x hx, Nat.zero_add]
  · simp only [hx, ↓reduceIte]
    rw [initFrom_not_mem v _ 0 x hx]
    exact hv _ (by have : cap = 64 := rfl; omega)

/-- **The pass's one equation**: on admissible inputs, the compiled run is the source's, exactly. -/
theorem compile_sim {E : Type} {P : Nat → Bool} {p : Prog} (hf : p.inputs.length ≤ 64) (m : Nat)
    (i : (Nat → W64) × E) (hi : ∀ k, cap ≤ k → i.1 k = W64.ofNat 0) :
    (slotLang E P).run m (compile p) (encBytes i.1, i.2) = (sliceLang E P).run m p i := by
  have hr := init_rel (p := p) hi
  have hc : Cov p (push p.body [] []) :=
    push_cov _ _ _ (fun x hx => List.mem_append_left _ hx) (fun _ h => by cases h)
  have := runS_sim hf (fun x hx => List.mem_append_right _ hx) m _ _ _ hc hr
  rw [← pushS_cC] at this
  exact this

/-! ## The pass -/

/-- **The first pass whose input changes form.** -/
def slotPass (E : Type) (P : Nat → Bool) : PassCert (sliceLang E P) (slotLang E P) where
  comp := comp
  enc i := (encBytes i.1, i.2)
  enc_adm i hi off hoff := by
    have hb : Rv.inBytes = 512 := rfl
    have hk : cap ≤ off / 8 := by have : cap = 64 := rfl; omega
    show byteOf ((i.1 (off / 8)).val / 256 ^ (off % 8)) = byteOf 0
    rw [hi _ hk]
    simp [W64.ofNat]
  cover u hu := by
    refine ⟨(wordAt u.1, u.2), ?_, ?_⟩
    · intro k hk
      have hb : Rv.inBytes = 512 := rfl
      have hc : cap = 64 := rfl
      simp only [wordAt, hu (8 * k) (by omega), hu (8 * k + 1) (by omega), hu (8 * k + 2) (by omega),
        hu (8 * k + 3) (by omega), hu (8 * k + 4) (by omega), hu (8 * k + 5) (by omega),
        hu (8 * k + 6) (by omega), hu (8 * k + 7) (by omega)]
      rfl
    · show (encBytes (wordAt u.1), u.2) = u
      rw [enc_wordAt]; rfl
  low_cover u u' hu hu' hl := by
    have hb : Rv.inBytes = 512 := rfl
    have hc : cap = 64 := rfl
    have adm : ∀ w : (Nat → Byte) × E, (∀ off, Rv.inBytes ≤ off → w.1 off = byteOf 0) →
        ∀ k, cap ≤ k → wordAt w.1 k = W64.ofNat 0 := by
      intro w hw k hk
      simp only [wordAt, hw (8 * k) (by omega), hw (8 * k + 1) (by omega), hw (8 * k + 2) (by omega),
        hw (8 * k + 3) (by omega), hw (8 * k + 4) (by omega), hw (8 * k + 5) (by omega),
        hw (8 * k + 6) (by omega), hw (8 * k + 7) (by omega)]
      rfl
    refine ⟨(wordAt u.1, u.2), (wordAt u'.1, u'.2), adm u hu, adm u' hu', ?_, ?_, ?_⟩
    · intro k hk
      have hb8 : ∀ j, j < 8 → (8 * k + j) / 8 = k := by intro j hj; omega
      have e : ∀ j, j < 8 → u.1 (8 * k + j) = u'.1 (8 * k + j) :=
        fun j hj => hl _ (by rw [hb8 j hj]; exact hk)
      have e0 := e 0 (by omega)
      simp only [Nat.add_zero] at e0
      show wordAt u.1 k = wordAt u'.1 k
      simp only [wordAt, e0, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
        e 5 (by omega), e 6 (by omega), e 7 (by omega)]
    · show (encBytes (wordAt u.1), u.2) = u
      rw [enc_wordAt]; rfl
    · show (encBytes (wordAt u'.1), u'.2) = u'
      rw [enc_wordAt]; rfl
  ev_sim p p' t h m i hi := by
    obtain ⟨hf, rfl, rfl⟩ := comp_ok h
    rw [show Xform.id.fuel m = m from rfl]
    show ((slotLang E P).run m (compile p) (encBytes i.1, i.2)).ev <+: _
    rw [compile_sim hf m i hi]
    exact List.prefix_refl _
  cost_sim p p' t h m i hi := by
    obtain ⟨hf, rfl, rfl⟩ := comp_ok h
    show ((slotLang E P).run m (compile p) (encBytes i.1, i.2)).cost ≤ _
    rw [compile_sim hf m i hi]
    exact Nat.le_refl _
  det p p' t h f m i i' hi hi' he := by
    obtain ⟨hf, rfl, rfl⟩ := comp_ok h
    show ((slotLang E P).run m (compile p) (encBytes i.1, i.2)).view f =
      ((slotLang E P).run m (compile p) (encBytes i'.1, i'.2)).view f
    rw [compile_sim hf m i hi, compile_sim hf m i' hi']
    exact he
  progress p p' t h n i hi _ := by
    obtain ⟨hf, rfl, rfl⟩ := comp_ok h
    refine ⟨n, ?_, ?_⟩
    · show ((slotLang E P).run n (compile p) (encBytes i.1, i.2)).out = _
      rw [compile_sim hf n i hi]
    · show ((slotLang E P).run n (compile p) (encBytes i.1, i.2)).ev = _
      rw [compile_sim hf n i hi]
  catch_up p p' t h n i hi := by
    obtain ⟨hf, rfl, rfl⟩ := comp_ok h
    refine ⟨n, ?_⟩
    show _ <+: ((slotLang E P).run n (compile p) (encBytes i.1, i.2)).ev
    rw [compile_sim hf n i hi]
    exact List.prefix_refl _
  reflect p p' t h m i hi _ := by
    obtain ⟨hf, rfl, rfl⟩ := comp_ok h
    refine ⟨m, ?_, ?_⟩
    · show _ = ((slotLang E P).run m (compile p) (encBytes i.1, i.2)).out
      rw [compile_sim hf m i hi]
    · show _ = ((slotLang E P).run m (compile p) (encBytes i.1, i.2)).ev
      rw [compile_sim hf m i hi]

/-! ## Witnesses -/

theorem clean_comp : comp clean = .ok (compile clean, Xform.id) := by
  have h : fits clean = true := by decide
  simp [comp, h]

/-- **Carried by transfer alone**: the slot program has the source's `rel` and `bound`, over every byte pattern. -/
theorem clean_carried (E : Type) :
    Cert.rel (slotLang E sec0) (compile clean) ∧ Cert.bound (slotLang E sec0) 4 (compile clean) :=
  ⟨(slotPass E sec0).rel_transfer (p := clean) clean_comp (clean_rel E),
   (slotPass E sec0).bound_transfer (p := clean) clean_comp (clean_bound E)⟩

/-- A byte pattern no source word list was written to produce. -/
def bytesWith (a : Nat) : Nat → Byte := fun off => if off = 3 then byteOf a else byteOf 0

theorem bytesWith_adm (a : Nat) (off : Nat) (h : Rv.inBytes ≤ off) : bytesWith a off = byteOf 0 := by
  have hb : Rv.inBytes = 512 := rfl
  have : off ≠ 3 := by omega
  simp [bytesWith, this]

/-- **Coverage is real**: two inputs that differ in one byte, inside the secret word, are low-related, and the
    certificate speaks about them. -/
theorem carried_inside_a_word (n : Nat) :
    (slotLang Unit sec0).run n (compile clean) (bytesWith 1, ()) =
      (slotLang Unit sec0).run n (compile clean) (bytesWith 2, ()) := by
  refine (clean_carried Unit).1 n _ _ (bytesWith_adm 1) (bytesWith_adm 2) ?_
  intro off hoff
  have h0 : off / 8 ≠ 0 := by
    intro h; rw [h] at hoff; simp [sec0] at hoff
  have h3 : off ≠ 3 := by intro h; subst h; exact h0 rfl
  simp [bytesWith, h3]

/-- **The target's semantics decodes the bytes**: the word at position 0 really is what the program reads. -/
theorem target_reads_bytes :
    ((slotLang Unit sec0).run 5 { body := .skip, ret := .slot 0 } (bytesWith 2, ())).ev =
      [retEv (W64.ofNat 33554432)] := by
  decide

/-- **The compiled form of a refused program leaks too**, so `rel` on the target is not vacuous. -/
theorem secretRet_target_leaks : ¬ Cert.rel (slotLang Unit sec0) (compile secretRet) := by
  intro h
  have := h 5 (bytesWith 1, ()) (bytesWith 2, ()) (bytesWith_adm 1) (bytesWith_adm 2) (by
    intro off hoff
    have h0 : off / 8 ≠ 0 := by
      intro h; rw [h] at hoff; simp [sec0] at hoff
    have h3 : off ≠ 3 := by intro h; subst h; exact h0 rfl
    simp [bytesWith, h3])
  revert this; decide

/-- **`comp` refuses what does not fit.** -/
theorem comp_refuses_too_many_inputs :
    comp { inputs := (List.range 65).map toString, body := .skip, ret := .lit (W64.ofNat 0) } =
      .error "the program does not fit its data segment" := by
  have h : fits { inputs := (List.range 65).map toString, body := .skip, ret := .lit (W64.ofNat 0) } = false := by
    decide
  simp [comp, h]

end LCore.Slice.Slots
