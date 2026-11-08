/-
  VS-2 step 5: variables to slots, with loops and the array. Still lockstep: the compiled run is the source's, exactly, at every fuel.

  Input `k` lives at slot `k`. The array's 64 words live at slots 64 to 127, and locals from slot 128, so no store to the array can reach a variable. The input's
  encoding is VS-1's: the data segment's bytes, with `enc_wordAt` for coverage. The array and the locals start at zero because the input bytes are zero there, on admissible inputs.
-/
import LCore.Slice2.Source
import LCore.Slice.Slots

namespace LCore.Slice2.Slots

open Slice (W64 Expr Store upd eval retEv cap tick tick_ext Ext sec0)
open Slice.Rv (Byte byteOf)
open Slice.Slots (SExpr evalS updS encBytes wordAt wordAt_enc enc_wordAt evars)

abbrev Slots := Slice.Slots.Slots

/-! ## The target language -/

inductive SCmd where
  | skip  : SCmd
  | set   : Nat → SExpr → SCmd
  | seq   : SCmd → SCmd → SCmd
  | ite   : SExpr → SCmd → SCmd → SCmd
  | loop  : SExpr → SCmd → SCmd
  | load  : Nat → SExpr → SCmd
  /-- Byte `i` of the slots `ws` (RC-01). -/
  | loadB : Nat → List Nat → SExpr → SCmd
  | store : SExpr → SExpr → SCmd
  deriving DecidableEq, Repr

structure SProg where
  body : SCmd
  ret  : SExpr
  deriving DecidableEq, Repr

abbrev SFrame := SCmd × List Nat

def pushS : SCmd → List Nat → List SFrame → List SFrame
  | .seq a b, p, k => pushS a (p ++ [0]) (pushS b (p ++ [1]) k)
  | c, p, k => (c, p) :: k

/-- The array's first slot. -/
def arrBase : Nat := 64

/-- A byte array's index on the slots, masked to its bytes. -/
def bidxS (ws : List Nat) (v : W64) : Nat := v.val % (8 * ws.length)

/-- Byte `i` of the slots `ws`, and 0 past their end. -/
def byteAtS (t : Slots) (ws : List Nat) (i : Nat) : W64 :=
  match ws[i / 8]? with
  | some w => byteOfWord (t w) (i % 8)
  | none => W64.ofNat 0

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
    | .loop e b =>
      if (evalS e t).val ≠ 0 then tick [.branch true] p (runS ret n (pushS b (p ++ [0]) ((.loop e b, p) :: k)) t)
      else tick [.branch false] p (runS ret n k t)
    | .load x e => tick [addrLk (idx (evalS e t))] p (runS ret n k (updS t x (t (arrBase + idx (evalS e t)))))
    | .loadB x ws e => tick [addrLk (bidxS ws (evalS e t))] p (runS ret n k (updS t x (byteAtS t ws (bidxS ws (evalS e t)))))
    | .store e v => tick [addrLk (idx (evalS e t))] p (runS ret n k (updS t (arrBase + idx (evalS e t)) (evalS v t)))

/-- **The slot language.** Its input is the data segment's bytes. -/
def slotLang (E : Type) (P : Nat → Bool) : Lang where
  Prog  := SProg
  In    := (Nat → Byte) × E
  lowIn i i' := ∀ off, P (off / 8) = false → i.1 off = i'.1 off
  run n p i := runS p.ret n (pushS p.body [] []) (wordAt i.1)
  Adm i := ∀ off, Slice.Rv.inBytes ≤ off → i.1 off = byteOf 0

/-! ## Lawful -/

theorem runS_ext (ret : SExpr) : ∀ (n n' : Nat) (k : List SFrame) (t : Slots), n ≤ n' →
    Ext (runS ret n k t) (runS ret n' k t) := by
  intro n
  induction n with
  | zero =>
    intro n' k t _
    cases k with
    | nil => cases n' <;> exact Slice.Ext.refl _
    | cons f k => exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ m ih =>
    intro n' k t hle
    obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases k with
    | nil => exact Slice.Ext.refl _
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
      | loop e b =>
        simp only [runS]
        split
        · exact tick_ext _ _ (ih m' _ t hm)
        · exact tick_ext _ _ (ih m' _ t hm)
      | load x e => exact tick_ext _ _ (ih m' _ _ hm)
      | loadB x ws e => exact tick_ext _ _ (ih m' _ _ hm)
      | store e v => exact tick_ext _ _ (ih m' _ _ hm)

def NoSeqS (k : List SFrame) : Prop := ∀ f ∈ k, ∀ a b, f.1 ≠ .seq a b

theorem pushS_noSeq : ∀ (c : SCmd) (p : List Nat) (k : List SFrame), NoSeqS k → NoSeqS (pushS c p k)
  | .seq a b, p, k, h => pushS_noSeq a _ _ (pushS_noSeq b _ k h)
  | .skip, _, k, h | .set _ _, _, k, h | .ite _ _ _, _, k, h | .loop _ _, _, k, h
  | .load _ _, _, k, h | .loadB _ _ _, _, k, h | .store _ _, _, k, h => by
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
      | loop e b =>
        simp only [runS] at hf ⊢
        split at hf
        · rename_i hg; rw [if_pos hg]; simp only [tick] at hf ⊢
          have hk2 : NoSeqS ((SCmd.loop e b, p) :: k) := by
            intro x hx a' b'; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp
            · exact hk' x hx a' b'
          have := ih _ t (pushS_noSeq _ _ _ hk2) hf; omega
        · rename_i hg; rw [if_neg hg]; simp only [tick] at hf ⊢
          have := ih k t hk' hf; omega
      | load x e =>
        simp only [runS, tick] at hf ⊢
        have := ih k _ hk' hf; omega
      | loadB x ws e =>
        simp only [runS, tick] at hf ⊢
        have := ih k _ hk' hf; omega
      | store e v =>
        simp only [runS, tick] at hf ⊢
        have := ih k _ hk' hf; omega

theorem slotLang_lawful (E : Type) (P : Nat → Bool) : (slotLang E P).Lawful where
  ev_mono p i n n' h := (runS_ext _ n n' _ _ h).2.1
  lk_mono p i n n' h := (runS_ext _ n n' _ _ h).2.2.1
  cost_mono p i n n' h := (runS_ext _ n n' _ _ h).2.2.2
  stable p i n n' h hf := ((runS_ext _ n n' _ _ h).1 hf).symm
  diverge p := ⟨0, fun n i h =>
    runS_diverge _ n _ _ (pushS_noSeq _ _ _ (fun _ hx => by simp at hx)) h⟩

/-! ## The compiler -/

def cvars : Cmd → List String
  | .skip => []
  | .assign x e => x :: evars e
  | .seq a b => cvars a ++ cvars b
  | .ite e a b => evars e ++ cvars a ++ cvars b
  | .loop e b => evars e ++ cvars b
  | .load x e => x :: evars e
  | .loadB x ns e => x :: ns ++ evars e
  | .store e v => evars e ++ evars v

def allVars (p : Prog) : List String := cvars p.body ++ evars p.ret

/-- **Input `k` at slot `k`, and locals from slot 128.** The array is between them. -/
def slotOf (p : Prog) (x : String) : Nat :=
  if x ∈ p.inputs then Slice.Slots.idx p.inputs x else 128 + Slice.Slots.idx (allVars p) x

theorem slotOf_inj {p : Prog} (hf : p.inputs.length ≤ 64) {x z : String} (hx : x ∈ allVars p)
    (hz : z ∈ allVars p) (he : slotOf p x = slotOf p z) : x = z := by
  simp only [slotOf] at he
  by_cases h1 : x ∈ p.inputs
  · by_cases h2 : z ∈ p.inputs
    · simp only [h1, h2, ↓reduceIte] at he
      exact Slice.Slots.idx_inj h1 h2 he
    · simp only [h1, h2, ↓reduceIte] at he
      have := Slice.Slots.idx_lt h1; omega
  · by_cases h2 : z ∈ p.inputs
    · simp only [h1, h2, ↓reduceIte] at he
      have := Slice.Slots.idx_lt h2; omega
    · simp only [h1, h2, ↓reduceIte] at he
      exact Slice.Slots.idx_inj hx hz (by omega)

/-- **A variable's slot is outside the array.** -/
theorem slotOf_not_arr {p : Prog} (hf : p.inputs.length ≤ 64) (x : String) (i : Nat) (hi : i < 64) :
    slotOf p x ≠ arrBase + i := by
  have hb : arrBase = 64 := rfl
  simp only [slotOf]
  by_cases h1 : x ∈ p.inputs
  · simp only [h1, ↓reduceIte]
    have := Slice.Slots.idx_lt h1; omega
  · simp only [h1, ↓reduceIte]
    omega

theorem idx_lt (v : W64) : idx v < 64 := Nat.mod_lt _ (by omega)

def cE (p : Prog) : Expr → SExpr
  | .lit w => .lit w
  | .var x => .slot (slotOf p x)
  | .add a b => .add (cE p a) (cE p b)
  | .bin o a b => .bin o (cE p a) (cE p b)
  | .shr a k => .shr (cE p a) k

def cC (p : Prog) : Cmd → SCmd
  | .skip => .skip
  | .assign x e => .set (slotOf p x) (cE p e)
  | .seq a b => .seq (cC p a) (cC p b)
  | .ite e a b => .ite (cE p e) (cC p a) (cC p b)
  | .loop e b => .loop (cE p e) (cC p b)
  | .load x e => .load (slotOf p x) (cE p e)
  | .loadB x ns e => .loadB (slotOf p x) (ns.map (slotOf p)) (cE p e)
  | .store e v => .store (cE p e) (cE p v)

def compile (p : Prog) : SProg := { body := cC p p.body, ret := cE p p.ret }

/-- Does it fit: 64 input words, 64 array words, and the locals, within the data segment's 512 slots? -/
def fits (p : Prog) : Bool := decide (p.inputs.length ≤ 64) && decide (128 + (allVars p).length ≤ 512)

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

/-- The slots hold the store and the array. -/
def Rel (p : Prog) (s : Store) (a : Arr) (t : Slots) : Prop :=
  (∀ x ∈ allVars p, t (slotOf p x) = s x) ∧ ∀ i, i < 64 → t (arrBase + i) = a i

theorem evalS_cE {p : Prog} {s : Store} {a : Arr} {t : Slots} (h : Rel p s a t) :
    ∀ e, (∀ x ∈ evars e, x ∈ allVars p) → evalS (cE p e) t = eval e s
  | .lit _, _ => rfl
  | .var x, hv => h.1 x (hv x (by simp [evars]))
  | .add x y, hv | .bin _ x y, hv => by
    simp only [cE, evalS, eval]
    rw [evalS_cE h x (fun v hx => hv v (by simp [evars, hx])),
      evalS_cE h y (fun v hx => hv v (by simp [evars, hx]))]
  | .shr x _, hv => by
    simp only [cE, evalS, eval]
    rw [evalS_cE h x (fun v hx => hv v (by simp [evars, hx]))]

def cF (p : Prog) (f : Frame) : SFrame := (cC p f.1, f.2)

theorem pushS_cC (p : Prog) : ∀ (c : Cmd) (q : List Nat) (k : List Frame),
    pushS (cC p c) q (k.map (cF p)) = (push c q k).map (cF p)
  | .seq a b, q, k => by
    simp only [cC, pushS, push]
    rw [pushS_cC p b, pushS_cC p a]
  | .skip, _, _ | .assign _ _, _, _ | .ite _ _ _, _, _ | .loop _ _, _, _ | .load _ _, _, _ | .loadB _ _ _, _, _
  | .store _ _, _, _ => rfl

def Cov (p : Prog) (k : List Frame) : Prop := ∀ f ∈ k, ∀ x ∈ cvars f.1, x ∈ allVars p

theorem push_cov {p : Prog} : ∀ (c : Cmd) (q : List Nat) (k : List Frame),
    (∀ x ∈ cvars c, x ∈ allVars p) → Cov p k → Cov p (push c q k)
  | .seq a b, q, k, hc, hk => by
    apply push_cov a _ _ (fun x hx => hc x (by simp [cvars, hx]))
    exact push_cov b _ _ (fun x hx => hc x (by simp [cvars, hx])) hk
  | .skip, _, k, hc, hk | .assign _ _, _, k, hc, hk | .ite _ _ _, _, k, hc, hk | .loop _ _, _, k, hc, hk
  | .load _ _, _, k, hc, hk | .loadB _ _ _, _, k, hc, hk | .store _ _, _, k, hc, hk => by
    intro f hf
    simp only [push, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hc
    · exact hk f hf

/-- **The slots' byte is the store's**, for an array of the program's own variables. -/
theorem byteAtS_map {p : Prog} {s : Store} {a : Arr} {t : Slots} (h : Rel p s a t) {ns : List String}
    (hns : ∀ y ∈ ns, y ∈ allVars p) (i : Nat) : byteAtS t (ns.map (slotOf p)) i = byteAt s ns i := by
  simp only [byteAtS, byteAt, List.getElem?_map]
  cases hy : ns[i / 8]? with
  | none => rfl
  | some y => simp only [Option.map_some]; rw [h.1 y (hns y (List.mem_of_getElem? hy))]

/-- Setting a variable's slot keeps the relation. -/
theorem rel_set {p : Prog} (hf : p.inputs.length ≤ 64) {s : Store} {a : Arr} {t : Slots} (h : Rel p s a t) {x : String}
    (hx : x ∈ allVars p) (v : W64) : Rel p (upd s x v) a (updS t (slotOf p x) v) := by
  refine ⟨fun y hy => ?_, fun i hi => ?_⟩
  · by_cases hyx : y = x
    · subst hyx; simp [updS, upd]
    · have hne : slotOf p y ≠ slotOf p x := fun e => hyx (slotOf_inj hf hy hx e)
      simp [updS, upd, hne, hyx, h.1 y hy]
  · have hne : arrBase + i ≠ slotOf p x := (slotOf_not_arr hf x i hi).symm
    simp [updS, hne, h.2 i hi]

/-- Storing to the array keeps the relation. -/
theorem rel_store {p : Prog} (hf : p.inputs.length ≤ 64) {s : Store} {a : Arr} {t : Slots} (h : Rel p s a t) {i : Nat}
    (hi : i < 64) (v : W64) : Rel p s (updA a i v) (updS t (arrBase + i) v) := by
  have hb : arrBase = 64 := rfl
  refine ⟨fun y hy => ?_, fun j hj => ?_⟩
  · have hne := slotOf_not_arr hf y i hi
    simp [updS, hne, h.1 y hy]
  · by_cases hji : j = i
    · subst hji; simp [updS, updA]
    · have hne : arrBase + j ≠ arrBase + i := by omega
      simp [updS, updA, hne, hji, h.2 j hj]

/-- **Step for step, the compiled frames show what the source's show**, at every fuel. -/
theorem runS_sim {p : Prog} (hf : p.inputs.length ≤ 64) (hret : ∀ x ∈ evars p.ret, x ∈ allVars p) :
    ∀ (n : Nat) (k : List Frame) (s : Store) (a : Arr) (t : Slots),
    Cov p k → Rel p s a t → runS (cE p p.ret) n (k.map (cF p)) t = run p.ret n k s a := by
  intro n
  induction n with
  | zero =>
    intro k s a t _ hr
    cases k with
    | nil => simp only [List.map, runS, run, evalS_cE hr _ hret]
    | cons f k => rfl
  | succ m ih =>
    intro k s a t hc hr
    cases k with
    | nil => simp only [List.map, runS, run, evalS_cE hr _ hret]
    | cons f k =>
      obtain ⟨c, q⟩ := f
      have hc0 : ∀ x ∈ cvars c, x ∈ allVars p := hc _ List.mem_cons_self
      have hk : Cov p k := fun g hg => hc g (List.mem_cons_of_mem _ hg)
      cases c with
      | skip =>
        simp only [List.map, cF, cC, runS, run]
        rw [ih k s a t hk hr]
      | assign x e =>
        simp only [List.map, cF, cC, runS, run]
        have hx : x ∈ allVars p := hc0 x (by simp [cvars])
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        rw [he, ih k _ _ _ hk (rel_set hf hr hx _)]
      | seq c₁ c₂ =>
        have hpush := ih (push c₁ (q ++ [0]) (push c₂ (q ++ [1]) k)) s a t
          (push_cov c₁ _ _ (fun x hx => hc0 x (by simp [cvars, hx]))
            (push_cov c₂ _ _ (fun x hx => hc0 x (by simp [cvars, hx])) hk)) hr
        rw [← pushS_cC, ← pushS_cC] at hpush
        simpa only [List.map, cF, cC, runS, run] using hpush
      | ite e c₁ c₂ =>
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        simp only [List.map, cF, cC, runS, run, he]
        split
        · have := ih (push c₁ (q ++ [0]) k) s a t
            (push_cov c₁ _ _ (fun x hx => hc0 x (by simp [cvars, hx])) hk) hr
          rw [← pushS_cC] at this
          rw [this]
        · have := ih (push c₂ (q ++ [1]) k) s a t
            (push_cov c₂ _ _ (fun x hx => hc0 x (by simp [cvars, hx])) hk) hr
          rw [← pushS_cC] at this
          rw [this]
      | loop e b =>
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        simp only [List.map, cF, cC, runS, run, he]
        split
        · have := ih (push b (q ++ [0]) ((.loop e b, q) :: k)) s a t
            (push_cov b _ _ (fun x hx => hc0 x (by simp [cvars, hx])) hc) hr
          rw [← pushS_cC] at this
          simp only [List.map, cF, cC] at this
          rw [this]
        · rw [ih k s a t hk hr]
      | load x e =>
        simp only [List.map, cF, cC, runS, run]
        have hx : x ∈ allVars p := hc0 x (by simp [cvars])
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        rw [he, hr.2 _ (idx_lt _), ih k _ _ _ hk (rel_set hf hr hx _)]
      | loadB x ns e =>
        simp only [List.map, cF, cC, runS, run]
        have hx : x ∈ allVars p := hc0 x (by simp [cvars])
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        have hb := byteAtS_map (ns := ns) hr (fun y (hy : y ∈ ns) => hc0 y (by simp [cvars, hy])) (bidx ns (eval e s))
        have hi : bidxS (ns.map (slotOf p)) (eval e s) = bidx ns (eval e s) := by simp [bidxS, bidx]
        rw [he, hi, hb, ih k _ _ _ hk (rel_set hf hr hx _)]
      | store e v =>
        simp only [List.map, cF, cC, runS, run]
        have he := evalS_cE hr e (fun y hy => hc0 y (by simp [cvars, hy]))
        have hv := evalS_cE hr v (fun y hy => hc0 y (by simp [cvars, hy]))
        rw [he, hv, ih k _ _ _ hk (rel_store hf hr (idx_lt _) _)]

/-- **The initial slots hold the initial store and an empty array**, on admissible inputs. -/
theorem init_rel {p : Prog} {v : Nat → W64} (hv : ∀ k, cap ≤ k → v k = W64.ofNat 0) :
    Rel p (Slice.initFrom v p.inputs 0) zeroA (wordAt (encBytes v)) := by
  have hc : cap = 64 := rfl
  have hb : arrBase = 64 := rfl
  refine ⟨fun x _ => ?_, fun i _ => ?_⟩
  · rw [wordAt_enc]
    simp only [slotOf]
    by_cases hx : x ∈ p.inputs
    · simp only [hx, ↓reduceIte]
      rw [Slice.Slots.initFrom_mem v _ 0 x hx, Nat.zero_add]
    · simp only [hx, ↓reduceIte]
      rw [Slice.Slots.initFrom_not_mem v _ 0 x hx]
      exact hv _ (by omega)
  · rw [wordAt_enc]
    exact hv _ (by omega)

/-- **The pass's one equation**: on admissible inputs, the compiled run is the source's, exactly, at every fuel. -/
theorem compile_sim {E : Type} {P : Nat → Bool} {p : Prog} (hf : p.inputs.length ≤ 64) (m : Nat)
    (i : (Nat → W64) × E) (hi : ∀ k, cap ≤ k → i.1 k = W64.ofNat 0) :
    (slotLang E P).run m (compile p) (encBytes i.1, i.2) = (sliceLang E P).run m p i := by
  have hr := init_rel (p := p) hi
  have hc : Cov p (push p.body [] []) :=
    push_cov _ _ _ (fun x hx => List.mem_append_left _ hx) (fun _ h => by cases h)
  have := runS_sim hf (fun x hx => List.mem_append_right _ hx) m _ _ _ _ hc hr
  rw [← pushS_cC] at this
  exact this

/-! ## The pass -/

/-- A pass over loops whose input changes form. Fuel is the identity here, and not VS-1's constant. -/
def slotPass (E : Type) (P : Nat → Bool) : PassCert (sliceLang E P) (slotLang E P) where
  comp := comp
  enc i := (encBytes i.1, i.2)
  enc_adm i hi off hoff := by
    have hb : Slice.Rv.inBytes = 512 := rfl
    have hk : cap ≤ off / 8 := by have : cap = 64 := rfl; omega
    show byteOf ((i.1 (off / 8)).val / 256 ^ (off % 8)) = byteOf 0
    rw [hi _ hk]
    simp [W64.ofNat]
  cover u hu := by
    refine ⟨(wordAt u.1, u.2), ?_, ?_⟩
    · intro k hk
      have hb : Slice.Rv.inBytes = 512 := rfl
      have hc : cap = 64 := rfl
      simp only [wordAt, hu (8 * k) (by omega), hu (8 * k + 1) (by omega), hu (8 * k + 2) (by omega),
        hu (8 * k + 3) (by omega), hu (8 * k + 4) (by omega), hu (8 * k + 5) (by omega),
        hu (8 * k + 6) (by omega), hu (8 * k + 7) (by omega)]
      rfl
    · show (encBytes (wordAt u.1), u.2) = u
      rw [enc_wordAt]; rfl
  low_cover u u' hu hu' hl := by
    have hb : Slice.Rv.inBytes = 512 := rfl
    have hc : cap = 64 := rfl
    have adm : ∀ w : (Nat → Byte) × E, (∀ off, Slice.Rv.inBytes ≤ off → w.1 off = byteOf 0) →
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

theorem scan_comp : comp scan = .ok (compile scan, Xform.id) := by
  have h : fits scan = true := by decide
  simp [comp, h]

/-- **Carried by transfer alone**, over every byte pattern, for a program with a loop. -/
theorem scan_carried (E : Type) : Cert.rel (slotLang E sec0) (compile scan) :=
  (slotPass E sec0).rel_transfer (p := scan) scan_comp (scan_rel E)

theorem spin_comp : comp spin = .ok (compile spin, Xform.id) := by
  have h : fits spin = true := by decide
  simp [comp, h]

/-- **Carried for a run that never finishes.** -/
theorem spin_carried (E : Type) : Cert.rel (slotLang E sec0) (compile spin) :=
  (slotPass E sec0).rel_transfer (p := spin) spin_comp (spin_covered E)

/-- A store to the array reaches no variable: the array's slot is not an input's. -/
theorem array_does_not_alias : slotOf scan "n" ≠ arrBase + 1 := slotOf_not_arr (by decide) "n" 1 (by decide)

end LCore.Slice2.Slots
