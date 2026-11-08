/-
  VS-2 step 4: the second slice's source language. VS-1's, plus a `while` that may never finish, and one array read and written at an
  index that may depend on public input.

  **The array has its own memory**, 64 words, zero at the start, so it cannot alias the input variables. An index is masked to it, so it
  cannot go out of bounds: this language has no abort, on purpose. Each access leaks its masked index, because the machine's address is a function of it.

  **Attacker:** as in VS-1, and it also sees each array index. So an index must be public, and so must a loop guard, or how long the loop runs shows.

  **The checker** tracks which variables may hold a secret, and one bit for the whole array, which only rises: coarse, and it refuses programs that are safe. A loop's body must not raise
  anything beyond the loop head's state (`sub`). `secondIter` is why: it branches on a secret only on its second iteration.

  **Limits.** `bound` covers loop-free programs only: a `while` has no budget. No heap, strings, functions or mediation. Nothing here reaches a machine until the later steps carry it.
-/
import LCore.Slice.Source

namespace LCore.Slice2

open Slice (W64 Expr Store upd eval retEv initFrom cap highE highInit Low eval_low initFrom_low tick tick_ext Ext sec0 inp inp_adm inp_low)

/-! ## The language -/

inductive Cmd where
  | skip   : Cmd
  | assign : String → Expr → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : Expr → Cmd → Cmd → Cmd
  | loop   : Expr → Cmd → Cmd
  | load   : String → Expr → Cmd
  /-- `x := names[i]`, byte `i` of the input words `names`, read-only (RC-01): `crypto_verify_16`'s `x[i]`. -/
  | loadB  : String → List String → Expr → Cmd
  | store  : Expr → Expr → Cmd
  /-- `names[i] = v`, the low byte of `v` into byte `i` of the words `names` (RC-02): `sodium_add`'s `a[i] = (unsigned char) c`. -/
  | storeB : List String → Expr → Expr → Cmd
  /-- One step that emits the bytes of the words `names` as `.emit "out"` (RC-02): a writable array, observed at the end. -/
  | emitB  : List String → Cmd
  deriving DecidableEq, Repr

structure Prog where
  inputs : List String
  body   : Cmd
  ret    : Expr
  deriving DecidableEq, Repr

abbrev Arr := Nat → W64

def updA (a : Arr) (i : Nat) (v : W64) : Arr := fun j => if j = i then v else a j

/-- The array's size, and an index masked to it. -/
def idx (v : W64) : Nat := v.val % 64

abbrev Frame := Cmd × List Nat

def push : Cmd → List Nat → List Frame → List Frame
  | .seq a b, p, k => push a (p ++ [0]) (push b (p ++ [1]) k)
  | c, p, k => (c, p) :: k

/-- A byte array's index, masked to its `8 * length` bytes. -/
def bidx (ns : List String) (v : W64) : Nat := v.val % (8 * ns.length)

/-- Byte `i` of a word, little-endian, as RISC-V and x86 store them. -/
def byteOfWord (w : W64) (j : Nat) : W64 := W64.ofNat (w.val / 256 ^ j % 256)

/-- Byte `i` of the words `ns`, and 0 past their end. -/
def byteAt (s : Store) (ns : List String) (i : Nat) : W64 :=
  match ns[i / 8]? with
  | some y => byteOfWord (s y) (i % 8)
  | none => W64.ofNat 0

/-- Byte `j` of `w` set to `b`'s low byte, little-endian. Written as the machine's `load8` reads a word, byte by byte, so that a
    byte store on the machine is this on the slot's word. -/
def setByte (w : W64) (j : Nat) (b : W64) : W64 :=
  W64.ofNat ((List.range 8).foldr (fun i acc => (if i = j then b.val % 256 else w.val / 256 ^ i % 256) + 256 * acc) 0)

/-- Byte `i` of the words `ns` set to `v`'s low byte, and nothing past their end. -/
def storeAt (s : Store) (ns : List String) (i : Nat) (v : W64) : Store :=
  match ns[i / 8]? with
  | some y => upd s y (setByte (s y) (i % 8) v)
  | none => s

/-- The bytes of the words `ns`, little-endian. -/
def outBytes (s : Store) (ns : List String) : List Nat :=
  ns.flatMap fun y => (List.range 8).map fun j => (s y).val / 256 ^ j % 256

/-- A step that emits `v`, and leaks nothing else. -/
def etick (v : Ev) (p : List Nat) (r : Beh) : Beh := { tick [] p r with ev := v :: r.ev }

/-- An access's leakage: its masked index. -/
def addrLk (i : Nat) : Lk := .addr (Int.ofNat i)

/-- **The run**: `n` steps. A `while` that keeps going uses up the fuel. -/
def run (ret : Expr) : Nat → List Frame → Store → Arr → Beh
  | _, [], s, _ => { ev := [retEv (eval ret s)], lk := [], cost := 0, out := .done }
  | 0, _ :: _, _, _ => { ev := [], lk := [], cost := 0, out := .fuel }
  | n + 1, (c, p) :: k, s, a =>
    match c with
    | .skip => tick [] p (run ret n k s a)
    | .assign x e => tick [] p (run ret n k (upd s x (eval e s)) a)
    | .seq c₁ c₂ => run ret n (push c₁ (p ++ [0]) (push c₂ (p ++ [1]) k)) s a
    | .ite e c₁ c₂ =>
      if (eval e s).val ≠ 0 then tick [.branch true] p (run ret n (push c₁ (p ++ [0]) k) s a)
      else tick [.branch false] p (run ret n (push c₂ (p ++ [1]) k) s a)
    | .loop e b =>
      if (eval e s).val ≠ 0 then tick [.branch true] p (run ret n (push b (p ++ [0]) ((.loop e b, p) :: k)) s a)
      else tick [.branch false] p (run ret n k s a)
    | .load x e => tick [addrLk (idx (eval e s))] p (run ret n k (upd s x (a (idx (eval e s)))) a)
    | .loadB x ns e => tick [addrLk (bidx ns (eval e s))] p (run ret n k (upd s x (byteAt s ns (bidx ns (eval e s)))) a)
    | .store e v => tick [addrLk (idx (eval e s))] p (run ret n k s (updA a (idx (eval e s)) (eval v s)))
    | .storeB ns e v => tick [addrLk (bidx ns (eval e s))] p (run ret n k (storeAt s ns (bidx ns (eval e s)) (eval v s)) a)
    | .emitB ns => etick (.emit "out" (outBytes s ns)) p (run ret n k s a)

def zeroA : Arr := fun _ => W64.ofNat 0

/-- **The source language.** -/
def sliceLang (E : Type) (P : Nat → Bool) : Lang where
  Prog  := Prog
  In    := (Nat → W64) × E
  lowIn i i' := ∀ k, P k = false → i.1 k = i'.1 k
  run n p i := run p.ret n (push p.body [] []) (initFrom i.1 p.inputs 0) zeroA
  Adm i := ∀ k, cap ≤ k → i.1 k = W64.ofNat 0

/-! ## Lawful, and a loop really can run forever -/

theorem etick_ext {a b : Beh} (v : Ev) (p : List Nat) (h : Slice.Ext a b) :
    Slice.Ext (etick v p a) (etick v p b) := by
  refine ⟨fun hf => ?_, ?_, ?_, Nat.add_le_add_left h.2.2.2 _⟩
  · rw [h.1 hf]
  · obtain ⟨t, ht⟩ := h.2.1
    exact ⟨t, by simp [etick, ← ht]⟩
  · obtain ⟨t, ht⟩ := h.2.2.1
    exact ⟨t, by simp [etick, tick, ← ht]⟩

theorem run_ext (ret : Expr) : ∀ (n n' : Nat) (k : List Frame) (s : Store) (a : Arr), n ≤ n' →
    Ext (run ret n k s a) (run ret n' k s a) := by
  intro n
  induction n with
  | zero =>
    intro n' k s a _
    cases k with
    | nil => cases n' <;> exact Slice.Ext.refl _
    | cons f k => exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ m ih =>
    intro n' k s a hle
    obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases k with
    | nil => exact Slice.Ext.refl _
    | cons f k =>
      obtain ⟨c, p⟩ := f
      cases c with
      | skip => exact tick_ext _ _ (ih m' _ s a hm)
      | assign x e => exact tick_ext _ _ (ih m' _ _ a hm)
      | seq c₁ c₂ => exact ih m' _ s a hm
      | ite e c₁ c₂ =>
        simp only [run]
        split
        · exact tick_ext _ _ (ih m' _ s a hm)
        · exact tick_ext _ _ (ih m' _ s a hm)
      | loop e b =>
        simp only [run]
        split
        · exact tick_ext _ _ (ih m' _ s a hm)
        · exact tick_ext _ _ (ih m' _ s a hm)
      | load x e => exact tick_ext _ _ (ih m' _ _ a hm)
      | loadB x ns e => exact tick_ext _ _ (ih m' _ _ a hm)
      | store e v => exact tick_ext _ _ (ih m' _ s _ hm)
      | storeB ns e v => exact tick_ext _ _ (ih m' _ _ a hm)
      | emitB ns => exact etick_ext _ _ (ih m' _ s a hm)

def NoSeq (k : List Frame) : Prop := ∀ f ∈ k, ∀ a b, f.1 ≠ .seq a b

theorem push_noSeq : ∀ (c : Cmd) (p : List Nat) (k : List Frame), NoSeq k → NoSeq (push c p k)
  | .seq a b, p, k, h => push_noSeq a _ _ (push_noSeq b _ k h)
  | .skip, _, k, h | .assign _ _, _, k, h | .ite _ _ _, _, k, h | .loop _ _, _, k, h
  | .load _ _, _, k, h | .loadB _ _ _, _, k, h | .store _ _, _, k, h | .storeB _ _ _, _, k, h | .emitB _, _, k, h => by
    intro f hf a b
    simp only [push, List.mem_cons] at hf
    rcases hf with rfl | hf
    · simp
    · exact h f hf a b

/-- **Fuel spent is cost paid**, so a run that never finishes has unbounded cost. -/
theorem run_diverge (ret : Expr) : ∀ (n : Nat) (k : List Frame) (s : Store) (a : Arr), NoSeq k →
    (run ret n k s a).out = .fuel → n ≤ (run ret n k s a).cost := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; exact Nat.zero_le _
  | succ m ih =>
    intro k s a hk hf
    cases k with
    | nil => simp [run] at hf
    | cons f k =>
      obtain ⟨c, p⟩ := f
      have hk' : NoSeq k := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      cases c with
      | skip =>
        simp only [run, tick] at hf ⊢
        have := ih k s a hk' hf; omega
      | assign x e =>
        simp only [run, tick] at hf ⊢
        have := ih k _ a hk' hf; omega
      | seq c₁ c₂ => exact absurd rfl (hk _ List.mem_cons_self c₁ c₂)
      | ite e c₁ c₂ =>
        simp only [run] at hf ⊢
        split at hf
        · rename_i hg; rw [if_pos hg]; simp only [tick] at hf ⊢
          have := ih _ s a (push_noSeq _ _ _ hk') hf; omega
        · rename_i hg; rw [if_neg hg]; simp only [tick] at hf ⊢
          have := ih _ s a (push_noSeq _ _ _ hk') hf; omega
      | loop e b =>
        simp only [run] at hf ⊢
        split at hf
        · rename_i hg; rw [if_pos hg]; simp only [tick] at hf ⊢
          have hk2 : NoSeq ((Cmd.loop e b, p) :: k) := by
            intro x hx a' b'; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp
            · exact hk' x hx a' b'
          have := ih _ s a (push_noSeq _ _ _ hk2) hf; omega
        · rename_i hg; rw [if_neg hg]; simp only [tick] at hf ⊢
          have := ih k s a hk' hf; omega
      | load x e =>
        simp only [run, tick] at hf ⊢
        have := ih k _ a hk' hf; omega
      | loadB x ns e =>
        simp only [run, tick] at hf ⊢
        have := ih k _ a hk' hf; omega
      | store e v =>
        simp only [run, tick] at hf ⊢
        have := ih k s _ hk' hf; omega
      | storeB ns e v =>
        simp only [run, tick] at hf ⊢
        have := ih k _ a hk' hf; omega
      | emitB ns =>
        simp only [run, etick, tick] at hf ⊢
        have := ih k s a hk' hf; omega

theorem sliceLang_lawful (E : Type) (P : Nat → Bool) : (sliceLang E P).Lawful where
  ev_mono p i n n' h := (run_ext _ n n' _ _ _ h).2.1
  lk_mono p i n n' h := (run_ext _ n n' _ _ _ h).2.2.1
  cost_mono p i n n' h := (run_ext _ n n' _ _ _ h).2.2.2
  stable p i n n' h hf := ((run_ext _ n n' _ _ _ h).1 hf).symm
  diverge p := ⟨0, fun n i h =>
    run_diverge _ n _ _ _ (push_noSeq _ _ _ (fun _ hx => by simp at hx)) h⟩

/-! ## The checker -/

/-- What may hold a secret: some variables, and the array as a whole. -/
abbrev St := List String × Bool

/-- `a` claims no more than `b`. -/
def sub (a b : St) : Bool := a.1.all (fun x => decide (x ∈ b.1)) && (!a.2 || b.2)

def highC (st : St) : Cmd → Option St
  | .skip => some st
  | .assign x e => if highE st.1 e then some (x :: st.1, st.2) else some (st.1.filter (· ≠ x), st.2)
  | .seq a b => (highC st a).bind fun s₁ => highC s₁ b
  | .ite e a b =>
    if highE st.1 e then none
    else (highC st a).bind fun sa => (highC st b).map fun sb => (sa.1 ++ sb.1, sa.2 || sb.2)
  | .loop e b =>
    if highE st.1 e then none
    else (highC st b).bind fun s₁ =>
      if sub s₁ st then some st
      else
        -- one widening step: from the head joined with what the body raised
        if highE (s₁.1 ++ st.1) e then none
        else (highC (s₁.1 ++ st.1, st.2 || s₁.2) b).bind fun s₂ =>
          if sub s₂ (s₁.1 ++ st.1, st.2 || s₁.2) then some (s₁.1 ++ st.1, st.2 || s₁.2) else none
  | .load x e =>
    if highE st.1 e then none
    else if st.2 then some (x :: st.1, st.2) else some (st.1.filter (· ≠ x), st.2)
  | .loadB x ns e =>
    if highE st.1 e || ns.isEmpty then none
    else if ns.any (fun y => decide (y ∈ st.1)) then some (x :: st.1, st.2) else some (st.1.filter (· ≠ x), st.2)
  | .store e v =>
    if highE st.1 e then none else some (st.1, st.2 || highE st.1 v)
  | .storeB ns e v =>
    if highE st.1 e || ns.isEmpty then none
    else if highE st.1 v then some (ns ++ st.1, st.2) else some st
  | .emitB ns => if ns.any (fun y => decide (y ∈ st.1)) then none else some st

/-- **The checker**: no secret guard, loop guard, index or result. A loop whose body raises something past its head is retried once from the
    head joined with the body's result, and refused if the body still raises something past that. -/
def sliceCheck (P : Nat → Bool) (p : Prog) : Bool :=
  match highC (highInit P p.inputs 0, false) p.body with
  | some st => !highE st.1 p.ret
  | none => false

/-! ## `rel` -/

/-- Two states the checker's state cannot tell apart. -/
def LowS (st : St) (s s' : Store) (a a' : Arr) : Prop := Low st.1 s s' ∧ (st.2 = false → a = a')

/-- `a` claims no more than `b`, as a proposition. -/
def Sub (x y : St) : Prop := (∀ v, v ∈ x.1 → v ∈ y.1) ∧ (x.2 = true → y.2 = true)

theorem Sub.refl (x : St) : Sub x x := ⟨fun _ h => h, fun h => h⟩

theorem sub_sound {x y : St} (h : sub x y = true) : Sub x y := by
  simp only [sub, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun hx => ?_⟩
  rcases h2 with h2 | h2
  · rw [hx] at h2; cases h2
  · exact h2

theorem LowS.mono {x y : St} {s s' : Store} {a a' : Arr} (hs : Sub x y) (h : LowS x s s' a a') : LowS y s s' a a' :=
  ⟨Slice.Low.mono hs.1 h.1, fun hy => h.2 (by
    cases hx : x.2 with
    | false => rfl
    | true => have := hs.2 hx; rw [hy] at this; cases this)⟩

/-- **A byte of a low array is the same in two runs**: the mask keeps the index inside the array, so the word it reads is one of its own. -/
theorem byteAt_low {H : List String} {s s' : Store} {ns : List String} (h : Low H s s') (hns : ∀ y ∈ ns, y ∉ H)
    (i : Nat) : byteAt s ns i = byteAt s' ns i := by
  simp only [byteAt]
  split
  · rename_i y hy
    rw [h y (hns y (List.mem_of_getElem? hy))]
  · rfl

/-- **A byte store leaves every word outside the array alone.** -/
theorem storeAt_other {s : Store} {ns : List String} {i : Nat} {v : W64} {y : String} (hy : y ∉ ns) :
    storeAt s ns i v y = s y := by
  cases hz : ns[i / 8]? with
  | none => simp only [storeAt, hz]
  | some z =>
    have hz' : z ∈ ns := List.mem_of_getElem? hz
    have hne : y ≠ z := fun h => hy (h ▸ hz')
    simp [storeAt, hz, upd, hne]

/-- **A low byte stored at a public index keeps two low-equal stores low-equal.** -/
theorem storeAt_low {H : List String} {s s' : Store} (h : Low H s s') (ns : List String) (i : Nat) {v v' : W64} (hv : v = v') :
    Low H (storeAt s ns i v) (storeAt s' ns i v') := by
  intro y hy
  subst hv
  cases hz : ns[i / 8]? with
  | none => simp only [storeAt, hz]; exact h y hy
  | some z =>
    by_cases hyz : y = z
    · subst hyz; simp [storeAt, hz, upd, h y hy]
    · simp [storeAt, hz, upd, hyz, h y hy]

/-- **A store of a secret byte: every word of the array may now hold a secret, and the rest stay low-equal.** -/
theorem storeAt_high {H : List String} {s s' : Store} (h : Low H s s') (ns : List String) (i : Nat) (v v' : W64) :
    Low (ns ++ H) (storeAt s ns i v) (storeAt s' ns i v') := by
  intro y hy
  have hyn : y ∉ ns := fun hn => hy (List.mem_append_left _ hn)
  have hyH : y ∉ H := fun hn => hy (List.mem_append_right _ hn)
  rw [storeAt_other hyn, storeAt_other hyn]
  exact h y hyH

/-- **The bytes of low words are the same in two runs.** -/
theorem outBytes_low {H : List String} {s s' : Store} (h : Low H s s') {ns : List String} (hns : ∀ y ∈ ns, y ∉ H) :
    outBytes s ns = outBytes s' ns := by
  induction ns with
  | nil => rfl
  | cons y ys ih =>
    simp only [outBytes, List.flatMap_cons] at ih ⊢
    rw [h y (hns y List.mem_cons_self), ih (fun z hz => hns z (List.mem_cons_of_mem _ hz))]

inductive FT (ret : Expr) : St → List Frame → Prop where
  | nil  : ∀ {st : St}, highE st.1 ret = false → FT ret st []
  | cons : ∀ {st s₁ s₂ : St} {c : Cmd} {p : List Nat} {k : List Frame},
      highC st c = some s₁ → Sub s₁ s₂ → FT ret s₂ k → FT ret st ((c, p) :: k)

theorem push_ft {ret : Expr} : ∀ (c : Cmd) (p : List Nat) {st s₁ s₂ : St} {k : List Frame},
    highC st c = some s₁ → Sub s₁ s₂ → FT ret s₂ k → FT ret st (push c p k)
  | .seq a b, p, st, s₁, s₂, k, hc, hs, hk => by
    simp only [highC] at hc
    rcases ea : highC st a with _ | sa
    · rw [ea] at hc; simp at hc
    · rw [ea, Option.bind_some] at hc
      exact push_ft a _ ea (Sub.refl _) (push_ft b _ hc hs hk)
  | .skip, _, _, _, _, _, hc, hs, hk | .assign _ _, _, _, _, _, _, hc, hs, hk
  | .ite _ _ _, _, _, _, _, _, hc, hs, hk | .loop _ _, _, _, _, _, _, hc, hs, hk
  | .load _ _, _, _, _, _, _, hc, hs, hk | .loadB _ _ _, _, _, _, _, _, hc, hs, hk
  | .store _ _, _, _, _, _, _, hc, hs, hk | .storeB _ _ _, _, _, _, _, _, hc, hs, hk
  | .emitB _, _, _, _, _, _, hc, hs, hk => FT.cons hc hs hk

theorem low_set {H : List String} {s s' : Store} {x : String} {v v' : W64} (hl : Low H s s') (hv : v = v') :
    Low (H.filter (· ≠ x)) (upd s x v) (upd s' x v') := by
  intro y hy
  by_cases hyx : y = x
  · simp [upd, hyx, hv]
  · have hyH : y ∉ H := fun h => hy (List.mem_filter.mpr ⟨h, by simpa using hyx⟩)
    simp [upd, hyx, hl y hyH]

theorem low_high {H : List String} {s s' : Store} {x : String} {v v' : W64} (hl : Low H s s') :
    Low (x :: H) (upd s x v) (upd s' x v') := by
  intro y hy
  have hne : y ≠ x := fun h => hy (by simp [h])
  have hyH : y ∉ H := fun h => hy (List.mem_cons_of_mem _ h)
  simp [upd, hne, hl y hyH]

/-- **An accepted loop has an invariant** `w` that contains its head's state: a public guard, and a body that stays within it. -/
theorem loop_inv {st s₁ : St} {e : Expr} {b : Cmd} (h : highC st (.loop e b) = some s₁) :
    ∃ w : St, Sub st w ∧ s₁ = w ∧ highE w.1 e = false ∧ ∃ s₂, highC w b = some s₂ ∧ Sub s₂ w ∧ highC w (.loop e b) = some w := by
  have h0 := h
  simp only [highC] at h
  split at h
  · simp at h
  rename_i he
  rcases eb : highC st b with _ | sb
  · rw [eb] at h; simp at h
  rw [eb, Option.bind_some] at h
  split at h
  · rename_i hsub
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨st, Sub.refl _, rfl, by simpa using he, sb, eb, sub_sound hsub, h0⟩
  · rename_i hsub
    split at h
    · simp at h
    rename_i he'
    rcases eb' : highC (sb.1 ++ st.1, st.2 || sb.2) b with _ | sc
    · rw [eb'] at h; simp at h
    rw [eb', Option.bind_some] at h
    split at h
    · rename_i hsub'
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨_, ⟨fun v hv => List.mem_append_right _ hv, fun hv => by simp [hv]⟩, rfl, by simpa using he', sc, eb',
        sub_sound hsub', ?_⟩
      simp only [highC, eb', Option.bind_some, hsub', ite_true]
      simp only [Bool.not_eq_true] at he'
      simp [he']
    · simp at h

/-- **Two low-equal runs of accepted frames show the same, at every fuel**, whether or not they ever finish. -/
theorem run_same {ret : Expr} : ∀ (n : Nat) (st : St) (k : List Frame) (s s' : Store) (a a' : Arr),
    FT ret st k → LowS st s s' a a' → run ret n k s a = run ret n k s' a' := by
  intro n
  induction n with
  | zero =>
    intro st k s s' a a' hk hl
    cases hk with
    | nil he => simp only [run, eval_low hl.1 _ he]
    | cons => rfl
  | succ m ih =>
    intro st k s s' a a' hk hl
    cases hk with
    | nil he => simp only [run, eval_low hl.1 _ he]
    | @cons st s₁ s₂ c p k hc hs hk' =>
      cases c with
      | skip =>
        simp only [highC, Option.some.injEq] at hc
        subst hc
        simp only [run]
        rw [ih _ _ s s' a a' hk' (LowS.mono hs hl)]
      | assign x e =>
        simp only [highC] at hc
        have hnew : LowS s₁ (upd s x (eval e s)) (upd s' x (eval e s')) a a' := by
          split at hc
          · simp only [Option.some.injEq] at hc
            subst hc
            exact ⟨low_high hl.1, hl.2⟩
          · rename_i he
            simp only [Option.some.injEq] at hc
            subst hc
            exact ⟨low_set hl.1 (eval_low hl.1 e (by simpa using he)), hl.2⟩
        simp only [run]
        rw [ih _ _ _ _ _ _ hk' (LowS.mono hs hnew)]
      | seq c₁ c₂ =>
        simp only [highC] at hc
        rcases ea : highC st c₁ with _ | sa
        · rw [ea] at hc; simp at hc
        rw [ea, Option.bind_some] at hc
        exact ih _ _ s s' a a' (push_ft c₁ _ ea (Sub.refl _) (push_ft c₂ _ hc hs hk')) hl
      | ite e c₁ c₂ =>
        simp only [highC] at hc
        split at hc
        · simp at hc
        rename_i he
        rcases e1 : highC st c₁ with _ | sa
        · rw [e1] at hc; simp at hc
        rw [e1, Option.bind_some] at hc
        rcases e2 : highC st c₂ with _ | sb
        · rw [e2] at hc; simp at hc
        rw [e2] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        subst hc
        have hg : eval e s = eval e s' := eval_low hl.1 e (by simpa using he)
        simp only [run, hg]
        split
        · rw [ih _ _ s s' a a' (push_ft c₁ _ e1 ⟨fun v h => hs.1 v (List.mem_append_left _ h),
            fun h => hs.2 (by simp [h])⟩ hk') hl]
        · rw [ih _ _ s s' a a' (push_ft c₂ _ e2 ⟨fun v h => hs.1 v (List.mem_append_right _ h),
            fun h => hs.2 (by simp [h])⟩ hk') hl]
      | loop e b =>
        have hc0 := hc
        simp only [highC] at hc
        split at hc
        · simp at hc
        obtain ⟨w, hsw, hw, he, s₂, eb, hsub, hloop⟩ := loop_inv hc0
        subst hw
        have hl' := LowS.mono hsw hl
        have hg : eval e s = eval e s' := eval_low hl'.1 e he
        simp only [run, hg]
        split
        · rw [ih _ _ s s' a a' (push_ft b _ eb hsub (FT.cons hloop hs hk')) hl']
        · rw [ih _ _ s s' a a' hk' (LowS.mono hs hl')]
      | load x e =>
        simp only [highC] at hc
        split at hc
        · simp at hc
        rename_i he
        have hg : eval e s = eval e s' := eval_low hl.1 e (by simpa using he)
        have hnew : LowS s₁ (upd s x (a (idx (eval e s)))) (upd s' x (a' (idx (eval e s')))) a a' := by
          split at hc
          · rename_i hh
            simp only [Option.some.injEq] at hc
            subst hc
            exact ⟨low_high hl.1, hl.2⟩
          · rename_i hh
            simp only [Option.some.injEq] at hc
            subst hc
            have ha : a = a' := hl.2 (by simpa using hh)
            exact ⟨low_set hl.1 (by rw [hg, ha]), hl.2⟩
        simp only [run, hg]
        rw [hg] at hnew
        rw [ih _ _ _ _ _ _ hk' (LowS.mono hs hnew)]
      | loadB x ns e =>
        simp only [highC] at hc
        split at hc
        · simp at hc
        rename_i he
        simp only [Bool.or_eq_true, not_or] at he
        have hg : eval e s = eval e s' := eval_low hl.1 e (by simpa using he.1)
        have hne : ns ≠ [] := by intro h; apply he.2; simp [h]
        have hnew : LowS s₁ (upd s x (byteAt s ns (bidx ns (eval e s)))) (upd s' x (byteAt s' ns (bidx ns (eval e s')))) a a' := by
          split at hc
          · simp only [Option.some.injEq] at hc
            subst hc
            exact ⟨low_high hl.1, hl.2⟩
          · rename_i hh
            simp only [Option.some.injEq] at hc
            subst hc
            simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at hh
            have hb := byteAt_low hl.1 hh (bidx ns (eval e s))
            exact ⟨low_set hl.1 (by rw [hg] at hb ⊢; exact hb), hl.2⟩
        simp only [run, hg]
        rw [hg] at hnew
        rw [ih _ _ _ _ _ _ hk' (LowS.mono hs hnew)]
      | store e v =>
        simp only [highC] at hc
        split at hc
        · simp at hc
        rename_i he
        simp only [Option.some.injEq] at hc
        subst hc
        have hg : eval e s = eval e s' := eval_low hl.1 e (by simpa using he)
        have hnew : LowS (st.1, st.2 || highE st.1 v) s s' (updA a (idx (eval e s)) (eval v s))
            (updA a' (idx (eval e s')) (eval v s')) := by
          refine ⟨hl.1, fun h0 => ?_⟩
          simp only [Bool.or_eq_false_iff] at h0
          have ha : a = a' := hl.2 h0.1
          rw [hg, ha, eval_low hl.1 v h0.2]
        simp only [run, hg]
        rw [hg] at hnew
        rw [ih _ _ _ _ _ _ hk' (LowS.mono hs hnew)]
      | storeB ns e v =>
        simp only [highC] at hc
        split at hc
        · simp at hc
        rename_i he
        simp only [Bool.or_eq_true, not_or] at he
        have hg : eval e s = eval e s' := eval_low hl.1 e (by simpa using he.1)
        have hnew : LowS s₁ (storeAt s ns (bidx ns (eval e s)) (eval v s)) (storeAt s' ns (bidx ns (eval e s')) (eval v s')) a a' := by
          split at hc
          · simp only [Option.some.injEq] at hc
            subst hc
            rw [hg]
            exact ⟨storeAt_high hl.1 ns _ _ _, hl.2⟩
          · rename_i hh
            simp only [Option.some.injEq] at hc
            subst hc
            rw [hg]
            exact ⟨storeAt_low hl.1 ns _ (eval_low hl.1 v (by simpa using hh)), hl.2⟩
        simp only [run, hg]
        rw [hg] at hnew
        rw [ih _ _ _ _ _ _ hk' (LowS.mono hs hnew)]
      | emitB ns =>
        simp only [highC] at hc
        split at hc
        · simp at hc
        rename_i hh
        simp only [Option.some.injEq] at hc
        subst hc
        simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at hh
        simp only [run, outBytes_low hl.1 hh]
        rw [ih _ _ s s' a a' hk' (LowS.mono hs hl)]

/-- **`rel` on the source**: at every fuel, on inputs that agree at public positions, whatever the environment, whether or not the run finishes. -/
theorem sliceCheck_rel {E : Type} {P : Nat → Bool} {p : Prog} (h : sliceCheck P p = true) :
    Cert.rel (sliceLang E P) p := by
  intro n i i' _ _ hi
  simp only [sliceCheck] at h
  split at h
  · rename_i st eh
    have hr : highE st.1 p.ret = false := by simpa using h
    exact run_same n _ _ _ _ _ _ (push_ft p.body [] eh (Sub.refl _) (FT.nil hr))
      ⟨initFrom_low hi p.inputs 0, fun _ => rfl⟩
  · simp at h

/-! ## The budget, for loop-free programs -/

def loopFree : Cmd → Bool
  | .loop _ _ => false
  | .seq a b | .ite _ a b => loopFree a && loopFree b
  | _ => true

def costOf : Cmd → Nat
  | .seq a b => costOf a + costOf b
  | .ite _ a b => 1 + max (costOf a) (costOf b)
  | _ => 1

def costK : List Frame → Nat
  | [] => 0
  | (c, _) :: k => costOf c + costK k

theorem costK_push : ∀ (c : Cmd) (p : List Nat) (k : List Frame), costK (push c p k) = costOf c + costK k
  | .seq a b, p, k => by simp only [push, costK_push a, costK_push b, costOf]; omega
  | .skip, _, _ | .assign _ _, _, _ | .ite _ _ _, _, _ | .loop _ _, _, _ | .load _ _, _, _ | .loadB _ _ _, _, _
  | .store _ _, _, _ | .storeB _ _ _, _, _ | .emitB _, _, _ => rfl

def LF (k : List Frame) : Prop := ∀ f ∈ k, loopFree f.1 = true

theorem push_lf : ∀ (c : Cmd) (p : List Nat) (k : List Frame), loopFree c = true → LF k → LF (push c p k)
  | .seq a b, p, k, hc, hk => by
    simp only [loopFree, Bool.and_eq_true] at hc
    exact push_lf a _ _ hc.1 (push_lf b _ _ hc.2 hk)
  | .skip, _, _, hc, hk | .assign _ _, _, _, hc, hk | .ite _ _ _, _, _, hc, hk | .loop _ _, _, _, hc, hk
  | .load _ _, _, _, hc, hk | .loadB _ _ _, _, _, hc, hk | .store _ _, _, _, hc, hk
  | .storeB _ _ _, _, _, hc, hk | .emitB _, _, _, hc, hk => by
    intro f hf
    simp only [push, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hc
    · exact hk f hf

theorem run_cost (ret : Expr) : ∀ (n : Nat) (k : List Frame) (s : Store) (a : Arr), LF k →
    (run ret n k s a).cost ≤ costK k := by
  intro n
  induction n with
  | zero => intro k s a _; cases k <;> simp [run]
  | succ m ih =>
    intro k s a hk
    cases k with
    | nil => simp [run]
    | cons f k =>
      obtain ⟨c, p⟩ := f
      have hc : loopFree c = true := hk _ List.mem_cons_self
      have hk' : LF k := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      cases c with
      | skip => have := ih k s a hk'; simp only [run, tick, costK, costOf]; omega
      | assign x e => have := ih k (upd s x (eval e s)) a hk'; simp only [run, tick, costK, costOf]; omega
      | load x e => have := ih k (upd s x (a (idx (eval e s)))) a hk'; simp only [run, tick, costK, costOf]; omega
      | loadB x ns e => have := ih k (upd s x (byteAt s ns (bidx ns (eval e s)))) a hk'; simp only [run, tick, costK, costOf]; omega
      | store e v => have := ih k s (updA a (idx (eval e s)) (eval v s)) hk'; simp only [run, tick, costK, costOf]; omega
      | storeB ns e v => have := ih k (storeAt s ns (bidx ns (eval e s)) (eval v s)) a hk'; simp only [run, tick, costK, costOf]; omega
      | emitB ns => have := ih k s a hk'; simp only [run, etick, tick, costK, costOf]; omega
      | loop e b => simp [loopFree] at hc
      | seq c₁ c₂ =>
        simp only [loopFree, Bool.and_eq_true] at hc
        have := ih (push c₁ (p ++ [0]) (push c₂ (p ++ [1]) k)) s a (push_lf _ _ _ hc.1 (push_lf _ _ _ hc.2 hk'))
        rw [costK_push, costK_push] at this
        simp only [run, costK, costOf]; omega
      | ite e c₁ c₂ =>
        simp only [loopFree, Bool.and_eq_true] at hc
        simp only [run]
        split
        · have := ih (push c₁ (p ++ [0]) k) s a (push_lf _ _ _ hc.1 hk')
          rw [costK_push] at this
          simp only [tick, costK, costOf]; omega
        · have := ih (push c₂ (p ++ [1]) k) s a (push_lf _ _ _ hc.2 hk')
          rw [costK_push] at this
          simp only [tick, costK, costOf]; omega

/-- **`bound`, for a program with no loop.** -/
theorem slice_bound (E : Type) (P : Nat → Bool) (p : Prog) (hl : loopFree p.body = true) :
    Cert.bound (sliceLang E P) (costOf p.body) p := by
  intro n i _
  have := run_cost p.ret n (push p.body [] []) (initFrom i.1 p.inputs 0) zeroA (push_lf _ _ _ hl (fun _ h => by simp at h))
  rw [costK_push] at this
  show (run p.ret n (push p.body [] []) (initFrom i.1 p.inputs 0) zeroA).cost ≤ costOf p.body
  simpa [costK] using this

/-! ## Witnesses -/

/-- Leakage as numbers, since `decide` on `Lk` over unevaluated values is what exhausts the kernels (VS-2, step 1). -/
def lkCode : Lk → Nat
  | .branch true => 1
  | .branch false => 2
  | .addr (.ofNat a) => 100 + a
  | _ => 0

def num (n : Nat) : Expr := .lit (W64.ofNat n)
def minusOne : Expr := .lit (W64.ofNat (2 ^ 64 - 1))

/-- **Accepted**: a loop over the array at a public index, with a secret input present and unused. -/
def scan : Prog where
  inputs := ["s", "n"]
  body := .seq (.assign "i" (.var "n")) (.loop (.var "i")
    (.seq (.store (.var "i") (.var "n"))
      (.seq (.load "t" (.var "i"))
        (.seq (.assign "r" (.add (.var "r") (.var "t")))
          (.assign "i" (.add (.var "i") minusOne))))))
  ret := .var "r"

theorem scan_checks : sliceCheck sec0 scan = true := by decide
theorem scan_rel (E : Type) : Cert.rel (sliceLang E sec0) scan := sliceCheck_rel scan_checks

/-- **It does something, and its addresses depend on its public input**, so `rel` is not vacuous here. -/
theorem scan_runs :
    ((sliceLang Unit sec0).run 40 scan (inp 5 3, ())).ev = [retEv (W64.ofNat 9)]
  ∧ ((sliceLang Unit sec0).run 40 scan (inp 5 3, ())).out = .done
  ∧ ((sliceLang Unit sec0).run 40 scan (inp 5 3, ())).lk.map lkCode ≠
      ((sliceLang Unit sec0).run 40 scan (inp 5 2, ())).lk.map lkCode := by
  decide

/-- A loop that never ends. -/
def spin : Prog := { inputs := ["s", "n"], body := .loop (num 1) .skip, ret := num 0 }

theorem spin_checks : sliceCheck sec0 spin = true := by decide

/-- **Accepted, and it never finishes**, so the certificate covers a run that does not end. -/
theorem spin_covered (E : Type) : Cert.rel (sliceLang E sec0) spin := sliceCheck_rel spin_checks

theorem spin_never_finishes (n : Nat) : ((sliceLang Unit sec0).run (n + 1) spin (inp 5 1, ())).out = .fuel := by
  have key : ∀ (m : Nat) (s : Store), (run (num 0) m [(.loop (num 1) .skip, [])] s zeroA).out = .fuel := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro s
      cases m with
      | zero => rfl
      | succ m =>
        cases m with
        | zero =>
          have hg : (eval (num 1) s).val ≠ 0 := by show (W64.ofNat 1).val ≠ 0; decide
          simp only [run, hg, ne_eq, not_false_eq_true, ↓reduceIte, tick, push]
        | succ m =>
          have hg : (eval (num 1) s).val ≠ 0 := by show (W64.ofNat 1).val ≠ 0; decide
          simp only [run, hg, ne_eq, not_false_eq_true, ↓reduceIte, tick, push]
          exact ih m (by omega) s
  exact key (n + 1) _

/-- **Accepted**: a body that writes a secret to a variable already marked secret. The fixed point holds. -/
def markedFirst : Prog where
  inputs := ["s", "n"]
  body := .seq (.assign "t" (.var "s")) (.seq (.assign "i" (.var "n"))
    (.loop (.var "i") (.seq (.assign "t" (.var "s")) (.assign "i" (.add (.var "i") minusOne)))))
  ret := .var "i"

theorem markedFirst_checks : sliceCheck sec0 markedFirst = true := by decide

/-- Refuted by two runs differing only in the secret, on leakage. -/
theorem leak_lk {p : Prog} {a a' b n : Nat}
    (hne : ((sliceLang Unit sec0).run n p (inp a b, ())).lk.map lkCode ≠ ((sliceLang Unit sec0).run n p (inp a' b, ())).lk.map lkCode) :
    ¬ Cert.rel (sliceLang Unit sec0) p :=
  fun h => hne (congrArg (fun r : Beh => r.lk.map lkCode) (h n _ _ (inp_adm a b) (inp_adm a' b) (inp_low a a' b)))

/-- Refuted on the result. -/
theorem leak_ev {p : Prog} {a a' b n : Nat}
    (hne : ((sliceLang Unit sec0).run n p (inp a b, ())).ev ≠ ((sliceLang Unit sec0).run n p (inp a' b, ())).ev) :
    ¬ Cert.rel (sliceLang Unit sec0) p :=
  fun h => hne (congrArg Beh.ev (h n _ _ (inp_adm a b) (inp_adm a' b) (inp_low a a' b)))

/-- **Refused, the index rule on a load**, and the address leaks. -/
def secretLoad : Prog := { inputs := ["s", "n"], body := .load "t" (.var "s"), ret := num 0 }
theorem secretLoad_refused : sliceCheck sec0 secretLoad = false := by decide
theorem secretLoad_leaks : ¬ Cert.rel (sliceLang Unit sec0) secretLoad := leak_lk (n := 5) (a := 1) (a' := 2) (b := 1) (by decide)

/-- **Refused, the index rule on a store.** -/
def secretStore : Prog := { inputs := ["s", "n"], body := .store (.var "s") (num 1), ret := num 0 }
theorem secretStore_refused : sliceCheck sec0 secretStore = false := by decide
theorem secretStore_leaks : ¬ Cert.rel (sliceLang Unit sec0) secretStore := leak_lk (n := 5) (a := 1) (a' := 2) (b := 1) (by decide)

/-- **Refused, the loop-guard rule**: how long it runs shows the secret. -/
def secretLoop : Prog :=
  { inputs := ["s", "n"], body := .loop (.var "s") (.assign "s" (.add (.var "s") minusOne)), ret := num 0 }
theorem secretLoop_refused : sliceCheck sec0 secretLoop = false := by decide
theorem secretLoop_leaks : ¬ Cert.rel (sliceLang Unit sec0) secretLoop := leak_lk (n := 20) (a := 1) (a' := 2) (b := 1) (by decide)

/-- **Refused, the fixed point**: the branch on a secret happens only on the second iteration. A checker looking at the body once would accept this. -/
def secondIter : Prog where
  inputs := ["s", "n"]
  body := .seq (.assign "x" (num 0)) (.seq (.assign "i" (num 2)) (.loop (.var "i")
    (.seq (.ite (.var "x") .skip .skip)
      (.seq (.assign "x" (.var "s")) (.assign "i" (.add (.var "i") minusOne))))))
  ret := num 0
theorem secondIter_refused : sliceCheck sec0 secondIter = false := by decide
theorem secondIter_leaks : ¬ Cert.rel (sliceLang Unit sec0) secondIter := leak_lk (n := 40) (a := 0) (a' := 5) (b := 1) (by decide)

/-- **Refused, the array's bit**: a secret through the array and out. -/
def throughArray : Prog :=
  { inputs := ["s", "n"], body := .seq (.store (num 0) (.var "s")) (.load "t" (num 0)), ret := .var "t" }
theorem throughArray_refused : sliceCheck sec0 throughArray = false := by decide
theorem throughArray_leaks : ¬ Cert.rel (sliceLang Unit sec0) throughArray := leak_ev (n := 10) (a := 1) (a' := 2) (b := 1) (by decide)

/-- **Refused, the array's bit in a loop**: the store raises it past the head, so the load's value counts as secret too late. -/
def arrayInLoop : Prog where
  inputs := ["s", "n"]
  body := .seq (.assign "i" (num 2)) (.loop (.var "i")
    (.seq (.load "t" (num 0))
      (.seq (.ite (.var "t") .skip .skip)
        (.seq (.store (num 0) (.var "s")) (.assign "i" (.add (.var "i") minusOne))))))
  ret := num 0
theorem arrayInLoop_refused : sliceCheck sec0 arrayInLoop = false := by decide
theorem arrayInLoop_leaks : ¬ Cert.rel (sliceLang Unit sec0) arrayInLoop := leak_lk (n := 40) (a := 0) (a' := 5) (b := 1) (by decide)

/-- **Accepted**: while the array is low, a load clears its target, even one that held a secret. -/
theorem load_clears_when_low :
    sliceCheck sec0 { inputs := ["s", "n"], body := .seq (.assign "t" (.var "s")) (.load "t" (num 0)), ret := .var "t" } = true := by decide

/-- **Refused, the index rule on a byte store** (RC-02), and the address leaks. -/
def secretStoreB : Prog := { inputs := ["s", "n"], body := .storeB ["n"] (.var "s") (num 1), ret := num 0 }
theorem secretStoreB_refused : sliceCheck sec0 secretStoreB = false := by decide
theorem secretStoreB_leaks : ¬ Cert.rel (sliceLang Unit sec0) secretStoreB := leak_lk (n := 5) (a := 1) (a' := 2) (b := 1) (by decide)

/-- **Refused, the output rule** (RC-02): an output of a secret word, and the output shows it. -/
def secretEmit : Prog := { inputs := ["s", "n"], body := .emitB ["s"], ret := num 0 }
theorem secretEmit_refused : sliceCheck sec0 secretEmit = false := by decide
theorem secretEmit_leaks : ¬ Cert.rel (sliceLang Unit sec0) secretEmit := leak_ev (n := 5) (a := 1) (a' := 2) (b := 1) (by decide)

end LCore.Slice2
