/-
  P1, names to slots (PH1 step 5; CMP-P1 rebuilt after I-0003). Not Ring 0.

  The first pass of L's compiler: integer variables, named by strings, become slots, numbered by
  a table `T` (`slotOf T x` is `x`'s index). The compiled program runs on a slot machine whose
  integer store is indexed by `Nat`; everything else in the state is as in `UState`.

  The pass is a `PassCert (ucmdLang P π) (slotLang π)` with the identity leakage and cost
  transformers: a compiled run observes *exactly* what the source run observes. The content is
  one simulation (`texec_compile`): if the table lists every variable once, the slot store read
  through the table is the source store, at every step. The frame theorem is its corollary.
  `collide_leaks` shows why the table must be injective: a compiler that puts two variables in
  one slot turns a noninterferent program into a leaky one.
-/
import ConfTyping.LAdapter

namespace ConfTyping

/-! ## The slot machine -/

def slotOf : List String → String → Nat
  | [],      _ => 0
  | y :: ys, x => if y = x then 0 else slotOf ys x + 1

inductive TExpr where
  | num  : Int → TExpr
  | slot : Nat → TExpr
  | add  : TExpr → TExpr → TExpr

inductive TCmd where
  | skip   : TCmd
  | assign : Nat → TExpr → TCmd
  | check  : String → TCmd
  | access : String → TCmd
  | memop  : MemOp → Nat → TCmd
  | sop    : SOp → String → SExpr → TCmd
  | hop    : HOp → Nat → Nat → TCmd
  | seq    : TCmd → TCmd → TCmd
  | ite    : TExpr → TCmd → TCmd → TCmd
  | loop   : TExpr → TCmd → TCmd

/-- The slot machine's state: `UState` with the integer store indexed by slot. -/
structure SlotState where
  store : Nat → Int
  auth  : List String
  reads : List String
  dead  : Bool
  heap  : Int → Int
  live  : List Int
  fresh : Int
  err   : Bool
  freed : List Int
  hlab  : Int → Bool
  sstore : String → UStr
  sink  : List (String × UStr)

/-- Everything but the integer store, as a `UState` with the given store. -/
def SlotState.withStore (t : SlotState) (σ : Store) : UState :=
  ⟨σ, t.auth, t.reads, t.dead, t.heap, t.live, t.fresh, t.err, t.freed, t.hlab, t.sstore, t.sink⟩

def tupd (τ : Nat → Int) (k : Nat) (v : Int) : Nat → Int := fun j => if j = k then v else τ j

def tevalE : TExpr → (Nat → Int) → Int
  | .num n,   _ => n
  | .slot k,  τ => τ k
  | .add a b, τ => tevalE a τ + tevalE b τ

/-- The slot machine's evaluator: `uexec` line for line, with slots for names. -/
def texec : Nat → TCmd → MedPolicy → SlotState → Option (SlotState × Nat × List Bool)
  | 0,     _,            _, _ => none
  | _ + 1, .skip,        _, s => some (s, 1, [])
  | _ + 1, .assign k e,  _, s =>
      some (if s.dead then s else { s with store := tupd s.store k (tevalE e s.store) }, 1, [])
  | _ + 1, .check r,     π, s =>
      some (if s.dead then s
            else if π r then { s with auth := r :: s.auth }
            else { s with dead := true }, 1, [])
  | _ + 1, .access r,    _, s =>
      some (if s.dead then s else { s with reads := r :: s.reads }, 1, [])
  | _ + 1, .memop op k,  _, s =>
      some (if s.dead then s else
              match op with
              | .alloc => { s with store := tupd s.store k (pickAddr s.freed s.fresh),
                                   live := pickAddr s.freed s.fresh :: s.live,
                                   freed := dropInt (pickAddr s.freed s.fresh) s.freed,
                                   fresh := bumpFresh s.freed s.fresh,
                                   hlab := updBU s.hlab (pickAddr s.freed s.fresh) false,
                                   heap := updHU s.heap (pickAddr s.freed s.fresh) 0 }
              | .allocS => { s with store := tupd s.store k (pickAddr s.freed s.fresh),
                                    live := pickAddr s.freed s.fresh :: s.live,
                                    freed := dropInt (pickAddr s.freed s.fresh) s.freed,
                                    fresh := bumpFresh s.freed s.fresh,
                                    hlab := updBU s.hlab (pickAddr s.freed s.fresh) true,
                                    heap := updHU s.heap (pickAddr s.freed s.fresh) 0 }
              | .deref => if memInt (s.store k) s.live then s
                          else { s with dead := true, err := true }
              | .free  => if memInt (s.store k) s.live
                          then { s with live := dropInt (s.store k) s.live,
                                        freed := if s.hlab (s.store k) then s.freed
                                                 else s.store k :: s.freed }
                          else { s with dead := true, err := true }, 1, [])
  | _ + 1, .sop op x e,  _, s =>
      some (if s.dead then s else
              match op with
              | .set  => { s with sstore := updSU s.sstore x (evalS s.sstore e) }
              | .emit => { s with sink := (x, evalS s.sstore e) :: s.sink }, 1, [])
  | _ + 1, .hop op x y,  _, s =>
      some (if s.dead then s else
              match op with
              | .load  => if memInt (s.store y) s.live
                          then { s with store := tupd s.store x (s.heap (s.store y)) }
                          else { s with dead := true, err := true }
              | .store => if memInt (s.store x) s.live
                          then { s with heap := updHU s.heap (s.store x) (s.store y) }
                          else { s with dead := true, err := true }, 1, [])
  | n + 1, .seq c₁ c₂,   π, s =>
      (texec n c₁ π s).bind fun r₁ =>
        (texec n c₂ π r₁.1).map fun r₂ =>
          (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2)
  | n + 1, .ite e c₁ c₂, π, s =>
      if tevalE e s.store ≠ 0 then
        (texec n c₁ π s).map fun r => (r.1, 1 + r.2.1, true :: r.2.2)
      else
        (texec n c₂ π s).map fun r => (r.1, 1 + r.2.1, false :: r.2.2)
  | n + 1, .loop e c,    π, s =>
      if tevalE e s.store ≠ 0 then
        (texec n c π s).bind fun r₁ =>
          (texec n (.loop e c) π r₁.1).map fun r₂ =>
            (r₂.1, 1 + r₁.2.1 + r₂.2.1, true :: (r₁.2.2 ++ r₂.2.2))
      else some (s, 1, [false])


/-! ## The compiler -/

def compileE (T : List String) : Expr → TExpr
  | .num n   => .num n
  | .var x   => .slot (slotOf T x)
  | .add a b => .add (compileE T a) (compileE T b)

def compile (T : List String) : UCmd → TCmd
  | .skip          => .skip
  | .assign x e    => .assign (slotOf T x) (compileE T e)
  | .check r       => .check r
  | .access r      => .access r
  | .memop op x    => .memop op (slotOf T x)
  | .sop op x e    => .sop op x e
  | .hop op x y    => .hop op (slotOf T x) (slotOf T y)
  | .seq c₁ c₂     => .seq (compile T c₁) (compile T c₂)
  | .ite e c₁ c₂   => .ite (compileE T e) (compile T c₁) (compile T c₂)
  | .loop e c      => .loop (compileE T e) (compile T c)

/-- The integer variables an expression reads. -/
def evars : Expr → List String
  | .num _   => []
  | .var x   => [x]
  | .add a b => evars a ++ evars b

/-- The integer variables a program names (string variables and resource names are not
    renamed by P1). -/
def cvars : UCmd → List String
  | .assign x e  => x :: evars e
  | .memop _ x   => [x]
  | .hop _ x y   => [x, y]
  | .seq c₁ c₂   => cvars c₁ ++ cvars c₂
  | .ite e c₁ c₂ => evars e ++ cvars c₁ ++ cvars c₂
  | .loop e c    => evars e ++ cvars c
  | _            => []

/-! ## The table -/

theorem slotOf_inj : ∀ {T : List String} {x y : String}, T.Nodup → x ∈ T → y ∈ T →
    slotOf T x = slotOf T y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | z :: zs, x, y, hnd, hx, hy, h => by
      have hz : z ∉ zs := (List.nodup_cons.mp hnd).1
      have hnd' : zs.Nodup := (List.nodup_cons.mp hnd).2
      by_cases hzx : z = x <;> by_cases hzy : z = y
      · exact hzx.symm.trans hzy
      · simp [slotOf, hzx, hzy] at h <;> first | exact h | exact h.symm
      · simp [slotOf, hzx, hzy] at h <;> first | exact h | exact h.symm
      · simp only [slotOf, hzx, hzy, ite_false] at h
        have hx' : x ∈ zs := by
          rcases List.mem_cons.mp hx with h' | h'
          · exact absurd h'.symm hzx
          · exact h'
        have hy' : y ∈ zs := by
          rcases List.mem_cons.mp hy with h' | h'
          · exact absurd h'.symm hzy
          · exact h'
        exact slotOf_inj hnd' hx' hy' (Nat.succ.inj h)

/-- The slot store, read through the table, is the source store. -/
def StoreRel (T : List String) (τ : Nat → Int) (σ : Store) : Prop :=
  ∀ x ∈ T, τ (slotOf T x) = σ x

theorem tevalE_compile {T : List String} {τ : Nat → Int} {σ : Store} (hr : StoreRel T τ σ) :
    ∀ (e : Expr), (∀ x ∈ evars e, x ∈ T) → tevalE (compileE T e) τ = evalE e σ
  | .num _,   _  => rfl
  | .var x,   hv => hr x (hv x (by simp [evars]))
  | .add a b, hv => by
      simp only [compileE, tevalE, evalE]
      rw [tevalE_compile hr a (fun x hx => hv x (by simp [evars, hx])),
          tevalE_compile hr b (fun x hx => hv x (by simp [evars, hx]))]

theorem storeRel_upd {T : List String} {τ : Nat → Int} {σ : Store} (hnd : T.Nodup)
    (hr : StoreRel T τ σ) {x : String} (hx : x ∈ T) (v : Int) :
    StoreRel T (tupd τ (slotOf T x) v) (upd σ x v) := by
  intro y hy
  simp only [tupd, upd]
  by_cases hyx : y = x
  · subst hyx; simp
  · have : slotOf T y ≠ slotOf T x := fun h => hyx (slotOf_inj hnd hy hx h)
    rw [if_neg this, if_neg hyx]; exact hr y hy

/-- What the simulation preserves: equal cost and branches, and the source state is the target
    state with the slot store read through the table. -/
def TRel (T : List String) :
    Option (SlotState × Nat × List Bool) → Option (UState × Nat × List Bool) → Prop
  | none,   none   => True
  | some t, some s => t.2 = s.2 ∧ s.1 = t.1.withStore s.1.store ∧ StoreRel T t.1.store s.1.store
  | _,      _      => False


/-- **The simulation.** With a table listing each variable once and covering the program, a
    compiled run is the source run, step for step: same cost, same branches, same state except
    that the integer store is read through the table. -/
theorem texec_compile {T : List String} (hnd : T.Nodup) (π : MedPolicy) :
    ∀ (n : Nat) (c : UCmd) (t : SlotState) (σ : Store), (∀ x ∈ cvars c, x ∈ T) →
      StoreRel T t.store σ →
      TRel T (texec n (compile T c) π t) (uexec n c π (t.withStore σ)) := by
  intro n
  induction n with
  | zero => intro c t σ _ _; cases c <;> trivial
  | succ m ih =>
    intro c t σ hv hr
    cases c with
    | skip => exact ⟨rfl, rfl, hr⟩
    | assign x e =>
        have hx : x ∈ T := hv x (by simp [cvars])
        have he := tevalE_compile hr e (fun y hy => hv y (by simp [cvars, hy]))
        simp only [texec, uexec, compile]
        repeat' split
        all_goals first
          | exact ⟨rfl, rfl, hr⟩
          | exact ⟨rfl, rfl, by simp only [SlotState.withStore]; rw [← he]; exact storeRel_upd hnd hr hx _⟩
          | (simp only [SlotState.withStore] at *; contradiction)
    | check r | access r =>
        simp only [texec, uexec, compile]
        repeat' split
        all_goals first
          | exact ⟨rfl, rfl, hr⟩
          | (simp only [SlotState.withStore] at *; contradiction)
    | sop op x e =>
        simp only [texec, uexec, compile]
        cases op <;> (repeat' split) <;> first
          | exact ⟨rfl, rfl, hr⟩
          | (simp only [SlotState.withStore] at *; contradiction)
    | memop op x =>
        have hx : x ∈ T := hv x (by simp [cvars])
        have hxv : t.store (slotOf T x) = σ x := hr x hx
        simp only [texec, uexec, compile, hxv]
        cases op <;> (repeat' split) <;> first
          | exact ⟨rfl, rfl, hr⟩
          | exact ⟨rfl, rfl, storeRel_upd hnd hr hx _⟩
          | (simp only [SlotState.withStore] at *; contradiction)
    | hop op x y =>
        have hx : x ∈ T := hv x (by simp [cvars])
        have hy : y ∈ T := hv y (by simp [cvars])
        have hxv : t.store (slotOf T x) = σ x := hr x hx
        have hyv : t.store (slotOf T y) = σ y := hr y hy
        simp only [texec, uexec, compile, hxv, hyv]
        cases op <;> (repeat' split) <;> first
          | exact ⟨rfl, rfl, hr⟩
          | exact ⟨rfl, rfl, storeRel_upd hnd hr hx _⟩
          | (simp only [SlotState.withStore] at *; contradiction)
    | seq c₁ c₂ =>
        have hv₁ : ∀ x ∈ cvars c₁, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have hv₂ : ∀ x ∈ cvars c₂, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have h₁ := ih c₁ t σ hv₁ hr
        show TRel T ((texec m (compile T c₁) π t).bind _) ((uexec m c₁ π (t.withStore σ)).bind _)
        rcases e₁ : texec m (compile T c₁) π t with _ | r₁ <;>
          rcases e₂ : uexec m c₁ π (t.withStore σ) with _ | s₁
        · trivial
        · rw [e₁, e₂] at h₁; exact h₁.elim
        · rw [e₁, e₂] at h₁; exact h₁.elim
        rw [e₁, e₂] at h₁
        obtain ⟨hc₁, hs₁, hr₁⟩ := h₁
        simp only [Option.bind_some]
        rw [hs₁]
        have h₂ := ih c₂ r₁.1 s₁.1.store hv₂ hr₁
        rcases e₃ : texec m (compile T c₂) π r₁.1 with _ | r₂ <;>
          rcases e₄ : uexec m c₂ π (r₁.1.withStore s₁.1.store) with _ | s₂
        · trivial
        · rw [e₃, e₄] at h₂; exact h₂.elim
        · rw [e₃, e₄] at h₂; exact h₂.elim
        rw [e₃, e₄] at h₂
        obtain ⟨hc₂, hs₂, hr₂⟩ := h₂
        refine ⟨?_, hs₂, hr₂⟩
        dsimp only; rw [hc₁, hc₂]
    | ite e c₁ c₂ =>
        have he := tevalE_compile hr e (fun y hy => hv y (by simp [cvars, hy]))
        have hv₁ : ∀ x ∈ cvars c₁, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have hv₂ : ∀ x ∈ cvars c₂, x ∈ T := fun x h => hv x (by simp [cvars, h])
        show TRel T (if tevalE (compileE T e) t.store ≠ 0 then _ else _)
          (if evalE e (t.withStore σ).store ≠ 0 then _ else _)
        rw [he]
        show TRel T (if evalE e σ ≠ 0 then _ else _) (if evalE e σ ≠ 0 then _ else _)
        split
        · have h₁ := ih c₁ t σ hv₁ hr
          rcases e₁ : texec m (compile T c₁) π t with _ | r₁ <;>
            rcases e₂ : uexec m c₁ π (t.withStore σ) with _ | s₁
          · exact True.intro
          · rw [e₁, e₂] at h₁; exact h₁.elim
          · rw [e₁, e₂] at h₁; exact h₁.elim
          rw [e₁, e₂] at h₁
          obtain ⟨hc, hs, hrr⟩ := h₁
          exact ⟨by dsimp only; rw [hc], hs, hrr⟩
        · have h₂ := ih c₂ t σ hv₂ hr
          rcases e₁ : texec m (compile T c₂) π t with _ | r₁ <;>
            rcases e₂ : uexec m c₂ π (t.withStore σ) with _ | s₁
          · exact True.intro
          · rw [e₁, e₂] at h₂; exact h₂.elim
          · rw [e₁, e₂] at h₂; exact h₂.elim
          rw [e₁, e₂] at h₂
          obtain ⟨hc, hs, hrr⟩ := h₂
          exact ⟨by dsimp only; rw [hc], hs, hrr⟩
    | loop e c₀ =>
        have he := tevalE_compile hr e (fun y hy => hv y (by simp [cvars, hy]))
        have hv₀ : ∀ x ∈ cvars c₀, x ∈ T := fun x h => hv x (by simp [cvars, h])
        show TRel T (if tevalE (compileE T e) t.store ≠ 0 then _ else _)
          (if evalE e (t.withStore σ).store ≠ 0 then _ else _)
        rw [he]
        show TRel T (if evalE e σ ≠ 0 then _ else _) (if evalE e σ ≠ 0 then _ else _)
        split
        · have h₁ := ih c₀ t σ hv₀ hr
          rcases e₁ : texec m (compile T c₀) π t with _ | r₁ <;>
            rcases e₂ : uexec m c₀ π (t.withStore σ) with _ | s₁
          · exact True.intro
          · rw [e₁, e₂] at h₁; exact h₁.elim
          · rw [e₁, e₂] at h₁; exact h₁.elim
          rw [e₁, e₂] at h₁
          obtain ⟨hc₁, hs₁, hr₁⟩ := h₁
          simp only [Option.bind_some]
          rw [hs₁]
          have h₂ := ih (.loop e c₀) r₁.1 s₁.1.store hv hr₁
          simp only [compile] at h₂
          rcases e₃ : texec m (.loop (compileE T e) (compile T c₀)) π r₁.1 with _ | r₂ <;>
            rcases e₄ : uexec m (.loop e c₀) π (r₁.1.withStore s₁.1.store) with _ | s₂
          · exact True.intro
          · rw [e₃, e₄] at h₂; exact h₂.elim
          · rw [e₃, e₄] at h₂; exact h₂.elim
          rw [e₃, e₄] at h₂
          obtain ⟨hc₂, hs₂, hr₂⟩ := h₂
          refine ⟨?_, hs₂, hr₂⟩
          dsimp only; rw [hc₁, hc₂]
        · exact ⟨rfl, rfl, hr⟩


/-! ## The address trace on the slot machine -/

def taddrs : Nat → TCmd → MedPolicy → SlotState → Option (List Int)
  | 0,     _,            _, _ => none
  | _ + 1, .memop op k,  _, s =>
      some (if s.dead then [] else
              match op with
              | .alloc | .allocS => [pickAddr s.freed s.fresh]
              | .deref | .free   => [s.store k])
  | _ + 1, .hop op k j,  _, s =>
      some (if s.dead then [] else
              match op with
              | .load  => [s.store j]
              | .store => [s.store k])
  | n + 1, .seq c₁ c₂,   π, s =>
      (texec n c₁ π s).bind fun r₁ =>
        (taddrs n c₁ π s).bind fun a₁ =>
          (taddrs n c₂ π r₁.1).map fun a₂ => a₁ ++ a₂
  | n + 1, .ite e c₁ c₂, π, s =>
      if tevalE e s.store ≠ 0 then taddrs n c₁ π s else taddrs n c₂ π s
  | n + 1, .loop e c,    π, s =>
      if tevalE e s.store ≠ 0 then
        (texec n c π s).bind fun r₁ =>
          (taddrs n c π s).bind fun a₁ =>
            (taddrs n (.loop e c) π r₁.1).map fun a₂ => a₁ ++ a₂
      else some []
  | _ + 1, _,            _, _ => some []

/-- The compiled program touches the same addresses. -/
theorem taddrs_compile {T : List String} (hnd : T.Nodup) (π : MedPolicy) :
    ∀ (n : Nat) (c : UCmd) (t : SlotState) (σ : Store), (∀ x ∈ cvars c, x ∈ T) →
      StoreRel T t.store σ →
      taddrs n (compile T c) π t = uaddrs n c π (t.withStore σ) := by
  intro n
  induction n with
  | zero => intro c t σ _ _; cases c <;> rfl
  | succ m ih =>
    intro c t σ hv hr
    cases c with
    | memop op x =>
        have hxv : t.store (slotOf T x) = σ x := hr x (hv x (by simp [cvars]))
        simp only [taddrs, uaddrs, compile, hxv]; rfl
    | hop op x y =>
        have hxv : t.store (slotOf T x) = σ x := hr x (hv x (by simp [cvars]))
        have hyv : t.store (slotOf T y) = σ y := hr y (hv y (by simp [cvars]))
        simp only [taddrs, uaddrs, compile, hxv, hyv]; rfl
    | seq c₁ c₂ =>
        have hv₁ : ∀ x ∈ cvars c₁, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have hv₂ : ∀ x ∈ cvars c₂, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have h₁ := texec_compile hnd π m c₁ t σ hv₁ hr
        show (texec m (compile T c₁) π t).bind _ = (uexec m c₁ π (t.withStore σ)).bind _
        rw [ih c₁ t σ hv₁ hr]
        rcases e₁ : texec m (compile T c₁) π t with _ | r₁ <;>
          rcases e₂ : uexec m c₁ π (t.withStore σ) with _ | s₁
        · rfl
        · rw [e₁, e₂] at h₁; exact h₁.elim
        · rw [e₁, e₂] at h₁; exact h₁.elim
        rw [e₁, e₂] at h₁
        obtain ⟨_, hs₁, hr₁⟩ := h₁
        simp only [Option.bind_some]
        rw [hs₁, ih c₂ r₁.1 s₁.1.store hv₂ hr₁]
    | ite e c₁ c₂ =>
        have he := tevalE_compile hr e (fun y hy => hv y (by simp [cvars, hy]))
        have hv₁ : ∀ x ∈ cvars c₁, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have hv₂ : ∀ x ∈ cvars c₂, x ∈ T := fun x h => hv x (by simp [cvars, h])
        show (if tevalE (compileE T e) t.store ≠ 0 then _ else _) =
          (if evalE e (t.withStore σ).store ≠ 0 then _ else _)
        rw [he]
        show (if evalE e σ ≠ 0 then _ else _) = (if evalE e σ ≠ 0 then _ else _)
        split
        · exact ih c₁ t σ hv₁ hr
        · exact ih c₂ t σ hv₂ hr
    | loop e c₀ =>
        have he := tevalE_compile hr e (fun y hy => hv y (by simp [cvars, hy]))
        have hv₀ : ∀ x ∈ cvars c₀, x ∈ T := fun x h => hv x (by simp [cvars, h])
        show (if tevalE (compileE T e) t.store ≠ 0 then _ else _) =
          (if evalE e (t.withStore σ).store ≠ 0 then _ else _)
        rw [he]
        show (if evalE e σ ≠ 0 then _ else _) = (if evalE e σ ≠ 0 then _ else _)
        split
        · have h₁ := texec_compile hnd π m c₀ t σ hv₀ hr
          rw [ih c₀ t σ hv₀ hr]
          rcases e₁ : texec m (compile T c₀) π t with _ | r₁ <;>
            rcases e₂ : uexec m c₀ π (t.withStore σ) with _ | s₁
          · rfl
          · rw [e₁, e₂] at h₁; exact h₁.elim
          · rw [e₁, e₂] at h₁; exact h₁.elim
          rw [e₁, e₂] at h₁
          obtain ⟨_, hs₁, hr₁⟩ := h₁
          simp only [Option.bind_some]
          have := ih (.loop e c₀) r₁.1 s₁.1.store hv hr₁
          simp only [compile] at this
          rw [hs₁, this]
        · rfl
    | skip | assign _ _ | check _ | access _ | sop _ _ _ => rfl


/-! ## The table a program gets -/

/-- The program's variables, each once. -/
def dedup : List String → List String
  | []      => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup : ∀ {l : List String} {x : String}, x ∈ dedup l ↔ x ∈ l
  | [], _ => by simp [dedup]
  | y :: ys, x => by
      unfold dedup
      split
      · rename_i hy
        rw [mem_dedup]
        constructor
        · intro h; exact List.mem_cons_of_mem _ h
        · intro h
          rcases List.mem_cons.mp h with h | h
          · subst h; exact mem_dedup.mp hy
          · exact h
      · simp [mem_dedup]

theorem nodup_dedup : ∀ (l : List String), (dedup l).Nodup
  | [] => by simp [dedup]
  | y :: ys => by
      unfold dedup
      split
      · exact nodup_dedup ys
      · rename_i hy; exact List.nodup_cons.mpr ⟨hy, nodup_dedup ys⟩

theorem slotOf_mem : ∀ {T : List String} {x : String}, x ∈ T →
    ∃ h : slotOf T x < T.length, T[slotOf T x] = x
  | [], _, hx => by cases hx
  | z :: zs, x, hx => by
      by_cases hzx : z = x
      · subst hzx; exact ⟨by simp [slotOf], by simp [slotOf]⟩
      · have hx' : x ∈ zs := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h.symm hzx
          · exact h
        obtain ⟨hl, he⟩ := slotOf_mem hx'
        refine ⟨by simp [slotOf, hzx]; omega, ?_⟩
        simp [slotOf, hzx, he]

/-! ## The slot machine as an L `Lang` -/

/-- The initial slot state: slot `k` holds the input's value of the table's `k`-th variable. -/
def initT (T : List String) (σ : Store) : SlotState :=
  ⟨fun k => if h : k < T.length then σ T[k] else 0, [], [], false, fun _ => 0, [], 0, false, [],
   fun _ => false, fun _ => [], []⟩

theorem initT_rel {T : List String} {σ : Store} : StoreRel T (initT T σ).store σ := by
  intro x hx
  obtain ⟨hl, he⟩ := slotOf_mem hx
  simp only [initT, dif_pos hl, he]

theorem initT_withStore (T : List String) (σ : Store) : (initT T σ).withStore σ = initU σ := rfl

/-- The observation of a slot-machine run: the same builder as the source's, on the state with
    any integer store (the observation never reads it). -/
def tBeh (r : Option (SlotState × Nat × List Bool)) (a : Option (List Int)) : LCore.Beh :=
  uBeh (r.map fun r => (r.1.withStore (fun _ => 0), r.2)) a

/-- **The slot machine as an L `Lang`.** A program is its table and its slot code. -/
def slotLang (P : Partition) (π : MedPolicy) : LCore.Lang where
  Prog  := List String × TCmd
  In    := Store
  lowIn := lowEq P
  run n p σ := tBeh (texec n p.2 π (initT p.1 σ)) (taddrs n p.2 π (initT p.1 σ))

/-- `uBeh` reads only the fields `withStore` keeps. -/
theorem uBeh_withStore (t : SlotState) (σ σ' : Store) (k : Nat) (b : List Bool) (a : Option (List Int)) :
    uBeh (some (t.withStore σ, k, b)) a = uBeh (some (t.withStore σ', k, b)) a := by
  cases a <;> rfl

/-! ## P1 as a certified pass -/

def p1Table (c : UCmd) : List String := dedup (cvars c)

/-- **P1, names to slots, certified.** Identity leakage and cost transformers: the compiled
    program's observation is the source's, exactly. -/
def p1Pass (P : Partition) (π : MedPolicy) : LCore.PassCert (ucmdLang P π) (slotLang P π) where
  comp c := .ok (p1Table c, compile (p1Table c) c)
  enc σ := σ
  lkT _ l := l
  costT _ k := k
  fuelT _ m := m
  costMono _ _ _ h := h
  sim c p' h m σ := by
    cases h
    have hnd := nodup_dedup (cvars c)
    have hv : ∀ x ∈ cvars c, x ∈ p1Table c := fun x hx => mem_dedup.mpr hx
    have hsim : TRel (p1Table c) (texec m (compile (p1Table c) c) π (initT (p1Table c) σ))
        (uexec m c π (initU σ)) := texec_compile hnd π m c (initT (p1Table c) σ) σ hv initT_rel
    have haddr : taddrs m (compile (p1Table c) c) π (initT (p1Table c) σ) = uaddrs m c π (initU σ) :=
      taddrs_compile hnd π m c (initT (p1Table c) σ) σ hv initT_rel
    show tBeh (texec m (compile (p1Table c) c) π (initT (p1Table c) σ))
        (taddrs m (compile (p1Table c) c) π (initT (p1Table c) σ))
      = uBeh (uexec m c π (initU σ)) (uaddrs m c π (initU σ))
    simp only [tBeh]
    rw [haddr]
    rcases e₁ : texec m (compile (p1Table c) c) π (initT (p1Table c) σ) with _ | ⟨r₁, k, b⟩ <;>
      rcases e₂ : uexec m c π (initU σ) with _ | ⟨s₁, k', b'⟩
    · rfl
    · rw [e₁, e₂] at hsim; exact hsim.elim
    · rw [e₁, e₂] at hsim; exact hsim.elim
    rw [e₁, e₂] at hsim
    obtain ⟨hc, hs, _⟩ := hsim
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [Option.map_some]
    have hs' : s₁ = r₁.withStore s₁.store := hs
    rw [hs']
    exact uBeh_withStore r₁ _ _ _ _ _

/-- **The Phase 1 exit (PLAN-2026-10 §12): `ucmd_p1_carries`.** A program `bcheck` accepts
    keeps its budget, its mediation and its noninterference (addresses in the leakage) after
    P1, by the kernel's transfer theorems alone. There is no proof here about any certificate
    and P1 together. -/
theorem ucmd_p1_carries {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    let p' := (p1Table c, compile (p1Table c) c)
    (∀ m σ, ((slotLang P π).run m p' σ).cost ≤ k)
  ∧ (∀ m σ, mediated π ((slotLang P π).run m p' σ).ev)
  ∧ (∀ m σ σ', lowEq P σ σ' → (slotLang P π).run m p' σ = (slotLang P π).run m p' σ') := by
  obtain ⟨hb, ht, hr⟩ := bcheck_lcore h π
  exact ⟨(p1Pass P π).bound_transfer rfl hb,
         (p1Pass P π).trace_transfer rfl ht,
         (p1Pass P π).rel_transfer rfl hr⟩


/-! ## The frame theorem -/

theorem slotOf_lt {T : List String} {x : String} (hx : x ∈ T) : slotOf T x < T.length :=
  (slotOf_mem hx).1

/-- **Frame.** A compiled program never writes a slot outside its table. -/
theorem texec_frame {T : List String} (π : MedPolicy) :
    ∀ (n : Nat) (c : UCmd) (t : SlotState) (r : SlotState × Nat × List Bool),
      (∀ x ∈ cvars c, x ∈ T) → texec n (compile T c) π t = some r →
      ∀ j, T.length ≤ j → r.1.store j = t.store j := by
  intro n
  induction n with
  | zero => intro c t r _ h; cases c <;> simp [texec] at h
  | succ m ih =>
    intro c t r hv h j hj
    have hne : ∀ x ∈ cvars c, j ≠ slotOf T x := fun x hx he => by
      have := slotOf_lt (hv x hx); omega
    cases c with
    | seq c₁ c₂ =>
        have hv₁ : ∀ x ∈ cvars c₁, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have hv₂ : ∀ x ∈ cvars c₂, x ∈ T := fun x h => hv x (by simp [cvars, h])
        simp only [compile, texec] at h
        rcases e₁ : texec m (compile T c₁) π t with _ | r₁
        · rw [e₁] at h; simp at h
        rw [e₁, Option.bind_some] at h
        rcases e₂ : texec m (compile T c₂) π r₁.1 with _ | r₂
        · rw [e₂] at h; simp at h
        rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        exact (ih c₂ r₁.1 r₂ hv₂ e₂ j hj).trans (ih c₁ t r₁ hv₁ e₁ j hj)
    | ite e c₁ c₂ =>
        have hv₁ : ∀ x ∈ cvars c₁, x ∈ T := fun x h => hv x (by simp [cvars, h])
        have hv₂ : ∀ x ∈ cvars c₂, x ∈ T := fun x h => hv x (by simp [cvars, h])
        simp only [compile, texec] at h
        split at h
        · rcases e₁ : texec m (compile T c₁) π t with _ | r₁
          · rw [e₁] at h; simp at h
          rw [e₁] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
          exact ih c₁ t r₁ hv₁ e₁ j hj
        · rcases e₂ : texec m (compile T c₂) π t with _ | r₂
          · rw [e₂] at h; simp at h
          rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
          exact ih c₂ t r₂ hv₂ e₂ j hj
    | loop e c₀ =>
        have hv₀ : ∀ x ∈ cvars c₀, x ∈ T := fun x h => hv x (by simp [cvars, h])
        simp only [compile, texec] at h
        split at h
        · rcases e₁ : texec m (compile T c₀) π t with _ | r₁
          · rw [e₁] at h; simp at h
          rw [e₁, Option.bind_some] at h
          rcases e₂ : texec m (.loop (compileE T e) (compile T c₀)) π r₁.1 with _ | r₂
          · rw [e₂] at h; simp at h
          rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
          have h₂ := ih (.loop e c₀) r₁.1 r₂ hv (by simpa [compile] using e₂) j hj
          exact h₂.trans (ih c₀ t r₁ hv₀ e₁ j hj)
        · simp only [Option.some.injEq] at h; subst h; rfl
    | assign x e =>
        have hjx := hne x (by simp [cvars])
        simp only [compile, texec, Option.some.injEq] at h; subst h
        split <;> simp [tupd, hjx]
    | memop op x =>
        have hjx := hne x (by simp [cvars])
        simp only [compile, texec, Option.some.injEq] at h; subst h
        cases op <;> (repeat' split) <;> simp [tupd, hjx]
    | hop op x y =>
        have hjx := hne x (by simp [cvars])
        simp only [compile, texec, Option.some.injEq] at h; subst h
        cases op <;> (repeat' split) <;> simp [tupd, hjx]
    | skip => simp only [compile, texec, Option.some.injEq] at h; subst h; rfl
    | check q =>
        simp only [compile, texec, Option.some.injEq] at h; subst h
        (repeat' split) <;> rfl
    | access q =>
        simp only [compile, texec, Option.some.injEq] at h; subst h
        split <;> rfl
    | sop op x e =>
        simp only [compile, texec, Option.some.injEq] at h; subst h
        cases op <;> split <;> rfl

/-! ## Witnesses -/

/-- A small program that does something observable: set `x`, branch on it, read `db`. -/
def p1Demo : UCmd := .seq (.assign "x" (.num 3)) (.ite (.var "x") (.access "db") .skip)

/-- P1 on it, run: the slot machine reads `db`, as the source does (decided, not just proved
    in general). -/
theorem p1Demo_runs :
    (slotLang Psec (fun _ => true)).run 4 (p1Table p1Demo, compile (p1Table p1Demo) p1Demo) σSecret0
      = (ucmdLang Psec (fun _ => true)).run 4 p1Demo σSecret0
  ∧ ((ucmdLang Psec (fun _ => true)).run 4 p1Demo σSecret0).ev = [.read "db"] := by decide

/-- **The table is load-bearing.** Compiled with a table that does not cover the program,
    `x` and `y` share a slot, and the compiled run no longer reads `db`: the observation
    changes. `texec_compile`'s hypotheses are what rule this out. -/
def p1Collide : UCmd :=
  .seq (.assign "x" (.num 1)) (.seq (.assign "y" (.num 0)) (.ite (.var "x") (.access "db") .skip))

theorem collide_breaks_simulation :
    (slotLang Psec (fun _ => true)).run 6 ([], compile [] p1Collide) σSecret0
      ≠ (ucmdLang Psec (fun _ => true)).run 6 p1Collide σSecret0 := by decide

end ConfTyping
