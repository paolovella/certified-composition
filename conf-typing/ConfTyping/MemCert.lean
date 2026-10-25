/-
  The composable core, stage 1h: a heap, and memory safety as a *separate* certificate.

  Stage 1g put the coverage at six of sixteen rows and named the obstacle: the
  remaining rows need the language to grow. This grows it. `UCmd` gains one
  constructor — `memop : MemOp → String → UCmd`, bundling `alloc`/`deref`/`free` so
  every downstream match takes **one** new case rather than three — and `UState`
  gains a heap, a live-address list, a fresh counter and an `err` flag recording a
  memory fault. Pointers are ordinary `Int` values in the existing store, so the value
  domain did not have to change; that is why this row was reachable and injection was
  not.

  The design decision worth naming: memory safety is **not** folded into `ucheck`. It
  gets its own analysis and its own certificate, and the bundle composes them. That is
  the honest test of stage 1a's claim — a genuinely new property, added later, by
  someone who did not write the original checker, should not require touching it. It
  did not: `ucheck` gained a single conservative line (`none` at a `memop`) and
  nothing else in stages 1c–1g was modified.

  What is proved: `umcheck_sound` — a checked program never faults, on any policy, from
  any state satisfying the invariant. The certificate is again a Hoare triple
  `{V} c {V'}` on the set of variables known to hold a live pointer, so it accumulates
  by threading, exactly like the authorization set, and joins at branches by
  intersection.

  Honest scope, and it is narrower than the rest of the module list. **No `free`.**
  The rules cover `alloc` and `deref`; `free` is in the *syntax* and the *semantics*
  but has no typing rule, because dropping an address from `live` invalidates every
  alias of it, and soundness would need brick 12's linearity or brick 19's must-alias
  tracking carried in the invariant. So this closes the wild-access half of row 6
  (CWE-119) and not the use-after-free half (CWE-416) — `free_has_no_rule` records
  that as a theorem rather than a footnote. (Stage 1i lifts the limit with a
  *separating* invariant, and proves that this one could not have been patched:
  `memInv_not_preserved_by_free` shows `MemInv` is not inductive for `free`. The
  theorem below stays true as a statement about `umcheck`, which is what it says.) **And no NI interaction**: `alloc` writes
  the fresh counter into the observable store, so heap ops are not NI-typed yet
  (`memops_not_yet_NI_typed`); whether allocation addresses are Low-visible is the
  same kind of question stage 1d settled for `reads`, and deserves the same care.
-/
import ConfTyping.BundleCoverage

namespace ConfTyping

/-! ## Removing a variable from a tracked set -/

def dropStr (x : String) : List String → List String
  | []      => []
  | y :: ys => if y == x then dropStr x ys else y :: dropStr x ys

theorem dropStr_mem {x y : String} : ∀ {V : List String}, y ∈ dropStr x V → y ∈ V
  | [],      h => by simp [dropStr] at h
  | z :: zs, h => by
      by_cases hz : z = x
      · rw [dropStr, ite_eq_left (by simp [hz])] at h
        exact List.mem_cons_of_mem _ (dropStr_mem h)
      · rw [dropStr, ite_eq_right (by simpa using hz)] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact h' ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (dropStr_mem h')

theorem dropStr_ne {x y : String} : ∀ {V : List String}, y ∈ dropStr x V → ¬ (y = x)
  | [],      h => by simp [dropStr] at h
  | z :: zs, h => by
      by_cases hz : z = x
      · rw [dropStr, ite_eq_left (by simp [hz])] at h; exact dropStr_ne h
      · rw [dropStr, ite_eq_right (by simpa using hz)] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact h' ▸ (by simpa using hz)
        · exact dropStr_ne h'

/-! ## The invariant and the certificate -/

/-- No fault has happened, and — while the run is live — every variable the analysis
    tracks really does hold an allocated address. -/
def MemInv (V : List String) (s : UState) : Prop :=
  s.err = false ∧ (s.dead = false → ∀ x ∈ V, memInt (s.store x) s.live = true)

/-- A **memory-safety certificate**: a Hoare triple on the set of variables known to
    hold a live pointer. It threads under `seq` and intersects at a branch, exactly
    like the authorization set — a third instance of the same shape. -/
structure MemCert (V : List String) (c : UCmd) (V' : List String) : Prop where
  safe : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    MemInv V s → uexec n c π s = some r → MemInv V' r.1

theorem MemCert.seq {V V₁ V₂ : List String} {c₁ c₂ : UCmd}
    (h₁ : MemCert V c₁ V₁) (h₂ : MemCert V₁ c₂ V₂) : MemCert V (.seq c₁ c₂) V₂ := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      rw [uexec_seq_eq] at hr
      rcases e₁ : uexec n c₁ π s with _ | r₁
      · rw [e₁] at hr; simp at hr
      · rw [e₁, Option.bind_some] at hr
        rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
        · rw [e₂] at hr; simp at hr
        · rw [e₂] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact h₂.safe n π r₁.1 r₂ (h₁.safe n π s r₁ hinv e₁) e₂

theorem MemCert.ite {V V₁ V₂ : List String} {e : Expr} {c₁ c₂ : UCmd}
    (h₁ : MemCert V c₁ V₁) (h₂ : MemCert V c₂ V₂) :
    MemCert V (.ite e c₁ c₂) (interStr V₁ V₂) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      rw [uexec_ite_eq] at hr
      by_cases hg : evalE e s.store ≠ 0
      · rw [ite_eq_left hg] at hr
        rcases e₁ : uexec n c₁ π s with _ | r₁
        · rw [e₁] at hr; simp at hr
        · rw [e₁] at hr; simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          obtain ⟨he, hv⟩ := h₁.safe n π s r₁ hinv e₁
          exact ⟨he, fun hd q hq => hv hd q (interStr_left hq)⟩
      · rw [ite_eq_right hg] at hr
        rcases e₂ : uexec n c₂ π s with _ | r₂
        · rw [e₂] at hr; simp at hr
        · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          obtain ⟨he, hv⟩ := h₂.safe n π s r₂ hinv e₂
          exact ⟨he, fun hd q hq => hv hd q (interStr_right hq)⟩

/-! ## The rules -/

theorem MemCert.skip {V : List String} : MemCert V .skip V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; exact hinv

/-- An assignment may destroy a pointer, so the variable leaves the tracked set. -/
theorem MemCert.assign {V : List String} (x : String) (e : Expr) :
    MemCert V (.assign x e) (dropStr x V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [ite_eq_left hd]
        exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [ite_eq_right hd]
        refine ⟨he, fun _ q hq => ?_⟩
        have hqx : ¬ (q = x) := dropStr_ne hq
        show memInt (upd s.store x (evalE e s.store) q) s.live = true
        simp only [upd, ite_eq_right hqx]
        exact hv hd0 q (dropStr_mem hq)

/-- `check` and `access` touch nothing the heap analysis tracks. -/
theorem MemCert.check {V : List String} (r₀ : String) : MemCert V (.check r₀) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [ite_eq_left hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [ite_eq_right hd]
        by_cases hp : π r₀ = true
        · simp only [ite_eq_left hp]; exact ⟨he, fun _ => hv hd0⟩
        · simp only [ite_eq_right hp]; exact ⟨he, fun hc => absurd hc (by simp)⟩

theorem MemCert.access {V : List String} (r₀ : String) : MemCert V (.access r₀) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [ite_eq_left hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [ite_eq_right hd]; exact ⟨he, fun _ => hv hd0⟩

/-- **Allocation.** The fresh address is added to `live` and stored in `x`, so `x`
    joins the tracked set — and every variable already tracked stays tracked, because
    `live` only grows. -/
theorem MemCert.alloc {V : List String} (x : String) :
    MemCert V (.memop .alloc x) (x :: V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [ite_eq_left hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [ite_eq_right hd]
        refine ⟨he, fun _ q hq => ?_⟩
        rcases List.mem_cons.mp hq with hqx | hqv
        · subst hqx
          show memInt (upd s.store q (pickAddr s.freed s.fresh) q)
              (pickAddr s.freed s.fresh :: s.live) = true
          simp [upd, memInt]
        · show memInt (upd s.store x (pickAddr s.freed s.fresh) q)
                (pickAddr s.freed s.fresh :: s.live) = true
          by_cases hqx : q = x
          · subst hqx; simp [upd, memInt]
          · simp only [upd, ite_eq_right hqx, memInt, Bool.or_eq_true]
            exact Or.inr (hv hd0 q hqv)

/-- **Secret allocation.** The same liveness argument: the label is not part of
    the separation invariant. The fresh address is added to `live` and stored in `x`, so `x`
    joins the tracked set — and every variable already tracked stays tracked, because
    `live` only grows. -/
theorem MemCert.allocS {V : List String} (x : String) :
    MemCert V (.memop .allocS x) (x :: V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [ite_eq_left hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [ite_eq_right hd]
        refine ⟨he, fun _ q hq => ?_⟩
        rcases List.mem_cons.mp hq with hqx | hqv
        · subst hqx
          show memInt (upd s.store q (pickAddr s.freed s.fresh) q)
              (pickAddr s.freed s.fresh :: s.live) = true
          simp [upd, memInt]
        · show memInt (upd s.store x (pickAddr s.freed s.fresh) q)
                (pickAddr s.freed s.fresh :: s.live) = true
          by_cases hqx : q = x
          · subst hqx; simp [upd, memInt]
          · simp only [upd, ite_eq_right hqx, memInt, Bool.or_eq_true]
            exact Or.inr (hv hd0 q hqv)

/-- **Dereference.** Tracked means live, so the fault branch is unreachable and `err`
    stays `false` — which is exactly the memory-safety guarantee. -/
theorem MemCert.deref {V : List String} (x : String) (hx : memStr x V = true) :
    MemCert V (.memop .deref x) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [ite_eq_left hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        have hlive : memInt (s.store x) s.live = true := hv hd0 x (memStr_mem hx)
        simp only [ite_eq_right hd, ite_eq_left hlive]
        exact ⟨he, fun _ => hv hd0⟩

/-! ## The checker -/

def umcheck : List String → UCmd → Option (List String)
  | V, .skip              => some V
  | V, .assign x _        => some (dropStr x V)
  | V, .check _           => some V
  | V, .access _          => some V
  | V, .memop .alloc x    => some (x :: V)
  | V, .memop .allocS x   => some (x :: V)
  | V, .memop .deref x    => if memStr x V then some V else none
  | _, .memop .free _     => none        -- no rule: see `free_has_no_rule`
  | _, .sop _ _ _         => none        -- strings do not touch the heap; stage 1o
  | _, .hop _ _ _         => none        -- stage 1v: see `SepCert.load`/`SepCert.store`
  | V, .seq c₁ c₂         => (umcheck V c₁).bind fun V₁ => umcheck V₁ c₂
  | V, .ite _ c₁ c₂       => match umcheck V c₁, umcheck V c₂ with
                             | some V₁, some V₂ => some (interStr V₁ V₂)
                             | _, _ => none
  | _, .loop _ _          => none

theorem umcheck_sound : ∀ (c : UCmd) (V V' : List String),
    umcheck V c = some V' → MemCert V c V'
  | .skip, V, V', h => by
      simp only [umcheck, Option.some.injEq] at h; subst h; exact MemCert.skip
  | .assign x e, V, V', h => by
      simp only [umcheck, Option.some.injEq] at h; subst h; exact MemCert.assign x e
  | .check r, V, V', h => by
      simp only [umcheck, Option.some.injEq] at h; subst h; exact MemCert.check r
  | .access r, V, V', h => by
      simp only [umcheck, Option.some.injEq] at h; subst h; exact MemCert.access r
  | .memop .alloc x, V, V', h => by
      simp only [umcheck, Option.some.injEq] at h; subst h; exact MemCert.alloc x
  | .memop .allocS x, V, V', h => by
      simp only [umcheck, Option.some.injEq] at h; subst h; exact MemCert.allocS x
  | .memop .deref x, V, V', h => by
      simp only [umcheck] at h
      by_cases hx : memStr x V = true
      · rw [ite_eq_left hx] at h
        simp only [Option.some.injEq] at h; subst h
        exact MemCert.deref x hx
      · rw [ite_eq_right hx] at h; simp at h
  | .memop .free _, _, _, h => by simp [umcheck] at h
  | .sop _ _ _, _, _, h => by simp [umcheck] at h
  | .hop _ _ _, _, _, h => by simp [umcheck] at h
  | .seq c₁ c₂, V, V', h => by
      simp only [umcheck] at h
      rcases e₁ : umcheck V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        exact MemCert.seq (umcheck_sound c₁ V V₁ e₁) (umcheck_sound c₂ V₁ V' h)
  | .ite e c₁ c₂, V, V', h => by
      simp only [umcheck] at h
      rcases e₁ : umcheck V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rcases e₂ : umcheck V c₂ with _ | V₂
        · rw [e₁, e₂] at h; simp at h
        · rw [e₁, e₂] at h
          simp only [Option.some.injEq] at h; subst h
          exact MemCert.ite (umcheck_sound c₁ V V₁ e₁) (umcheck_sound c₂ V V₂ e₂)
  | .loop _ _, _, _, h => by simp [umcheck] at h

/-! ## The guarantee, and a witness on each side -/

/-- **Memory safety.** A checked program never faults: started clean, its `err` flag
    is still `false` however it runs. -/
theorem umcheck_no_fault {c : UCmd} {V' : List String} (h : umcheck [] c = some V') :
    ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n c π (initU σ) = some r → r.1.err = false := by
  intro n π σ r hr
  have hinv : MemInv [] (initU σ) := ⟨rfl, by simp⟩
  exact ((umcheck_sound c [] V' h).safe n π (initU σ) r hinv hr).1

/-- The wild dereference — brick 11's class, CWE-119 — is rejected. -/
theorem wild_deref_rejected : umcheck [] (.memop .deref "p") = none := by decide

/-- And it really does fault when run: the check is not rejecting something harmless. -/
theorem wild_deref_faults :
    ((uexec 1 (.memop .deref "p") (fun _ => true) (initU (fun _ => 0))).map
      (fun r => r.1.err)) = some true := by decide

/-- Allocate first and it is accepted, and does not fault. -/
theorem alloc_then_deref_ok :
    umcheck [] (.seq (.memop .alloc "p") (.memop .deref "p")) = some ["p"]
  ∧ ((uexec 3 (.seq (.memop .alloc "p") (.memop .deref "p")) (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some false := by decide

/-- Overwriting the pointer drops it from the tracked set, so a later dereference is
    rejected — the analysis is not fooled by an intervening assignment. -/
theorem clobbered_pointer_rejected :
    umcheck [] (.seq (.memop .alloc "p")
                (.seq (.assign "p" (.num 99)) (.memop .deref "p"))) = none := by decide

/-- **`free` has no rule, and that is deliberate.** It is in the syntax and the
    semantics, so use-after-free is *expressible* — but dropping an address from
    `live` invalidates every alias of it, and soundness needs brick 12's linearity or
    brick 19's must-alias tracking carried in the invariant. Rejecting it is the
    conservative direction; claiming it would not be. -/
theorem free_has_no_rule (x : String) (V : List String) :
    umcheck V (.memop .free x) = none := rfl

end ConfTyping
