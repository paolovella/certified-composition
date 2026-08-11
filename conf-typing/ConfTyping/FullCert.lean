/-
  The composable core, stage 1n: one checker, four certificates — and the one law that
  does not compose over loops.

  Stages 1c–1e built a bundle carrying a **budget**, an **authorization set** and a
  **ledger**; stages 1h–1m built a joint judgment carrying **noninterference** and
  **memory safety**. They were separate artifacts: `ucheck` refused every heap
  operation (`| _, .memop _ _ => none`, added in stage 1h so that stage 1c's soundness
  proof did not have to change), and `jcheck` said nothing about cost or mediation. So
  no single program had ever carried all of them.

  `allcheck` does. One pass produces the authorization set, the tracked pointer set and
  the cost bound, and `allcheck_sound` turns that into a `FullCert` — a `UCert` and a
  `JSecTy` side by side. `fullProg` is the artifact the whole 1a–1n arc was for: a
  program that checks a permission, allocates, reads a mediated resource, dereferences,
  assigns and frees, carrying **four certificates** proved from one run of one checker,
  with a budget that is *tight* (certified 6, spends 6).

  This much is integration rather than discovery — stages 1c–1e already established
  that these laws do not interact, so putting them in one function was expected to
  work, and it did.

  **The part that is not integration.** Extending the budget to heap operations needed
  a new rule (`UCert.memop`), and writing it exposed an asymmetry that had been hiding
  behind two separate `none`s. Of the four certificates, three have loop rules:
  `JSecTy.whileW` (stage 1l), `SepCert.loop` (stage 1k), and mediation threads through
  a loop unchanged. The **budget does not**, and cannot: a cost bound over a loop
  requires an *iteration* bound, which is a termination argument rather than a typing
  side-condition. `only_the_budget_lacks_a_loop_rule` states the asymmetry as a
  theorem. It is not a gap to be closed by more of the same work — brick 30's
  `loopFix` and stage 1f's `countdown` are the two ways to supply the missing
  ingredient, and both are analyses of a different kind.

  So the honest summary of the composable core is: four certificates, one checker, on
  the loop-free fragment; and on loops, three of the four. (Stages 1o–1q added two more
  certificates, both initially without loop rules, and stage 1r gave them loop rules by
  narrowing — so the current figure is five of six, the budget still being the only law
  that cannot. `StringLoop.five_of_six_compose_over_loops` is the up-to-date statement;
  `only_the_budget_lacks_a_loop_rule` below stays true as written.)
-/
import ConfTyping.HeapAlloc

namespace ConfTyping

/-! ## The budget rule for heap operations -/

/-- **Heap operations cost one step and leave mediation alone.** Stage 1h gave `ucheck`
    a conservative `none` here so that stage 1c's soundness proof would not have to
    change; this is the rule it was standing in for. A fault sets `dead`, which makes
    the authorization obligation vacuous, so even the failing branches are fine. -/
theorem UCert.memop {A : List String} (op : MemOp) (x : String) :
    UCert A (.memop op x) A 1 := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; simp
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr
        subst hr
        obtain ⟨ha, hrd, hd⟩ := hinv
        by_cases hdead : s.dead = true
        · simp only [if_pos hdead]; exact ⟨ha, hrd, hd⟩
        · have hd0 : s.dead = false := by simpa using hdead
          simp only [if_neg hdead]
          cases op with
          | alloc => exact ⟨ha, hrd, fun _ => hd hd0⟩
          | allocS => exact ⟨ha, hrd, fun _ => hd hd0⟩
          | deref =>
              by_cases hl : memInt (s.store x) s.live = true
              · simp only [if_pos hl]; exact ⟨ha, hrd, hd⟩
              · simp only [if_neg hl]
                exact ⟨ha, hrd, fun hc => absurd hc (by simp)⟩
          | free =>
              by_cases hl : memInt (s.store x) s.live = true
              · simp only [if_pos hl]; exact ⟨ha, hrd, fun _ => hd hd0⟩
              · simp only [if_neg hl]
                exact ⟨ha, hrd, fun hc => absurd hc (by simp)⟩

/-- String operations cost one step and leave mediation alone, for the same reason
    heap operations do. -/
theorem UCert.sop {A : List String} (op : SOp) (x : String) (e : SExpr) :
    UCert A (.sop op x e) A 1 := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; simp
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr
        subst hr
        obtain ⟨ha, hrd, hd⟩ := hinv
        by_cases hdead : s.dead = true
        · simp only [if_pos hdead]; exact ⟨ha, hrd, hd⟩
        · have hd0 : s.dead = false := by simpa using hdead
          simp only [if_neg hdead]
          cases op with
          | set  => exact ⟨ha, hrd, fun _ => hd hd0⟩
          | emit => exact ⟨ha, hrd, fun _ => hd hd0⟩

/-- Heap value operations cost one step and leave mediation alone. -/
theorem UCert.hop {A : List String} (op : HOp) (x y : String) :
    UCert A (.hop op x y) A 1 := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; simp
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr
        subst hr
        obtain ⟨ha, hrd, hd⟩ := hinv
        by_cases hdead : s.dead = true
        · simp only [if_pos hdead]; exact ⟨ha, hrd, hd⟩
        · have hd0 : s.dead = false := by simpa using hdead
          simp only [if_neg hdead]
          cases op with
          | load =>
              by_cases hl : memInt (s.store y) s.live = true
              · simp only [if_pos hl]; exact ⟨ha, hrd, fun _ => hd hd0⟩
              · simp only [if_neg hl]; exact ⟨ha, hrd, fun hc => absurd hc (by simp)⟩
          | store =>
              by_cases hl : memInt (s.store x) s.live = true
              · simp only [if_pos hl]; exact ⟨ha, hrd, fun _ => hd hd0⟩
              · simp only [if_neg hl]; exact ⟨ha, hrd, fun hc => absurd hc (by simp)⟩

/-! ## The full certificate -/

/-- Everything the composable core knows about a command, in one place: a cost bound, a
    threaded authorization set, noninterference and memory safety. -/
structure FullCert (P : Partition) (A V : List String) (c : UCmd)
    (A' V' : List String) (k : Nat) : Prop where
  bundle : UCert A c A' k
  joint  : JSecTy P V c V'

/-! ## One checker -/

def allcheck (P : Partition) :
    List String → List String → UCmd → Option (List String × List String × Nat)
  | A, V, .skip           => some (A, V, 1)
  | A, V, .assign x e     => if P x || exprLow P e then some (A, dropStr x V, 1) else none
  | A, V, .check r        => some (r :: A, V, 1)
  | A, V, .access r       => if memStr r A then some (A, V, 1) else none
  | A, V, .memop .alloc x => if P x then none else some (A, x :: V, 1)
  | A, V, .memop .allocS x => if P x then some (A, x :: V, 1) else none
  | A, V, .memop .deref x => if memStr x V then some (A, V, 1) else none
  | A, V, .memop .free x  => if memStr x V && !P x then some (A, dropStr x V, 1) else none
  | A, V, .sop .set x e   => if P x || sexprLow P e then some (A, V, 1) else none
  | A, V, .sop .emit _ e  => if sexprLow P e then some (A, V, 1) else none
  | A, V, .hop .load d p  => if memStr p V && (!P p || P d)
                             then some (A, dropStr d V, 1) else none
  | A, V, .hop .store p v => if memStr p V && !P p && !P v then some (A, V, 1) else none
  | A, V, .seq c₁ c₂      => (allcheck P A V c₁).bind fun p₁ =>
                               (allcheck P p₁.1 p₁.2.1 c₂).map fun p₂ =>
                                 (p₂.1, p₂.2.1, p₁.2.2 + p₂.2.2)
  | A, V, .ite e c₁ c₂    => if exprLow P e then
                               match allcheck P A V c₁, allcheck P A V c₂ with
                               | some p₁, some p₂ =>
                                   some (interStr p₁.1 p₂.1, interStr p₁.2.1 p₂.2.1,
                                         1 + max p₁.2.2 p₂.2.2)
                               | _, _ => none
                             else none
  | _, _, .loop _ _       => none   -- see `only_the_budget_lacks_a_loop_rule`

theorem allcheck_sound {P : Partition} : ∀ (c : UCmd) (A V A' V' : List String) (k : Nat),
    allcheck P A V c = some (A', V', k) → FullCert P A V c A' V' k
  | .skip, A, V, A', V', k, h => by
      simp only [allcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨UCert.skip, .skip V⟩
  | .check r, A, V, A', V', k, h => by
      simp only [allcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨UCert.check r, .check V r⟩
  | .assign x e, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : (P x || exprLow P e) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨UCert.assign x e, ?_⟩
        rcases Bool.or_eq_true _ _ |>.mp hx with h' | h'
        · exact .assignH V x e h'
        · exact .assignL V x e h'
      · rw [if_neg hx] at h; simp at h
  | .access r, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hr : memStr r A = true
      · rw [if_pos hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨UCert.access r hr, .access V r⟩
      · rw [if_neg hr] at h; simp at h
  | .memop .alloc x, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : P x = true
      · rw [if_pos hx] at h; simp at h
      · rw [if_neg hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨UCert.memop .alloc x, .alloc V x (by simpa using hx)⟩
  | .memop .allocS x, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : P x = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨UCert.memop .allocS x, .allocS V x hx⟩
      · rw [if_neg hx] at h; simp at h
  | .memop .deref x, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : memStr x V = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨UCert.memop .deref x, .deref V x hx⟩
      · rw [if_neg hx] at h; simp at h
  | .memop .free x, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : (memStr x V && !P x) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hx
        exact ⟨UCert.memop .free x, .free V x h1 (by simpa using h2)⟩
      · rw [if_neg hx] at h; simp at h
  | .sop .set x e, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : (P x || sexprLow P e) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨UCert.sop .set x e, ?_⟩
        rcases Bool.or_eq_true _ _ |>.mp hx with h' | h'
        · exact .setH V x e h'
        · exact .setL V x e h'
      · rw [if_neg hx] at h; simp at h
  | .sop .emit q e, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : sexprLow P e = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨UCert.sop .emit q e, .emit V q e hx⟩
      · rw [if_neg hx] at h; simp at h
  | .seq c₁ c₂, A, V, A', V', k, h => by
      simp only [allcheck] at h
      rcases e₁ : allcheck P A V c₁ with _ | p₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        rcases e₂ : allcheck P p₁.1 p₁.2.1 c₂ with _ | p₂
        · rw [e₂] at h; simp at h
        · rw [e₂] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have f₁ := allcheck_sound c₁ A V p₁.1 p₁.2.1 p₁.2.2 (by rw [e₁])
          have f₂ := allcheck_sound c₂ p₁.1 p₁.2.1 p₂.1 p₂.2.1 p₂.2.2 (by rw [e₂])
          exact ⟨UCert.seq f₁.bundle f₂.bundle, .seq f₁.joint f₂.joint⟩
  | .ite e c₁ c₂, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hg : exprLow P e = true
      · rw [if_pos hg] at h
        rcases e₁ : allcheck P A V c₁ with _ | p₁
        · rw [e₁] at h; simp at h
        · rcases e₂ : allcheck P A V c₂ with _ | p₂
          · rw [e₁, e₂] at h; simp at h
          · rw [e₁, e₂] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have f₁ := allcheck_sound c₁ A V p₁.1 p₁.2.1 p₁.2.2 (by rw [e₁])
            have f₂ := allcheck_sound c₂ A V p₂.1 p₂.2.1 p₂.2.2 (by rw [e₂])
            exact ⟨UCert.ite f₁.bundle f₂.bundle, .iteL e hg f₁.joint f₂.joint⟩
      · rw [if_neg hg] at h; simp at h
  | .hop .load d p, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : (memStr p V && (!P p || P d)) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hx
        refine ⟨UCert.hop .load d p, ?_⟩
        rcases Bool.or_eq_true _ _ |>.mp h2 with h' | h'
        · exact .loadL V d p h1 (by simpa using h')
        · exact .loadH V d p h1 h'
      · rw [if_neg hx] at h; simp at h
  | .hop .store p v, A, V, A', V', k, h => by
      simp only [allcheck] at h
      by_cases hx : (memStr p V && !P p && !P v) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h12, h3⟩ := Bool.and_eq_true _ _ |>.mp hx
        obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h12
        exact ⟨UCert.hop .store p v, .storeL V p v h1 (by simpa using h2) (by simpa using h3)⟩
      · rw [if_neg hx] at h; simp at h
  | .loop _ _, _, _, _, _, _, h => by simp [allcheck] at h

/-! ## Four certificates from one run of one checker -/

/-- **The composable core's deliverable.** From `allcheck` alone: a cost bound, every
    read authorized, noninterference (hence timing and termination too, since the clock
    and the halting bit are in the observation), and no memory fault. -/
theorem allcheck_gives_four {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : allcheck P [] [] c = some (A', V', k)) :
    -- the budget
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n c π s = some r → r.2.1 ≤ k)
    -- mediation: every resource read was permitted
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
    -- noninterference
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
    -- memory safety
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false) := by
  have hf := allcheck_sound c [] [] A' V' k h
  refine ⟨hf.bundle.budget, ?_, fun n π σ σ' hσ => ?_, fun n π σ r hr => ?_⟩
  · intro n π σ r hr q hq
    have hinv : UMedInv π [] (initU σ) := ⟨by simp [initU], by simp [initU], by simp⟩
    exact (hf.bundle.auth n π (initU σ) r hinv hr).2.1 q hq
  · exact uOptLowEqA.toLowEq (jsecTy_sound n c [] V' hf.joint π (initU σ) (initU σ')
      SepInv.initU SepInv.initU ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩)
  · exact (hf.joint.toSepCert.safe n π (initU σ) r SepInv.initU hr).1

/-! ## The artifact -/

/-- Check a permission, allocate a buffer, read the mediated resource, use the buffer,
    do some work, release the buffer. Six steps, four certificates. -/
def fullProg : UCmd :=
  .seq (.check "db")
   (.seq (.memop .alloc "buf")
    (.seq (.access "db")
     (.seq (.memop .deref "buf")
      (.seq (.assign "n" (.num 1)) (.memop .free "buf")))))

theorem fullProg_checks : allcheck Psec [] [] fullProg = some (["db"], [], 6) := by decide

/-- **One program, four certificates, one checker.** -/
theorem fullProg_four :
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n fullProg π s = some r → r.2.1 ≤ 6)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fullProg π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n fullProg π (initU σ)) (uexec n fullProg π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fullProg π (initU σ) = some r → r.1.err = false) :=
  allcheck_gives_four fullProg_checks

/-- And the budget is **tight**: certified six, spends six. The bound is the real cost,
    not a safe over-estimate — and the run reads exactly the mediated resource, faults
    nowhere, and leaves no allocation live. -/
theorem fullProg_runs :
    ((uexec 13 fullProg (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.err, r.1.dead, r.1.reads, r.1.live, r.2.1)))
      = some (false, false, ["db"], [], 6) := by decide

/-- Drop the permission check and the same program is refused — the mediation
    certificate is doing work, not decorating. -/
theorem fullProg_needs_its_check :
    allcheck Psec [] []
      (.seq (.memop .alloc "buf") (.seq (.access "db") (.memop .free "buf"))) = none := by
  decide

/-! ## The asymmetry the merge exposed -/

/-- **Three of the four laws compose over loops; the budget does not.**
    Noninterference has `JSecTy.whileW`, memory safety has `SepCert.loop`, and
    mediation threads through unchanged — but a cost bound over a loop needs an
    *iteration* bound, which is a termination argument and not a typing side-condition.
    This is not a gap to close with more of the same work: brick 30's `loopFix` and
    stage 1f's `countdown` are the two ways to supply the missing ingredient, and both
    are analyses of a different kind. Behind two separate `none`s this asymmetry was
    invisible; merging the checkers is what made it a statement. -/
theorem only_the_budget_lacks_a_loop_rule :
    (∀ (P : Partition) (V : List String) (e : Expr) (c : UCmd), exprLow P e = true →
        JSecTy P V c V → JSecTy P V (.loop e c) V)
  ∧ (∀ (V : List String) (e : Expr) (c : UCmd), SepCert V c V → SepCert V (.loop e c) V)
  ∧ (∀ (P : Partition) (A V : List String) (e : Expr) (c : UCmd),
        allcheck P A V (.loop e c) = none) :=
  ⟨fun _ _ e _ hg hc => .whileW e hg (fun _ hx => hx) hc (fun _ hx => hx),
   fun _ _ _ h => SepCert.loop h,
   fun _ _ _ _ _ => rfl⟩

/-- The other three really are available on a loop, and `jcheckW` decides them: the
    widened checker accepts `widenProg`, which `allcheck` cannot cost. So the split is
    between *which* certificates a loop can carry, not between programs. -/
theorem loops_carry_three_of_four :
    jcheckW Pheap 10 [] widenProg = some ["p"]
  ∧ allcheck Pheap [] [] widenProg = none := by decide

end ConfTyping
