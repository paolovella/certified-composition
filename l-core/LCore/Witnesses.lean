/-
  Witnesses for the kernel (PH1 steps 1–4). Every certificate shape is shown inhabited *and*
  refuted, on a toy language, so none of the definitions is vacuous. A transfer is exercised
  through a pass that really changes the leakage and the cost (CLAUDE.md: every rule has an
  accepted and a refused witness). Not Ring 0: this file only uses the kernel.
-/
import LCore.Kernel.Pass

namespace LCore.Witness

/-- A toy language. An input is (public, secret). Program `true` branches and spends on the
    secret; program `false` only looks at the public part. -/
def toy : Lang where
  Prog  := Bool
  In    := Nat × Nat
  lowIn i i' := i.1 = i'.1
  run _ p i :=
    { ev   := [.read "r"]
      lk   := [.branch (if p then i.2 != 0 else i.1 != 0)]
      cost := if p then i.2 else 3
      out  := .done }

/-! ## `rel` -/

theorem toy_rel_holds : Cert.rel toy false := by
  intro n i i' h
  show (⟨_, _, _, _⟩ : Beh) = ⟨_, _, _, _⟩
  simp only [toy] at h ⊢
  simp [h]

theorem toy_rel_fails : ¬ Cert.rel toy true := by
  intro h
  have := h 0 (0, 0) (0, 1) rfl
  simp [toy] at this

/-! ## `bound` -/

theorem toy_bound_holds : Cert.bound toy 3 false := by
  intro n i; simp [toy]

theorem toy_bound_fails : ¬ Cert.bound toy 3 true := by
  intro h
  have := h 0 (0, 4)
  simp [toy] at this

/-! ## `trace` -/

theorem toy_trace_holds : Cert.trace toy (fun evs => ∀ e ∈ evs, e = .read "r") true := by
  intro n i e he; simpa [toy] using he

theorem toy_trace_fails : ¬ Cert.trace toy (fun evs => evs = []) true := by
  intro h
  have := h 0 (0, 0)
  simp [toy] at this

/-! ## A pass that changes leakage and cost -/

/-- The target: the same programs, run with one extra (public) bounds-check branch and one
    extra unit of cost, the shape of a pass that inserts a check. -/
def toyPad : Lang where
  Prog  := Bool
  In    := Nat × Nat
  lowIn i i' := i.1 = i'.1
  run n p i :=
    { ev   := (toy.run n p i).ev
      lk   := .branch true :: (toy.run n p i).lk
      cost := (toy.run n p i).cost + 1
      out  := (toy.run n p i).out }

/-- The pad's transformers: one public branch in front, one unit of cost more. -/
def padX : Xform where
  lk l := .branch true :: l
  cost c := c + 1
  fuel m := m
  costMono _ _ h := Nat.add_le_add_right h 1

def padPass : PassCert toy toyPad where
  comp p := .ok (p, padX)
  enc i := i
  sim p p' t h m i := by cases h; rfl

/-- **The transfers, exercised.** `false`'s three certificates arrive on the padded program
    with no proof about the pad itself; the budget arrives transformed (3 + 1). -/
theorem padPass_carries :
    (∀ m i i', toy.lowIn i i' → toyPad.run m false (padPass.enc i) = toyPad.run m false (padPass.enc i'))
  ∧ (∀ m i, (toyPad.run m false (padPass.enc i)).cost ≤ 4)
  ∧ (∀ m i, ∀ e ∈ (toyPad.run m true (padPass.enc i)).ev, e = .read "r") :=
  ⟨padPass.rel_transfer (p' := false) (t := padX) rfl toy_rel_holds,
   padPass.bound_transfer (p' := false) (t := padX) rfl toy_bound_holds,
   padPass.trace_transfer (p' := true) (t := padX) rfl toy_trace_holds⟩

/-- And the transfer is not vacuous: `true`, which is not `rel`, stays distinguishable after
    the pass. -/
theorem padPass_keeps_the_leak :
    toyPad.run 0 true (padPass.enc (0, 0)) ≠ toyPad.run 0 true (padPass.enc (0, 1)) := by
  simp [toyPad, toy, padPass]

/-- The identity pass on the padded language: composing with it must change nothing. -/
def idPad : PassCert toyPad toyPad where
  comp p := .ok (p, Xform.id)
  enc i := i
  sim p p' t h m i := by cases h; rfl

/-- **Composition, exercised.** The two-pass pipeline is itself a `PassCert`, and the budget
    arrives through both cost transformers. -/
theorem seq_carries_bound :
    ∀ m i, (toyPad.run m false ((padPass.seq idPad).enc i)).cost ≤ 4 :=
  (padPass.seq idPad).bound_transfer (p' := false) (t := padX.then Xform.id) rfl toy_bound_holds

/-- Two pads in a row: the target language with two extra branches and two extra units. -/
def toyPad2 : Lang where
  Prog  := Bool
  In    := Nat × Nat
  lowIn i i' := i.1 = i'.1
  run n p i :=
    { ev   := (toyPad.run n p i).ev
      lk   := .branch true :: (toyPad.run n p i).lk
      cost := (toyPad.run n p i).cost + 1
      out  := (toyPad.run n p i).out }

def padPass2 : PassCert toyPad toyPad2 where
  comp p := .ok (p, padX)
  enc i := i
  sim p p' t h m i := by cases h; rfl

/-- **A three-pass pipeline's budget, computed by the kernel.** Compiling `false` through
    pad, identity, pad yields the transformers in one pass over the stages, and its cost
    transformer sends the source budget 3 to 5. -/
theorem seq3_budget :
    (((padPass.seq idPad).seq padPass2).comp false).map (fun r => r.2.cost 3) = .ok 5 := rfl

/-- The same budget, carried by `bound_transfer` through all three passes. -/
theorem seq3_carries_bound :
    ∀ m i, (toyPad2.run m false (((padPass.seq idPad).seq padPass2).enc i)).cost ≤ 5 :=
  ((padPass.seq idPad).seq padPass2).bound_transfer (p' := false)
    (t := (padX.then Xform.id).then padX) rfl toy_bound_holds

/-- A pass that refuses: `seq` propagates the refusal, so nothing is certified. -/
def refuseTrue : PassCert toyPad toyPad where
  comp
    | true  => .error "refused"
    | false => .ok (false, Xform.id)
  enc i := i
  sim p p' t h m i := by
    cases p
    · cases h; rfl
    · cases h

theorem seq_refusal_propagates :
    ((padPass.seq refuseTrue).comp true).toOption = none := rfl

/-! ## Lawful languages (F2) -/

/-- Lawful: the toy runs to completion at every fuel. -/
def toyL : Lang where
  Prog := Bool
  In := Nat
  lowIn _ _ := True
  run _ p i := { ev := [.read "r"], lk := [.branch p], cost := i, out := .done }

theorem toyL_lawful : toyL.Lawful where
  ev_mono _ _ _ _ _ := List.prefix_refl _
  lk_mono _ _ _ _ _ := List.prefix_refl _
  cost_mono _ _ _ _ _ := Nat.le_refl _
  stable _ _ _ _ _ _ := rfl
  diverge _ := ⟨0, fun _ _ h => by cases h⟩

/-- The empty language: every run is the empty, out-of-fuel record (what `ucmdLang` reports
    for a run that never returns). Not lawful: it never pays for its fuel. -/
def emptyL : Lang where
  Prog := Unit
  In := Unit
  lowIn _ _ := True
  run _ _ _ := { ev := [], lk := [], cost := 0, out := .fuel }

theorem emptyL_unlawful : ¬ emptyL.Lawful := by
  intro h
  obtain ⟨d, hd⟩ := h.diverge ()
  have := hd (d + 1) () rfl
  simp [emptyL] at this; omega

/-- A language whose events grow in the middle (all reads, then all emits): not lawful. -/
def middleL : Lang where
  Prog := Unit
  In := Unit
  lowIn _ _ := True
  run n _ _ := { ev := List.replicate n (.read "r") ++ [.emit "out" []], lk := [], cost := n,
                 out := .fuel }

theorem middleL_unlawful : ¬ middleL.Lawful := by
  intro h
  have := h.ev_mono () () 0 1 (Nat.zero_le 1)
  simp [middleL] at this

end LCore.Witness
