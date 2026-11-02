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
  intro n i i' _ _ h
  show (⟨_, _, _, _⟩ : Beh) = ⟨_, _, _, _⟩
  simp only [toy] at h ⊢
  simp [h]

theorem toy_rel_fails : ¬ Cert.rel toy true := by
  intro h
  have := h 0 (0, 0) (0, 1) trivial trivial rfl
  simp [toy] at this

/-! ## `bound` -/

theorem toy_bound_holds : Cert.bound toy 3 false := by
  intro n i _; simp [toy]

theorem toy_bound_fails : ¬ Cert.bound toy 3 true := by
  intro h
  have := h 0 (0, 4) trivial
  simp [toy] at this

/-! ## `trace` -/

theorem toy_trace_holds : Cert.trace toy (fun evs => ∀ e ∈ evs, e = .read "r") true := by
  intro n i _ e he; simpa [toy] using he

theorem toy_trace_fails : ¬ Cert.trace toy (fun evs => evs = []) true := by
  intro h
  have := h 0 (0, 0) trivial
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

def padPass : PassCert toy toyPad :=
  PassCert.ofSim (fun p => .ok (p, padX)) (fun i => i) (fun _ _ => trivial)
    (fun u _ => ⟨u, trivial, rfl⟩) (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩)
    (fun _ _ _ h _ _ => by cases h; rfl)
    (fun _ _ _ h n => by cases h; exact ⟨n, rfl⟩)

/-- **The transfers, exercised.** `false`'s three certificates arrive on the padded program
    as certificates of `toyPad` itself, on every admissible input (F3), with no proof about
    the pad; the budget arrives transformed (3 + 1). -/
theorem padPass_carries :
    Cert.rel toyPad false
  ∧ Cert.bound toyPad 4 false
  ∧ Cert.trace toyPad (fun evs => ∀ e ∈ evs, e = .read "r") true :=
  ⟨padPass.rel_transfer (p' := false) (t := padX) rfl toy_rel_holds,
   padPass.bound_transfer (p' := false) (t := padX) rfl toy_bound_holds,
   padPass.trace_transfer (p' := true) (t := padX) rfl
     (fun _ _ hab hb e he => hb e (hab.subset he)) toy_trace_holds⟩

/-- And the transfer is not vacuous: `true`, which is not `rel`, stays distinguishable after
    the pass. -/
theorem padPass_keeps_the_leak :
    toyPad.run 0 true (padPass.enc (0, 0)) ≠ toyPad.run 0 true (padPass.enc (0, 1)) := by
  simp [toyPad, toy, padPass, PassCert.ofSim]

/-- The identity pass on the padded language: composing with it must change nothing. -/
def idPad : PassCert toyPad toyPad :=
  PassCert.ofSim (fun p => .ok (p, Xform.id)) (fun i => i) (fun _ _ => trivial)
    (fun u _ => ⟨u, trivial, rfl⟩) (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩)
    (fun _ _ _ h _ _ => by cases h; rfl)
    (fun _ _ _ h n => by cases h; exact ⟨n, rfl⟩)

/-- **Composition, exercised.** The two-pass pipeline is itself a `PassCert`, and the budget
    arrives through both cost transformers. -/
theorem seq_carries_bound : Cert.bound toyPad 4 false :=
  (padPass.seq idPad).bound_transfer (p' := false) (t := padX.then Xform.id) rfl toy_bound_holds

/-- **Composition at the certificate level** (F3). The padded program's certificate, which
    `padPass` produced, is an ordinary certificate of `toyPad`, so the next pass takes it as
    its source certificate directly, with no `seq`. -/
theorem chained_carries_bound : Cert.bound toyPad 4 false :=
  idPad.bound_transfer (p := false) (p' := false) (t := Xform.id) rfl
    (padPass.bound_transfer (p' := false) (t := padX) rfl toy_bound_holds)

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

def padPass2 : PassCert toyPad toyPad2 :=
  PassCert.ofSim (fun p => .ok (p, padX)) (fun i => i) (fun _ _ => trivial)
    (fun u _ => ⟨u, trivial, rfl⟩) (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩)
    (fun _ _ _ h _ _ => by cases h; rfl)
    (fun _ _ _ h n => by cases h; exact ⟨n, rfl⟩)

/-- **A three-pass pipeline's budget, computed by the kernel.** Compiling `false` through
    pad, identity, pad yields the transformers in one pass over the stages, and its cost
    transformer sends the source budget 3 to 5. -/
theorem seq3_budget :
    (((padPass.seq idPad).seq padPass2).comp false).map (fun r => r.2.cost 3) = .ok 5 := rfl

/-- The same budget, carried by `bound_transfer` through all three passes. -/
theorem seq3_carries_bound : Cert.bound toyPad2 5 false :=
  ((padPass.seq idPad).seq padPass2).bound_transfer (p' := false)
    (t := (padX.then Xform.id).then padX) rfl toy_bound_holds

/-- A pass that refuses: `seq` propagates the refusal, so nothing is certified. -/
def refuseComp : Bool → Except String (Bool × Xform)
  | true  => .error "refused"
  | false => .ok (false, Xform.id)

def refuseTrue : PassCert toyPad toyPad :=
  PassCert.ofSim refuseComp (fun i => i) (fun _ _ => trivial)
    (fun u _ => ⟨u, trivial, rfl⟩) (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩)
    (fun p _ _ h _ _ => by cases p <;> simp [refuseComp] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    (fun p _ _ h n => by cases p <;> simp [refuseComp] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨n, rfl⟩)

theorem seq_refusal_propagates :
    ((padPass.seq refuseTrue).comp true).toOption = none := rfl

/-! ## Progress (F4): a pass must finish what its source finishes -/

/-- A target language in which nothing ever runs: every run is the empty, out-of-fuel record.
    Every prefix-closed safety certificate holds of its programs vacuously. -/
def idleL : Lang where
  Prog  := Unit
  In    := Nat × Nat
  lowIn i i' := i.1 = i'.1
  run _ _ _ := { ev := [], lk := [], cost := 0, out := .fuel }

/-- Its programs satisfy any safety property the empty trace satisfies, and every budget. -/
theorem idle_safe (Φ : List Ev → Prop) (h : Φ []) : Cert.trace idleL Φ () ∧ Cert.bound idleL 0 () :=
  ⟨fun _ _ _ => h, fun _ _ _ => Nat.le_refl 0⟩

/-- **But no pass into it is certified**: `toy`'s programs finish, the idle target never does,
    so `progress` fails for any program the pass compiles. A compiler emitting a loop that does
    nothing cannot inherit certificates. -/
theorem no_idle_pass (pc : PassCert toy idleL) {p' : Unit} {t : Xform}
    (h : pc.comp false = .ok (p', t)) : False := by
  obtain ⟨m, ho, _⟩ := pc.progress false p' t h 0 (0, 0) trivial (by simp [toy])
  simp [idleL, toy] at ho

/-! ## Liveness (`Cert.live`) -/

/-- "The run eventually emits `x`", a property of the run's limit. -/
def eventually (x : Ev) (r : Chain) : Prop := ∃ n, x ∈ (r n).ev

theorem eventually_inv (x : Ev) : LimitInv (eventually x) := by
  intro r r' h ⟨n, hn⟩
  obtain ⟨m, hm⟩ := h.1 n
  exact ⟨m, hm.subset hn⟩

/-- "The run keeps producing events": a property only an infinite run can have when its
    finished runs are bounded, and no `trace` certificate can state. -/
def unbounded (r : Chain) : Prop := ∀ k, ∃ n, k ≤ (r n).ev.length

theorem unbounded_inv : LimitInv unbounded := by
  intro r r' h hu k
  obtain ⟨n, hn⟩ := hu k
  obtain ⟨m, hm⟩ := h.1 n
  exact ⟨m, Nat.le_trans hn hm.length_le⟩

/-- The toy's `true` eventually reads `r`. -/
theorem toy_live : Cert.live toy (eventually (.read "r")) true :=
  fun _ _ => ⟨0, by simp [toy]⟩

/-- **Liveness, carried through a pass**: the padded program eventually reads `r` too. -/
theorem padPass_carries_live : Cert.live toyPad (eventually (.read "r")) true :=
  padPass.live_transfer (p' := true) (t := padX) rfl (eventually_inv _) toy_live

/-- A program that never finishes and ticks once per unit of fuel. -/
def tickL : Lang where
  Prog  := Unit
  In    := Unit
  lowIn _ _ := True
  run n _ _ := { ev := List.replicate n (.emit "tick" []), lk := [], cost := n, out := .fuel }

/-- **An infinite run's liveness**: it keeps producing events. -/
theorem tick_unbounded : Cert.live tickL unbounded () :=
  fun _ _ k => ⟨k, by simp [tickL]⟩

/-- **Liveness is not trivial**: nothing ever happens in the idle language. -/
theorem idle_not_live : ¬ Cert.live idleL (eventually (.read "r")) () := by
  intro h
  obtain ⟨n, hn⟩ := h (0, 0) trivial
  simp [idleL] at hn

/-- A target that ticks once and then stalls forever. -/
def stallL : Lang where
  Prog  := Unit
  In    := Unit
  lowIn _ _ := True
  run n _ _ := { ev := List.replicate (min n 1) (.emit "tick" []), lk := [], cost := n,
                 out := .fuel }

/-- **Catch-up refuses a stalling compiler.** Its events are prefixes of the source's, and
    neither run ever finishes, so `ev_sim`, `progress` and `reflect` cannot object; only
    catch-up does. Without it, "keeps producing events" would be lost in compilation. -/
theorem no_stall_pass (pc : PassCert tickL stallL) {p' : Unit} {t : Xform}
    (h : pc.comp () = .ok (p', t)) : False := by
  obtain ⟨m, hm⟩ := pc.catch_up () p' t h 2 () trivial
  have := hm.length_le
  simp [tickL, stallL] at this
  omega

/-! ## The relational shape (`Cert.hyper`) -/

/-- "Both runs eventually show the same events." -/
def sameEvents (r r' : Chain) : Prop := ∀ l, (∃ n, l <+: (r n).ev) ↔ (∃ n, l <+: (r' n).ev)

theorem sameEvents_inv : LimitInv2 sameEvents := by
  intro r₁ r₂ r₁' r₂' h₁ h₂ h l
  constructor
  · intro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := h₁.2.1 n
    obtain ⟨k, hk⟩ := (h l).mp ⟨m, prefix_trans' hn hm⟩
    obtain ⟨j, hj⟩ := h₂.1 k
    exact ⟨j, prefix_trans' hk hj⟩
  · intro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := h₂.2.1 n
    obtain ⟨k, hk⟩ := (h l).mpr ⟨m, prefix_trans' hn hm⟩
    obtain ⟨j, hj⟩ := h₁.1 k
    exact ⟨j, prefix_trans' hk hj⟩

/-- A toy that emits: program `false` emits the public part, program `true` the secret. -/
def toyEmit : Lang where
  Prog  := Bool
  In    := Nat × Nat
  lowIn i i' := i.1 = i'.1
  run _ p i := { ev := [.emit "out" [if p then i.2 else i.1]], lk := [], cost := 1, out := .done }

/-- **Holds**: for publicly equal inputs, `false` shows the same events. -/
theorem emit_hyper_holds : Cert.hyper toyEmit (fun i i' => i.1 = i'.1) sameEvents false := by
  intro i i' _ _ h l
  simp only [toyEmit, Bool.false_eq_true, ↓reduceIte, h]

/-- **Fails**: `true` emits the secret, so publicly equal inputs can show different events. -/
theorem emit_hyper_fails : ¬ Cert.hyper toyEmit (fun i i' => i.1 = i'.1) sameEvents true := by
  intro h
  obtain ⟨n, hn⟩ := (h (0, 0) (0, 1) trivial trivial rfl [.emit "out" [0]]).mp
    ⟨0, prefix_refl' _⟩
  have := hn.eq_of_length (by simp [toyEmit])
  simp [toyEmit] at this

/-- The identity pass on `toyEmit`. -/
def idEmit : PassCert toyEmit toyEmit :=
  PassCert.ofSim (fun p => .ok (p, Xform.id)) (fun i => i) (fun _ _ => trivial)
    (fun u _ => ⟨u, trivial, rfl⟩) (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩)
    (fun _ _ _ h _ _ => by cases h; rfl)
    (fun _ _ _ h n => by cases h; exact ⟨n, rfl⟩)

/-- **The relational shape, carried through a pass.** -/
theorem idEmit_carries_hyper : Cert.hyper toyEmit (fun i i' => i.1 = i'.1) sameEvents false :=
  idEmit.hyper_transfer (p := false) (p' := false) (t := Xform.id) rfl sameEvents_inv
    (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩) emit_hyper_holds

/-! ## One observer's view (`Cert.relView`): two tenants, side channels included -/

/-- An observer cannot tell payloads apart: its choice depends only on the channel. -/
theorem observer_blind_to_data (f : Observer) (s : String) (d d' : List Nat) :
    f (Ev.emit s d).chan = f (Ev.emit s d').chan := rfl

/-- Three programs over A's data (`i.1`) and B's data (`i.2`). `clean` writes each tenant's data to
    its own channel. `timing` does too, and also branches on A's data. `crossed` writes A's data
    to B's channel. -/
inductive TenantProg where
  | clean | timing | crossed

/-- Two tenants, each with a channel. -/
def tenants : Lang where
  Prog  := TenantProg
  In    := Nat × Nat
  lowIn i i' := i = i'
  run _ p i :=
    match p with
    | .clean   => { ev := [.emit "a" [i.1], .emit "b" [i.2]], lk := [], cost := 2, out := .done }
    | .timing  => { ev := [.emit "a" [i.1], .emit "b" [i.2]], lk := [.branch (i.1 == 0)],
                    cost := 2, out := .done }
    | .crossed => { ev := [.emit "a" [i.1], .emit "b" [i.1]], lk := [], cost := 2, out := .done }

/-- Inputs that differ at most in A's data. -/
def sameB (i i' : Nat × Nat) : Prop := i.2 = i'.2

/-- B's observer: its own channel. -/
def obsB : Observer
  | .emit "b" => true
  | _ => false

/-- **Holds**: `clean` shows B nothing of A. -/
theorem clean_view_holds : Cert.relView tenants sameB obsB .clean := by
  intro _ i i' _ _ h
  cases i; cases i'; cases h; rfl

/-- **The all-channels observer fails on the same program**: A's own output depends on A's data,
    so isolation is not the whole-observation comparison `rel` makes. -/
theorem clean_view_all_fails : ¬ Cert.relView tenants sameB Observer.all .clean := by
  intro h
  have := congrArg Beh.ev (h 0 (0, 0) (1, 0) trivial trivial rfl)
  simp [tenants, Beh.view_all] at this

/-- "B's outputs are the same", at every fuel, with nothing about leakage or cost. -/
def sameBOutputs (r r' : Chain) : Prop :=
  ∀ n, ((r n).view obsB).ev = ((r' n).view obsB).ev

/-- **The outputs-only comparison passes `timing`**: B's outputs never depend on A's data. -/
theorem timing_outputs_pass : Cert.hyper tenants sameB sameBOutputs .timing := by
  intro i i' _ _ h _
  cases i; cases i'; cases h; rfl

/-- **B's view refuses it**: the branch on A's data shows, which is the side channel this shape
    adds. -/
theorem timing_view_fails : ¬ Cert.relView tenants sameB obsB .timing := by
  intro h
  have := congrArg Beh.lk (h 0 (0, 0) (1, 0) trivial trivial rfl)
  simp [tenants, Beh.view] at this

/-- **B's view refuses a plain leak too**: A's data on B's channel. -/
theorem crossed_view_fails : ¬ Cert.relView tenants sameB obsB .crossed := by
  intro h
  have := congrArg Beh.ev (h 0 (0, 0) (1, 0) trivial trivial rfl)
  simp [tenants, Beh.view, obsB, Ev.chan] at this

/-- The identity pass on `tenants`. -/
def idTenants : PassCert tenants tenants :=
  PassCert.ofSim (fun p => .ok (p, Xform.id)) (fun i => i) (fun _ _ => trivial)
    (fun u _ => ⟨u, trivial, rfl⟩) (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩)
    (fun _ _ _ h _ _ => by cases h; rfl)
    (fun _ _ _ h n => by cases h; exact ⟨n, rfl⟩)

/-- **The view, carried through a pass.** -/
theorem idTenants_carries_view : Cert.relView tenants sameB obsB .clean :=
  idTenants.relView_transfer (p := .clean) (p' := .clean) (t := Xform.id) rfl
    (fun u u' _ _ h => ⟨u, u', trivial, trivial, h, rfl, rfl⟩) clean_view_holds

/-! ## Coverage (F3): a pass must reach every admissible target input -/

/-- A target with an extra flag. With the flag off it runs as `toy`; with the flag on,
    program `false` branches on the secret. -/
def leakyT : Lang where
  Prog  := Bool
  In    := Nat × Nat × Bool
  lowIn i i' := i.1 = i'.1 ∧ i.2.2 = i'.2.2
  run _ p i :=
    { ev   := [.read "r"]
      lk   := [.branch (if p || i.2.2 then i.2.1 != 0 else i.1 != 0)]
      cost := if p then i.2.1 else 3
      out  := .done }

/-- An encoder that never sets the flag. -/
def leakyEnc (i : Nat × Nat) : Nat × Nat × Bool := (i.1, i.2, false)

/-- **The old transfer's conclusion holds, and says nothing.** On the encodings, `false`'s
    runs are indistinguishable, exactly what `rel_transfer` concluded before F3. -/
theorem leaky_rel_on_encodings : ∀ m i i', toy.lowIn i i' →
    leakyT.run m false (leakyEnc i) = leakyT.run m false (leakyEnc i') := by
  intro m i i' h
  show (⟨_, _, _, _⟩ : Beh) = ⟨_, _, _, _⟩
  simp only [leakyEnc, toy] at h ⊢
  simp [h]

/-- **But the compiled program leaks** on an admissible target input no source input encodes
    to: flag on, secrets 0 and 1. -/
theorem leaky_not_rel : ¬ Cert.rel leakyT false := by
  intro h
  have := h 0 (0, 0, true) (0, 1, true) trivial trivial ⟨rfl, rfl⟩
  simp [leakyT] at this

/-- **And the pass cannot be certified**: the encoder misses the flagged inputs, so `cover`
    fails, and no `PassCert toy leakyT` with this encoder exists. -/
theorem leaky_misses : ¬ ∀ u, leakyT.Adm u → ∃ i, toy.Adm i ∧ leakyEnc i = u := by
  intro h
  obtain ⟨i, _, hi⟩ := h (0, 0, true) trivial
  simp [leakyEnc] at hi

theorem no_leaky_pass (pc : PassCert toy leakyT) (he : pc.enc = leakyEnc) : False :=
  leaky_misses (fun u hu => by obtain ⟨i, hi, h⟩ := pc.cover u hu; exact ⟨i, hi, he ▸ h⟩)

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
