/-
  The composable core, stage 1k: the joint judgment stage 1j's counterexample forced.

  Stage 1j proved that noninterference and memory safety do not factor on the heap: a
  `deref` leaks through the fault flag unless the pointer is known live, so the two
  properties cannot be certified separately and conjoined at the end. It also said
  exactly what to build instead — a judgment *indexed by the tracked set*, so the NI
  rule for `deref x` can demand `x ∈ V`. This is that judgment.

  `JSecTy P V c V'` is a four-place relation: from tracked set `V`, command `c` is both
  noninterferent at `P` and memory-safe, ending with tracked set `V'`. It has the union
  of the two rule sets, with the heap rules carrying the membership side-condition that
  neither system could state alone. `jcheck` decides it, and `jcheck_gives_both`
  extracts the two guarantees from one run of one checker.

  Two things are worth more than the construction.

  **`indexed_beats_the_conjunction`.** On `safeHeapProg` — allocate, dereference,
  mediate an access, free — the old checkers give nothing: `ucheckNI` rejects it
  outright, so the NI certificate is unavailable, while `slcheck` accepts it but says
  nothing about leaks. `jcheck` certifies both. So the indexed judgment is not a
  repackaging: it proves things the conjunction of its parts cannot, which is precisely
  the prediction stage 1j made from a counterexample.

  **`SepCert.loop`.** Getting here needed a loop rule for the memory certificate, which
  stages 1h and 1i both ducked (`umcheck` and `slcheck` return `none` at a loop). It is
  a fuel induction and the tracked set is simply the loop invariant. Adding it here
  rather than back-patching `MemLinear` keeps stage 1i's claims exactly as they were
  audited.

  Honest scope. The judgment covers everything `UCmd` has, but two of its rules stay
  conservative and both were argued for earlier: `allocL` is still absent (stage 1j's
  open question — it needs `fresh` in the observation), and a loop must preserve the
  tracked set exactly, so a loop that allocates without freeing is rejected. Neither is
  a soundness gap; both are places the analysis says "no" to a safe program.
-/
import ConfTyping.HeapNI

namespace ConfTyping

/-! ## The loop rule the memory certificate was missing -/

/-- **Loops preserve the memory invariant** when the body does, with the tracked set as
    the loop invariant. Stages 1h and 1i both stopped at `none` for loops; the joint
    judgment needs this, and it is a plain fuel induction. -/
theorem SepCert.loop {V : List String} {e : Expr} {c : UCmd} (h : SepCert V c V) :
    SepCert V (.loop e c) V := by
  constructor
  intro n
  induction n with
  | zero => intro π s r _ hr; simp [uexec] at hr
  | succ m ihm =>
      intro π s r hinv hr
      rw [uexec_loop_eq] at hr
      by_cases hg : evalE e s.store ≠ 0
      · rw [if_pos hg] at hr
        rcases e₁ : uexec m c π s with _ | r₁
        · rw [e₁] at hr; simp at hr
        · rw [e₁, Option.bind_some] at hr
          rcases e₂ : uexec m (.loop e c) π r₁.1 with _ | r₂
          · rw [e₂] at hr; simp at hr
          · rw [e₂] at hr
            simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            exact ihm π r₁.1 r₂ (h.safe m π s r₁ hinv e₁) e₂
      · rw [if_neg hg] at hr
        simp only [Option.some.injEq] at hr
        subst hr
        exact hinv

/-- Shrinking the tracked set weakens the postcondition, so it is always allowed. -/
theorem SepCert.weakenPost {V V₁ V' : List String} {c : UCmd} (h : SepCert V c V₁)
    (hsub : ∀ x ∈ V', x ∈ V₁) : SepCert V c V' :=
  ⟨fun n π s r hinv hr => SepInv.mono hsub (h.safe n π s r hinv hr)⟩

/-- And a *smaller* precondition is a weaker assumption on the input state, so it may
    be strengthened to any superset. -/
theorem SepCert.strengthenPre {V W V' : List String} {c : UCmd} (h : SepCert W c V')
    (hsub : ∀ x ∈ W, x ∈ V) : SepCert V c V' :=
  ⟨fun n π s r hinv hr => h.safe n π s r (SepInv.mono hsub hinv) hr⟩

/-! ## The indexed judgment -/

/-- **Noninterference and memory safety, in one judgment indexed by the tracked set.**
    The heap rules carry a membership side-condition that neither of the two separate
    systems could express: `USecTy` has no `V`, and `SepCert` has no `P`. -/
inductive JSecTy (P : Partition) : List String → UCmd → List String → Prop where
  | skip    : ∀ V, JSecTy P V .skip V
  | assignH : ∀ V x e, P x = true → JSecTy P V (.assign x e) (dropStr x V)
  | assignL : ∀ V x e, exprLow P e = true → JSecTy P V (.assign x e) (dropStr x V)
  | seq     : ∀ {V V₁ V₂ c₁ c₂}, JSecTy P V c₁ V₁ → JSecTy P V₁ c₂ V₂ →
              JSecTy P V (.seq c₁ c₂) V₂
  | iteL    : ∀ {V V₁ V₂ c₁ c₂} (e), exprLow P e = true →
              JSecTy P V c₁ V₁ → JSecTy P V c₂ V₂ →
              JSecTy P V (.ite e c₁ c₂) (interStr V₁ V₂)
  /-- **The widened loop rule** (stage 1l). The loop is analysed at an invariant `W`
      contained in the entry set, and the body need only *preserve* it — end with some
      `W₁ ⊇ W` rather than with `W` on the nose. Stage 1k's exact rule is the case
      `W = V`, `W₁ = V`. -/
  | whileW  : ∀ {V W W₁ c} (e), exprLow P e = true → (∀ x ∈ W, x ∈ V) →
              JSecTy P W c W₁ → (∀ x ∈ W, x ∈ W₁) →
              JSecTy P V (.loop e c) W
  | check   : ∀ V r, JSecTy P V (.check r) V
  | access  : ∀ V r, JSecTy P V (.access r) V
  /-- **Public allocation** (stage 1w gives it a side condition). The cell's label is
      fixed at the allocation site, so the site must agree with the pointer's level —
      otherwise `LabInv` is not inductive. Stage 1m removed a *secrecy* condition
      ("the target must be High"); this is a *consistency* one, and they are different
      in kind: 1m's was about whether the address leaks, this is about which cell you
      get. -/
  | alloc   : ∀ V x, P x = false → JSecTy P V (.memop .alloc x) (x :: V)
  /-- **Secret allocation.** -/
  | allocS  : ∀ V x, P x = true → JSecTy P V (.memop .allocS x) (x :: V)
  /-- **The rule that needed the index.** `deref` is noninterferent exactly when the
      pointer is known live, so the fault branch is unreachable. -/
  | deref   : ∀ V x, memStr x V = true → JSecTy P V (.memop .deref x) V
  /-- **Freeing needs a Low pointer** (stage 1u). With a *reusing* allocator the free
      list decides the next address handed out, so freeing a High pointer makes the two
      runs' allocators diverge and a later allocation into a Low variable publishes the
      difference. `freeing_a_secret_pointer_leaks` is the witness. Under the old
      non-reusing allocator this hypothesis was unnecessary. -/
  | free    : ∀ V x, memStr x V = true → P x = false →
              JSecTy P V (.memop .free x) (dropStr x V)
  /-- Writing a **High** string variable is invisible. -/
  | setH    : ∀ V x e, P x = true → JSecTy P V (.sop .set x e) V
  /-- Writing a Low string variable needs a Low value. -/
  | setL    : ∀ V x e, sexprLow P e = true → JSecTy P V (.sop .set x e) V
  /-- **Emitting is a Low output**, so the value must be Low. Stage 1o left the sink
      outside the observation, which made every `sop` trivially noninterferent and the
      guarantee weaker than it looked; stage 1p puts it in. -/
  | emit    : ∀ V q e, sexprLow P e = true → JSecTy P V (.sop .emit q e) V
  /-- **Loading through a Low pointer** yields a Low value, since the heap is public. -/
  | loadL   : ∀ V d p, memStr p V = true → P p = false →
              JSecTy P V (.hop .load d p) (dropStr d V)
  /-- Loading through a *High* pointer reads an address the adversary cannot predict,
      so the destination must be High. -/
  | loadH   : ∀ V d p, memStr p V = true → P d = true →
              JSecTy P V (.hop .load d p) (dropStr d V)
  /-- **Storing needs both operands Low** (stage 1v). The heap is in the observation,
      so a secret address *or* a secret value would make the two heaps differ. There is
      deliberately no High counterpart: see `HeapValue.storing_a_secret_is_refused`. -/
  | storeL  : ∀ V p v, memStr p V = true → P p = false → P v = false →
              JSecTy P V (.hop .store p v) V
  /-- **Storing a secret through a secret pointer** (stage 1x). `LabInv` says the cell
      is secret, so neither the address nor the value is observable. Stage 1v had no
      such rule and the heap was therefore public; this is what the invariant buys. -/
  | storeH  : ∀ V p v, memStr p V = true → P p = true →
              JSecTy P V (.hop .store p v) V

/-- Every joint derivation contains a memory-safety derivation. -/
theorem JSecTy.toSepCert {P : Partition} {V : List String} {c : UCmd} {V' : List String}
    (h : JSecTy P V c V') : SepCert V c V' := by
  induction h with
  | skip _ => exact SepCert.skip
  | assignH _ x e _ => exact SepCert.assign x e
  | assignL _ x e _ => exact SepCert.assign x e
  | seq _ _ ih₁ ih₂ => exact SepCert.seq ih₁ ih₂
  | iteL _ _ _ _ ih₁ ih₂ => exact SepCert.ite ih₁ ih₂
  | whileW _ _ hWV _ hWW₁ ih =>
      exact SepCert.strengthenPre (SepCert.loop (SepCert.weakenPost ih hWW₁)) hWV
  | check _ r => exact SepCert.check r
  | access _ r => exact SepCert.access r
  | alloc _ x _ => exact SepCert.alloc x
  | allocS _ x _ => exact SepCert.allocS x
  | deref _ x hx => exact SepCert.deref x hx
  | free _ x hx _ => exact SepCert.free x hx
  | setH _ x e _ => exact SepCert.sop .set x e
  | setL _ x e _ => exact SepCert.sop .set x e
  | emit _ q e _ => exact SepCert.sop .emit q e
  | loadL _ d p hp _ => exact SepCert.load d p hp
  | loadH _ d p hp _ => exact SepCert.load d p hp
  | storeL _ p v hp _ _ => exact SepCert.store p v hp
  | storeH _ p v hp _ => exact SepCert.store p v hp

/-! ## The invariant -/

/-- Every tracked pointer points at a cell of its own security level. -/
def LabInv (P : Partition) (V : List String) (s : UState) : Prop :=
  s.dead = false → ∀ x ∈ V, s.hlab (s.store x) = P x

theorem LabInv.mono {P : Partition} {V W : List String} {s : UState}
    (hsub : ∀ x ∈ W, x ∈ V) (h : LabInv P V s) : LabInv P W s :=
  fun hd x hx => h hd x (hsub x hx)

/-- The invariant carries whenever a step leaves the labels alone and leaves the store
    alone on the *surviving* tracked variables. Every rule but the two allocations. -/
theorem labInv_carry {P : Partition} {V V' : List String} {s t : UState}
    (hsub : ∀ x ∈ V', x ∈ V) (hst : ∀ x ∈ V', t.store x = s.store x)
    (hhl : t.hlab = s.hlab) (hdd : t.dead = false → s.dead = false)
    (h : LabInv P V s) : LabInv P V' t := by
  intro hdt x hx
  rw [hst x hx, hhl]
  exact h (hdd hdt) x (hsub x hx)

/-! ## Steps that leave the store and the labels alone -/

def LabStable (c : UCmd) : Prop :=
  ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    uexec n c π s = some r →
      (∀ x, r.1.store x = s.store x) ∧ r.1.hlab = s.hlab ∧
      (r.1.dead = false → s.dead = false)

theorem labStable_skip : LabStable .skip := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      exact ⟨fun _ => by simp, by simp, by simp⟩

theorem labStable_check (q : String) : LabStable (.check q) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hp : π q = true
        · simp only [if_pos hp]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hp]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labStable_access (q : String) : LabStable (.access q) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩

theorem labStable_sop (op : SOp) (x : String) (e : SExpr) : LabStable (.sop op x e) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        cases op with
        | set  => exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        | emit => exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩

theorem labStable_deref (x : String) : LabStable (.memop .deref x) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store x) s.live = true
        · simp only [if_pos hl]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hl]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labStable_free (x : String) : LabStable (.memop .free x) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store x) s.live = true
        · simp only [if_pos hl]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hl]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labStable_hstore (p v : String) : LabStable (.hop .store p v) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store p) s.live = true
        · simp only [if_pos hl]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hl]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labInv_of_stable {P : Partition} {V : List String} {c : UCmd}
    (hc : LabStable c) {n : Nat} {π : MedPolicy} {s : UState}
    {r : UState × Nat × List Bool} (hL : LabInv P V s) (hr : uexec n c π s = some r) :
    LabInv P V r.1 :=
  labInv_carry (s := s) (fun _ hx => hx) (fun x _ => (hc n π s r hr).1 x)
    (hc n π s r hr).2.1 (hc n π s r hr).2.2 hL

/-! ## The three steps that move the store -/

theorem labInv_assign {P : Partition} {V : List String} {x : String} {e : Expr}
    {n : Nat} {π : MedPolicy} {s : UState} {r : UState × Nat × List Bool}
    (hL : LabInv P V s) (hr : uexec n (.assign x e) π s = some r) :
    LabInv P (dropStr x V) r.1 := by
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]
        exact labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun _ _ => rfl) rfl id hL
      · simp only [if_neg hd]
        refine labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun y hy => ?_) rfl id hL
        show upd s.store x (evalE e s.store) y = s.store y
        simp only [upd, if_neg (dropStr_ne hy)]

theorem labInv_load {P : Partition} {V : List String} {d p : String}
    {n : Nat} {π : MedPolicy} {s : UState} {r : UState × Nat × List Bool}
    (hL : LabInv P V s) (hr : uexec n (.hop .load d p) π s = some r) :
    LabInv P (dropStr d V) r.1 := by
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]
        exact labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun _ _ => rfl) rfl id hL
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store p) s.live = true
        · simp only [if_pos hl]
          refine labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun y hy => ?_) rfl id hL
          show upd s.store d (s.heap (s.store p)) y = s.store y
          simp only [upd, if_neg (dropStr_ne hy)]
        · simp only [if_neg hl]
          intro hc; exact absurd hc (by simp)

/-- **The allocation case**, and the only one that needs the separation invariant: the
    new cell takes the label the rule demands, and every variable already tracked keeps
    its own, because the new address is not live and therefore not any of theirs. -/
theorem labInv_alloc {P : Partition} {V : List String} {x : String} {b : Bool}
    {n : Nat} {π : MedPolicy} {s : UState} {r : UState × Nat × List Bool}
    (hb : P x = b) (hS : SepInv V s) (hL : LabInv P V s)
    (hr : uexec n (.memop (if b then .allocS else .alloc) x) π s = some r) :
    LabInv P (x :: V) r.1 := by
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      by_cases hd : s.dead = true
      · cases b <;>
          simp only [uexec, if_pos hd, Option.some.injEq, if_true, if_false] at hr <;>
          subst hr <;> intro hc <;> exact absurd (hd ▸ hc) (by simp)
      · have hd0 : s.dead = false := by simpa using hd
        obtain ⟨hlive, hinj, hfr, hdisj, hfb⟩ := hS.2 hd0
        have hnl : memInt (pickAddr s.freed s.fresh) s.live = false := by
          cases hq : s.freed with
          | nil =>
              show memInt s.fresh s.live = false
              by_cases hm : memInt s.fresh s.live = true
              · exact absurd (hfr _ hm) (by omega)
              · simpa using hm
          | cons c cs => exact hdisj c (by rw [hq]; simp [memInt])
        have key : ∀ (lab : Bool), P x = lab →
            LabInv P (x :: V)
              ({ s with store := upd s.store x (pickAddr s.freed s.fresh),
                        live := pickAddr s.freed s.fresh :: s.live,
                        freed := dropInt (pickAddr s.freed s.fresh) s.freed,
                        fresh := bumpFresh s.freed s.fresh,
                        hlab := updBU s.hlab (pickAddr s.freed s.fresh) lab,
                        heap := updHU s.heap (pickAddr s.freed s.fresh) 0 }) := by
          intro lab hlabx _ y hy
          show updBU s.hlab (pickAddr s.freed s.fresh) lab
                 (upd s.store x (pickAddr s.freed s.fresh) y) = P y
          by_cases hyx : y = x
          · subst hyx
            simp only [upd, if_pos rfl]
            show (if pickAddr s.freed s.fresh = pickAddr s.freed s.fresh then lab
                  else s.hlab (pickAddr s.freed s.fresh)) = P y
            rw [if_pos rfl, hlabx]
          · have hyV : y ∈ V := memCons_ne hy hyx
            have hne : ¬ (s.store y = pickAddr s.freed s.fresh) := by
              intro hc
              exact absurd (hc ▸ hlive y hyV) (by simp [hnl])
            simp only [upd, if_neg hyx, updBU, if_neg hne]
            exact hL hd0 y hyV
        cases b with
        | false =>
            simp only [uexec, if_neg hd, if_false, Option.some.injEq] at hr
            subst hr; exact key false hb
        | true =>
            simp only [uexec, if_neg hd, if_true, Option.some.injEq] at hr
            subst hr; exact key true hb

/-! ## Preservation -/

/-- **The label invariant is inductive.** Every rule of the joint judgment preserves
    "each tracked pointer points at a cell of its own level". The separation invariant
    is a hypothesis because the allocation case needs it — which is stage 1i paying for
    stage 1w. -/
theorem JSecTy.toLabInv {P : Partition} {V : List String} {c : UCmd} {V' : List String}
    (h : JSecTy P V c V') :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      SepInv V s → LabInv P V s → uexec n c π s = some r → LabInv P V' r.1 := by
  induction h with
  | skip _ => intro n π s r _ hL hr; exact labInv_of_stable labStable_skip hL hr
  | assignH _ x e _ => intro n π s r _ hL hr; exact labInv_assign hL hr
  | assignL _ x e _ => intro n π s r _ hL hr; exact labInv_assign hL hr
  | check _ q => intro n π s r _ hL hr; exact labInv_of_stable (labStable_check q) hL hr
  | access _ q => intro n π s r _ hL hr; exact labInv_of_stable (labStable_access q) hL hr
  | setH _ x e _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_sop .set x e) hL hr
  | setL _ x e _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_sop .set x e) hL hr
  | emit _ q e _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_sop .emit q e) hL hr
  | deref _ x _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_deref x) hL hr
  | storeL _ p v _ _ _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_hstore p v) hL hr
  | storeH _ p v _ _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_hstore p v) hL hr
  | loadL _ d p _ _ => intro n π s r _ hL hr; exact labInv_load hL hr
  | loadH _ d p _ _ => intro n π s r _ hL hr; exact labInv_load hL hr
  | free _ x _ _ =>
      intro n π s r _ hL hr
      exact LabInv.mono (fun _ hz => dropStr_mem hz)
        (labInv_of_stable (labStable_free x) hL hr)
  | alloc _ x hx =>
      intro n π s r hS hL hr
      exact labInv_alloc (b := false) hx hS hL (by simpa using hr)
  | allocS _ x hx =>
      intro n π s r hS hL hr
      exact labInv_alloc (b := true) hx hS hL (by simpa using hr)
  | @seq V V₁ V₂ c₁ c₂ h₁ h₂ ih₁ ih₂ =>
      intro n π s r hS hL hr
      cases n with
      | zero => simp [uexec] at hr
      | succ m =>
          rw [uexec_seq_eq] at hr
          rcases e₁ : uexec m c₁ π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁, Option.bind_some] at hr
            rcases e₂ : uexec m c₂ π r₁.1 with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact ih₂ m π r₁.1 r₂ (h₁.toSepCert.safe m π s r₁ hS e₁)
                (ih₁ m π s r₁ hS hL e₁) e₂
  | @iteL V V₁ V₂ c₁ c₂ e _ h₁ h₂ ih₁ ih₂ =>
      intro n π s r hS hL hr
      cases n with
      | zero => simp [uexec] at hr
      | succ m =>
          rw [uexec_ite_eq] at hr
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg] at hr
            rcases e₁ : uexec m c₁ π s with _ | r₁
            · rw [e₁] at hr; simp at hr
            · rw [e₁] at hr; simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact LabInv.mono (fun _ hz => interStr_left hz) (ih₁ m π s r₁ hS hL e₁)
          · rw [if_neg hg] at hr
            rcases e₂ : uexec m c₂ π s with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact LabInv.mono (fun _ hz => interStr_right hz) (ih₂ m π s r₂ hS hL e₂)
  | @whileW V W W₁ c₀ e _ hWV h₀ hWW₁ ih =>
      have hbody : SepCert W c₀ W := SepCert.weakenPost h₀.toSepCert hWW₁
      have main : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
          SepInv W s → LabInv P W s → uexec n (.loop e c₀) π s = some r →
          LabInv P W r.1 := by
        intro n
        induction n with
        | zero => intro π s r _ _ hr; simp [uexec] at hr
        | succ m ihm =>
            intro π s r hSW hLW hr
            rw [uexec_loop_eq] at hr
            by_cases hg : evalE e s.store ≠ 0
            · rw [if_pos hg] at hr
              rcases e₁ : uexec m c₀ π s with _ | r₁
              · rw [e₁] at hr; simp at hr
              · rw [e₁, Option.bind_some] at hr
                rcases e₂ : uexec m (.loop e c₀) π r₁.1 with _ | r₂
                · rw [e₂] at hr; simp at hr
                · rw [e₂] at hr
                  simp only [Option.map_some, Option.some.injEq] at hr
                  subst hr
                  exact ihm π r₁.1 r₂ (hbody.safe m π s r₁ hSW e₁)
                    (LabInv.mono hWW₁ (ih m π s r₁ hSW hLW e₁)) e₂
            · rw [if_neg hg] at hr
              simp only [Option.some.injEq] at hr; subst hr; exact hLW
      intro n π s r hS hL hr
      exact main n π s r (SepInv.mono hWV hS) (LabInv.mono hWV hL) hr

/-- From a fresh state the invariant holds trivially, so a checked program maintains it
    all the way through. -/
theorem LabInv.initU {P : Partition} {σ : Store} : LabInv P [] (initU σ) := by
  intro _ x hx; simp at hx

/-! ## Two combinators that keep the equations

    The stage-1d versions discard the fact that the sub-run produced a particular
    outcome, which is fine when the only thing threaded is Low-equality. Here the
    invariant has to be re-established at the intermediate state, and that needs the
    equation. -/

theorem uOptLowEq_bindE {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEq P a a')
    {f f' : UState × Nat × List Bool → Option (UState × Nat × List Bool)}
    (hf : ∀ r r', a = some r → a' = some r' → uLowEq P r.1 r'.1 → r.2.1 = r'.2.1 →
          r.2.2 = r'.2.2 → uOptLowEq P (f r) (f' r')) :
    uOptLowEq P (a.bind f) (a'.bind f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' rfl rfl h.1 h.2.1 h.2.2

theorem uOptLowEq_mapE {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEq P a a')
    {f f' : UState × Nat × List Bool → UState × Nat × List Bool}
    (hf : ∀ r r', a = some r → a' = some r' → uLowEq P r.1 r'.1 → r.2.1 = r'.2.1 →
          r.2.2 = r'.2.2 → uLowEq P (f r).1 (f' r').1 ∧ (f r).2.1 = (f' r').2.1 ∧
          (f r).2.2 = (f' r').2.2) :
    uOptLowEq P (a.map f) (a'.map f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' rfl rfl h.1 h.2.1 h.2.2

/-! ## Allocator synchronisation

    Stage 1j left `allocL` open as a design question: allocating into a *Low* variable
    publishes the allocation counter, so it looked like it needed `fresh` in the
    observation — a decision about whether addresses are visible to a Low adversary.

    The question turns out to be avoidable. This type system has **no High-guarded
    control flow**: every `ite` and `loop` guard must be `exprLow`. So two Low-equal
    runs execute the *same* allocations in the same order, and their allocation
    counters never drift apart. Rather than widening the observation, the induction
    carries `s.fresh = s'.fresh` as a **relational invariant** — and then allocation
    into any variable, Low or High, is noninterferent with no side condition at all.

    `stage 1m` therefore *removes* a rule side-condition instead of adding one, and the
    public statements below are unchanged, because two runs both starting from `initU`
    trivially agree on the counter. -/

/-- Low-equivalence **with the allocator synchronised**. The last conjunct is the
    relational invariant; it is not part of what the adversary observes. -/
def uLowEqA (P : Partition) (s s' : UState) : Prop :=
  lowEq P s.store s'.store ∧ s.reads = s'.reads ∧ s.dead = s'.dead ∧ s.fresh = s'.fresh
  ∧ (∀ x, P x = false → s.sstore x = s'.sstore x) ∧ s.sink = s'.sink
  ∧ s.freed = s'.freed
  -- the heap is observed **per address**: labels agree, and public cells agree
  ∧ s.hlab = s'.hlab ∧ (∀ a, s.hlab a = false → s.heap a = s'.heap a)

def uOptLowEqA (P : Partition) :
    Option (UState × Nat × List Bool) → Option (UState × Nat × List Bool) → Prop
  | none,   none    => True
  | some r, some r' => uLowEqA P r.1 r'.1 ∧ r.2.1 = r'.2.1 ∧ r.2.2 = r'.2.2
  | _,      _       => False

/-- The synchronised relation is stronger, so every guarantee proved with it implies
    the ordinary one. Nothing observable was added. -/
theorem uOptLowEqA.toLowEq {P : Partition} :
    ∀ {a a' : Option (UState × Nat × List Bool)}, uOptLowEqA P a a' → uOptLowEq P a a'
  | none,   none,    _ => True.intro
  | some _, some _,  h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1⟩, h.2.1, h.2.2⟩
  | none,   some _,  h => h.elim
  | some _, none,    h => h.elim

theorem uOptLowEqA_bindE {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEqA P a a')
    {f f' : UState × Nat × List Bool → Option (UState × Nat × List Bool)}
    (hf : ∀ r r', a = some r → a' = some r' → uLowEqA P r.1 r'.1 → r.2.1 = r'.2.1 →
          r.2.2 = r'.2.2 → uOptLowEqA P (f r) (f' r')) :
    uOptLowEqA P (a.bind f) (a'.bind f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' rfl rfl h.1 h.2.1 h.2.2

theorem uOptLowEqA_mapE {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEqA P a a')
    {f f' : UState × Nat × List Bool → UState × Nat × List Bool}
    (hf : ∀ r r', a = some r → a' = some r' → uLowEqA P r.1 r'.1 → r.2.1 = r'.2.1 →
          r.2.2 = r'.2.2 → uLowEqA P (f r).1 (f' r').1 ∧ (f r).2.1 = (f' r').2.1 ∧
          (f r).2.2 = (f' r').2.2) :
    uOptLowEqA P (a.map f) (a'.map f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' rfl rfl h.1 h.2.1 h.2.2

/-! ## Soundness: one induction, both guarantees -/

/-- **The joint soundness theorem.** Two runs from memory-safe, Low-equal states are
    Low-equal throughout — including the heap operations, which no earlier theorem
    covered. The memory invariant is a *hypothesis of the noninterference proof*, which
    is the formal content of stage 1j's "these do not factor". -/
theorem jsecTy_sound {P : Partition} :
    ∀ (n : Nat) (c : UCmd) (V V' : List String), JSecTy P V c V' →
      ∀ (π : MedPolicy) (s s' : UState), SepInv V s → SepInv V s' →
        LabInv P V s → LabInv P V s' → uLowEqA P s s' →
        uOptLowEqA P (uexec n c π s) (uexec n c π s') := by
  intro n
  induction n with
  | zero => intro c V V' _ π s s' _ _ _ _ _; exact True.intro
  | succ m ih =>
    intro c V V' hc π s s' hI hI' hL hL' hle
    obtain ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩ := hle
    cases hc with
    | skip _ => exact ⟨⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩, rfl, rfl⟩
    | check _ r =>
        show uOptLowEqA P (uexec (m+1) (.check r) π s) (uexec (m+1) (.check r) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          by_cases hp : π r = true
          · rw [if_pos hp, if_pos hp]; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
          · rw [if_neg hp, if_neg hp]; exact ⟨hst, hrd, rfl, hfr, hss, hsk, hfd, hhl, hho⟩
    | access _ r =>
        show uOptLowEqA P (uexec (m+1) (.access r) π s) (uexec (m+1) (.access r) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          exact ⟨hst, by simp [hrd], hdd, hfr, hss, hsk, hfd, hhl, hho⟩
    | assignH _ x e hx =>
        show uOptLowEqA P (uexec (m+1) (.assign x e) π s) (uexec (m+1) (.assign x e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
          intro y hy
          have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
          show upd s.store x (evalE e s.store) y = upd s'.store x (evalE e s'.store) y
          simp only [upd, if_neg hyx]; exact hst y hy
    | assignL _ x e he =>
        show uOptLowEqA P (uexec (m+1) (.assign x e) π s) (uexec (m+1) (.assign x e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
          intro y hy
          show upd s.store x (evalE e s.store) y = upd s'.store x (evalE e s'.store) y
          simp only [upd]
          by_cases hxy : y = x
          · rw [if_pos hxy, if_pos hxy, evalE_lowEq e he hst]
          · rw [if_neg hxy, if_neg hxy]; exact hst y hy
    | alloc _ x _ =>
        show uOptLowEqA P (uexec (m+1) (.memop .alloc x) π s)
                        (uexec (m+1) (.memop .alloc x) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd,
                  by show bumpFresh s.freed s.fresh = bumpFresh s'.freed s'.fresh
                     rw [hfr, hfd],
                  hss, hsk,
                  by show dropInt (pickAddr s.freed s.fresh) s.freed
                        = dropInt (pickAddr s'.freed s'.fresh) s'.freed
                     rw [hfr, hfd],
                  by show updBU s.hlab (pickAddr s.freed s.fresh) false
                        = updBU s'.hlab (pickAddr s'.freed s'.fresh) false
                     rw [hhl, hfr, hfd],
                  by intro b hb
                     have hba' : b = pickAddr s.freed s.fresh ↔
                         b = pickAddr s'.freed s'.fresh := by rw [hfr, hfd]
                     show (if b = pickAddr s.freed s.fresh then (0 : Int) else s.heap b)
                        = (if b = pickAddr s'.freed s'.fresh then (0 : Int) else s'.heap b)
                     by_cases hba : b = pickAddr s.freed s.fresh
                     · rw [if_pos hba, if_pos (hba'.mp hba)]
                     · rw [if_neg hba, if_neg (fun h => hba (hba'.mpr h))]
                       refine hho b ?_
                       have hb2 : updBU s.hlab (pickAddr s.freed s.fresh) false b
                           = s.hlab b := by simp only [updBU, if_neg hba]
                       rw [← hb2]; exact hb⟩
          intro z hz
          show upd s.store x (pickAddr s.freed s.fresh) z
             = upd s'.store x (pickAddr s'.freed s'.fresh) z
          simp only [upd]
          by_cases hzx : z = x
          · rw [if_pos hzx, if_pos hzx, hfr, hfd]
          · rw [if_neg hzx, if_neg hzx]; exact hst z hz
    | allocS _ x _ =>
        show uOptLowEqA P (uexec (m+1) (.memop .allocS x) π s)
                        (uexec (m+1) (.memop .allocS x) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd,
                  by show bumpFresh s.freed s.fresh = bumpFresh s'.freed s'.fresh
                     rw [hfr, hfd],
                  hss, hsk,
                  by show dropInt (pickAddr s.freed s.fresh) s.freed
                        = dropInt (pickAddr s'.freed s'.fresh) s'.freed
                     rw [hfr, hfd],
                  by show updBU s.hlab (pickAddr s.freed s.fresh) true
                        = updBU s'.hlab (pickAddr s'.freed s'.fresh) true
                     rw [hhl, hfr, hfd],
                  by intro b hb
                     have hba' : b = pickAddr s.freed s.fresh ↔
                         b = pickAddr s'.freed s'.fresh := by rw [hfr, hfd]
                     show (if b = pickAddr s.freed s.fresh then (0 : Int) else s.heap b)
                        = (if b = pickAddr s'.freed s'.fresh then (0 : Int) else s'.heap b)
                     by_cases hba : b = pickAddr s.freed s.fresh
                     · rw [if_pos hba, if_pos (hba'.mp hba)]
                     · rw [if_neg hba, if_neg (fun h => hba (hba'.mpr h))]
                       refine hho b ?_
                       have hb2 : updBU s.hlab (pickAddr s.freed s.fresh) true b
                           = s.hlab b := by simp only [updBU, if_neg hba]
                       rw [← hb2]; exact hb⟩
          intro z hz
          show upd s.store x (pickAddr s.freed s.fresh) z
             = upd s'.store x (pickAddr s'.freed s'.fresh) z
          simp only [upd]
          by_cases hzx : z = x
          · rw [if_pos hzx, if_pos hzx, hfr, hfd]
          · rw [if_neg hzx, if_neg hzx]; exact hst z hz
    | deref _ x hx =>
        show uOptLowEqA P (uexec (m+1) (.memop .deref x) π s)
                        (uexec (m+1) (.memop .deref x) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd0 : s.dead = false := by simpa using hd
          have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          have hd0' : s'.dead = false := by simpa using hd'
          have hl : memInt (s.store x) s.live = true :=
            hI.toMemInv.2 hd0 x (memStr_mem hx)
          have hl' : memInt (s'.store x) s'.live = true :=
            hI'.toMemInv.2 hd0' x (memStr_mem hx)
          rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
          exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
    | free _ x hx hPx =>
        show uOptLowEqA P (uexec (m+1) (.memop .free x) π s)
                        (uexec (m+1) (.memop .free x) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd0 : s.dead = false := by simpa using hd
          have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          have hd0' : s'.dead = false := by simpa using hd'
          have hl : memInt (s.store x) s.live = true :=
            hI.toMemInv.2 hd0 x (memStr_mem hx)
          have hl' : memInt (s'.store x) s'.live = true :=
            hI'.toMemInv.2 hd0' x (memStr_mem hx)
          rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
          -- the freed address is Low, so the two free lists stay identical
          have hpx : s.store x = s'.store x := hst x hPx
          exact ⟨hst, hrd, hdd, hfr, hss, hsk,
                 by show s.store x :: s.freed = s'.store x :: s'.freed
                    rw [hpx, hfd], hhl, hho⟩
    | setH _ x e hx =>
        show uOptLowEqA P (uexec (m+1) (.sop .set x e) π s) (uexec (m+1) (.sop .set x e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨hst, hrd, hdd, hfr, ?_, hsk, hfd, hhl, hho⟩
          intro z hz
          have hzx : ¬ (z = x) := fun h => by rw [h, hx] at hz; cases hz
          show updSU s.sstore x (evalS s.sstore e) z
             = updSU s'.sstore x (evalS s'.sstore e) z
          simp only [updSU, if_neg hzx]; exact hss z hz
    | setL _ x e he =>
        show uOptLowEqA P (uexec (m+1) (.sop .set x e) π s) (uexec (m+1) (.sop .set x e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨hst, hrd, hdd, hfr, ?_, hsk, hfd, hhl, hho⟩
          intro z hz
          show updSU s.sstore x (evalS s.sstore e) z
             = updSU s'.sstore x (evalS s'.sstore e) z
          simp only [updSU]
          by_cases hzx : z = x
          · rw [if_pos hzx, if_pos hzx, evalS_lowEq hss e he]
          · rw [if_neg hzx, if_neg hzx]; exact hss z hz
    | emit _ q e he =>
        show uOptLowEqA P (uexec (m+1) (.sop .emit q e) π s)
                        (uexec (m+1) (.sop .emit q e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨hst, hrd, hdd, hfr, hss, ?_, hfd, hhl, hho⟩
          show (q, evalS s.sstore e) :: s.sink = (q, evalS s'.sstore e) :: s'.sink
          rw [evalS_lowEq hss e he, hsk]
    | loadL _ d p hp hPp =>
        show uOptLowEqA P (uexec (m+1) (.hop .load d p) π s)
                        (uexec (m+1) (.hop .load d p) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd0 : s.dead = false := by simpa using hd
          have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          have hd0' : s'.dead = false := by simpa using hd'
          have hl := hI.toMemInv.2 hd0 p (memStr_mem hp)
          have hl' := hI'.toMemInv.2 hd0' p (memStr_mem hp)
          rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
          refine ⟨?_, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
          intro z hz
          show upd s.store d (s.heap (s.store p)) z
             = upd s'.store d (s'.heap (s'.store p)) z
          simp only [upd]
          by_cases hzd : z = d
          · rw [if_pos hzd, if_pos hzd, hst p hPp]
            exact hho (s'.store p) (by rw [← hst p hPp]; exact (hL hd0 p (memStr_mem hp)).trans hPp)
          · rw [if_neg hzd, if_neg hzd]; exact hst z hz
    | loadH _ d p hp hPd =>
        show uOptLowEqA P (uexec (m+1) (.hop .load d p) π s)
                        (uexec (m+1) (.hop .load d p) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd0 : s.dead = false := by simpa using hd
          have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          have hd0' : s'.dead = false := by simpa using hd'
          have hl := hI.toMemInv.2 hd0 p (memStr_mem hp)
          have hl' := hI'.toMemInv.2 hd0' p (memStr_mem hp)
          rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
          refine ⟨?_, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
          intro z hz
          have hzd : z ≠ d := fun h => by rw [h, hPd] at hz; cases hz
          show upd s.store d (s.heap (s.store p)) z
             = upd s'.store d (s'.heap (s'.store p)) z
          simp only [upd, if_neg hzd]; exact hst z hz
    | storeL _ p v hp hPp hPv =>
        show uOptLowEqA P (uexec (m+1) (.hop .store p v) π s)
                        (uexec (m+1) (.hop .store p v) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd0 : s.dead = false := by simpa using hd
          have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          have hd0' : s'.dead = false := by simpa using hd'
          have hl := hI.toMemInv.2 hd0 p (memStr_mem hp)
          have hl' := hI'.toMemInv.2 hd0' p (memStr_mem hp)
          rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
          refine ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, ?_⟩
          intro b hb
          show (if b = s.store p then s.store v else s.heap b)
             = (if b = s'.store p then s'.store v else s'.heap b)
          rw [hst p hPp, hst v hPv]
          by_cases hbp : b = s'.store p
          · rw [if_pos hbp, if_pos hbp]
          · rw [if_neg hbp, if_neg hbp]; exact hho b hb
    | storeH _ p v hp hPp =>
        show uOptLowEqA P (uexec (m+1) (.hop .store p v) π s)
                        (uexec (m+1) (.hop .store p v) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        · have hd0 : s.dead = false := by simpa using hd
          have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          have hd0' : s'.dead = false := by simpa using hd'
          have hl := hI.toMemInv.2 hd0 p (memStr_mem hp)
          have hl' := hI'.toMemInv.2 hd0' p (memStr_mem hp)
          rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
          refine ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, ?_⟩
          -- both runs write a **secret** cell, so no public cell moves
          intro b hb
          have hsec : s.hlab (s.store p) = true := (hL hd0 p (memStr_mem hp)).trans hPp
          have hsec' : s'.hlab (s'.store p) = true := (hL' hd0' p (memStr_mem hp)).trans hPp
          have hbp : ¬ (b = s.store p) := fun h => by rw [h, hsec] at hb; cases hb
          have hbp' : ¬ (b = s'.store p) := by
            intro h; rw [← hhl] at hsec'; rw [h, hsec'] at hb; cases hb
          show (if b = s.store p then s.store v else s.heap b)
             = (if b = s'.store p then s'.store v else s'.heap b)
          rw [if_neg hbp, if_neg hbp']; exact hho b hb
    | @seq _ V₁ _ c₁ c₂ h₁ h₂ =>
        show uOptLowEqA P (uexec (m+1) (.seq c₁ c₂) π s) (uexec (m+1) (.seq c₁ c₂) π s')
        rw [uexec_seq_eq, uexec_seq_eq]
        refine uOptLowEqA_bindE (ih c₁ _ V₁ h₁ π s s' hI hI' hL hL' ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩) ?_
        intro r₁ r₁' e₁ e₁' hs₁ hc1 ht1
        have hJ : SepInv V₁ r₁.1 := h₁.toSepCert.safe m π s r₁ hI e₁
        have hJ' : SepInv V₁ r₁'.1 := h₁.toSepCert.safe m π s' r₁' hI' e₁'
        have hLJ : LabInv P V₁ r₁.1 := h₁.toLabInv m π s r₁ hI hL e₁
        have hLJ' : LabInv P V₁ r₁'.1 := h₁.toLabInv m π s' r₁' hI' hL' e₁'
        refine uOptLowEqA_mapE (ih c₂ V₁ _ h₂ π r₁.1 r₁'.1 hJ hJ' hLJ hLJ' hs₁) ?_
        intro r₂ r₂' _ _ hs₂ hc2 ht2
        exact ⟨hs₂, by simp [hc1, hc2], by simp [ht1, ht2]⟩
    | @iteL _ _ _ c₁ c₂ e hg h₁ h₂ =>
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        show uOptLowEqA P (uexec (m+1) (.ite e c₁ c₂) π s) (uexec (m+1) (.ite e c₁ c₂) π s')
        rw [uexec_ite_eq, uexec_ite_eq]
        by_cases hb : evalE e s.store ≠ 0
        · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_pos hb, if_pos hb']
          refine uOptLowEqA_mapE (ih c₁ _ _ h₁ π s s' hI hI' hL hL' ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩) ?_
          intro r r' _ _ hs hcs htr; exact ⟨hs, by simp [hcs], by simp [htr]⟩
        · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_neg hb, if_neg hb']
          refine uOptLowEqA_mapE (ih c₂ _ _ h₂ π s s' hI hI' hL hL' ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩) ?_
          intro r r' _ _ hs hcs htr; exact ⟨hs, by simp [hcs], by simp [htr]⟩
    | @whileW _ _ W₁ c₀ e hg hWV h₀ hWW₁ =>
        have hIV' : SepInv V' s := SepInv.mono hWV hI
        have hIV'' : SepInv V' s' := SepInv.mono hWV hI'
        have hLV' : LabInv P V' s := LabInv.mono hWV hL
        have hLV'' : LabInv P V' s' := LabInv.mono hWV hL'
        have hbody : SepCert V' c₀ V' := SepCert.weakenPost h₀.toSepCert hWW₁
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        show uOptLowEqA P (uexec (m+1) (.loop e c₀) π s) (uexec (m+1) (.loop e c₀) π s')
        rw [uexec_loop_eq, uexec_loop_eq]
        by_cases hb : evalE e s.store ≠ 0
        · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_pos hb, if_pos hb']
          refine uOptLowEqA_bindE (ih c₀ V' W₁ h₀ π s s' hIV' hIV'' hLV' hLV'' ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩) ?_
          intro r₁ r₁' e₁ e₁' hs₁ hc1 ht1
          have hJ : SepInv V' r₁.1 := hbody.safe m π s r₁ hIV' e₁
          have hJ' : SepInv V' r₁'.1 := hbody.safe m π s' r₁' hIV'' e₁'
          have hLJ : LabInv P V' r₁.1 :=
            LabInv.mono hWW₁ (h₀.toLabInv m π s r₁ hIV' hLV' e₁)
          have hLJ' : LabInv P V' r₁'.1 :=
            LabInv.mono hWW₁ (h₀.toLabInv m π s' r₁' hIV'' hLV'' e₁')
          refine uOptLowEqA_mapE
            (ih (.loop e c₀) V' V' (.whileW e hg (fun _ hx => hx) h₀ hWW₁)
              π r₁.1 r₁'.1 hJ hJ' hLJ hLJ' hs₁) ?_
          intro r₂ r₂' _ _ hs₂ hc2 ht2
          exact ⟨hs₂, by simp [hc1, hc2], by simp [ht1, ht2]⟩
        · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_neg hb, if_neg hb']
          exact ⟨⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩, rfl, rfl⟩

/-! ## The checker -/

/-- One decidable analysis producing both certificates. -/
def jcheck (P : Partition) : List String → UCmd → Option (List String)
  | V, .skip           => some V
  | V, .assign x e     => if P x || exprLow P e then some (dropStr x V) else none
  | V, .check _        => some V
  | V, .access _       => some V
  | V, .memop .alloc x => if P x then none else some (x :: V)
  | V, .memop .allocS x => if P x then some (x :: V) else none
  | V, .memop .deref x => if memStr x V then some V else none
  | V, .memop .free x  => if memStr x V && !P x then some (dropStr x V) else none
  | V, .sop .set x e   => if P x || sexprLow P e then some V else none
  | V, .sop .emit _ e  => if sexprLow P e then some V else none
  | V, .hop .load d p  => if memStr p V && (!P p || P d) then some (dropStr d V) else none
  | V, .hop .store p v => if memStr p V && (P p || !P v) then some V else none
  | V, .seq c₁ c₂      => (jcheck P V c₁).bind fun V₁ => jcheck P V₁ c₂
  | V, .ite e c₁ c₂    => if exprLow P e then
                            match jcheck P V c₁, jcheck P V c₂ with
                            | some V₁, some V₂ => some (interStr V₁ V₂)
                            | _, _ => none
                          else none
  | V, .loop e c       => if exprLow P e && (jcheck P V c == some V) then some V else none

theorem jcheck_sound {P : Partition} : ∀ (c : UCmd) (V V' : List String),
    jcheck P V c = some V' → JSecTy P V c V'
  | .skip, V, V', h => by
      simp only [jcheck, Option.some.injEq] at h; subst h; exact .skip V
  | .check r, V, V', h => by
      simp only [jcheck, Option.some.injEq] at h; subst h; exact .check V r
  | .access r, V, V', h => by
      simp only [jcheck, Option.some.injEq] at h; subst h; exact .access V r
  | .assign x e, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : (P x || exprLow P e) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        rcases Bool.or_eq_true _ _ |>.mp hx with h' | h'
        · exact .assignH V x e h'
        · exact .assignL V x e h'
      · rw [if_neg hx] at h; simp at h
  | .memop .alloc x, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : P x = true
      · rw [if_pos hx] at h; simp at h
      · rw [if_neg hx] at h
        simp only [Option.some.injEq] at h; subst h
        exact .alloc V x (by simpa using hx)
  | .memop .allocS x, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : P x = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        exact .allocS V x hx
      · rw [if_neg hx] at h; simp at h
  | .memop .deref x, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : memStr x V = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h; exact .deref V x hx
      · rw [if_neg hx] at h; simp at h
  | .memop .free x, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : (memStr x V && !P x) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hx
        exact .free V x h1 (by simpa using h2)
      · rw [if_neg hx] at h; simp at h
  | .seq c₁ c₂, V, V', h => by
      simp only [jcheck] at h
      rcases e₁ : jcheck P V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        exact .seq (jcheck_sound c₁ V V₁ e₁) (jcheck_sound c₂ V₁ V' h)
  | .ite e c₁ c₂, V, V', h => by
      simp only [jcheck] at h
      by_cases hg : exprLow P e = true
      · rw [if_pos hg] at h
        rcases e₁ : jcheck P V c₁ with _ | V₁
        · rw [e₁] at h; simp at h
        · rcases e₂ : jcheck P V c₂ with _ | V₂
          · rw [e₁, e₂] at h; simp at h
          · rw [e₁, e₂] at h
            simp only [Option.some.injEq] at h; subst h
            exact .iteL e hg (jcheck_sound c₁ V V₁ e₁) (jcheck_sound c₂ V V₂ e₂)
      · rw [if_neg hg] at h; simp at h
  | .sop .set x e, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : (P x || sexprLow P e) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        rcases Bool.or_eq_true _ _ |>.mp hx with h' | h'
        · exact .setH V x e h'
        · exact .setL V x e h'
      · rw [if_neg hx] at h; simp at h
  | .sop .emit q e, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : sexprLow P e = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        exact .emit V q e hx
      · rw [if_neg hx] at h; simp at h
  | .hop .load d p, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : (memStr p V && (!P p || P d)) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hx
        rcases Bool.or_eq_true _ _ |>.mp h2 with h' | h'
        · exact .loadL V d p h1 (by simpa using h')
        · exact .loadH V d p h1 h'
      · rw [if_neg hx] at h; simp at h
  | .hop .store p v, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : (memStr p V && (P p || !P v)) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hx
        rcases Bool.or_eq_true _ _ |>.mp h2 with h' | h'
        · exact .storeH V p v h1 h'
        · by_cases hpp : P p = true
          · exact .storeH V p v h1 hpp
          · exact .storeL V p v h1 (by simpa using hpp) (by simpa using h')
      · rw [if_neg hx] at h; simp at h
  | .loop e c₀, V, V', h => by
      simp only [jcheck] at h
      by_cases hg : (exprLow P e && (jcheck P V c₀ == some V)) = true
      · rw [if_pos hg] at h
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hg1, hg2⟩ := Bool.and_eq_true _ _ |>.mp hg
        exact .whileW e hg1 (fun _ hx => hx)
          (jcheck_sound c₀ V V (by simpa using hg2)) (fun _ hx => hx)
      · rw [if_neg hg] at h; simp at h

/-- **Both guarantees, from one run of one checker.** Noninterference *including* the
    heap operations, and no memory fault — for a program the two separate checkers
    could not certify together. -/
theorem jcheck_gives_both {P : Partition} {c : UCmd} {V' : List String}
    (h : jcheck P [] c = some V') :
    (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false) := by
  have hty := jcheck_sound c [] V' h
  refine ⟨fun n π σ σ' hσ => ?_, fun n π σ r hr => ?_⟩
  · exact uOptLowEqA.toLowEq (jsecTy_sound n c [] V' hty π (initU σ) (initU σ')
      SepInv.initU SepInv.initU LabInv.initU LabInv.initU
      ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩)
  · exact (hty.toSepCert.safe n π (initU σ) r SepInv.initU hr).1

/-! ## What the index buys -/

/-- Allocate a pointer in a secret, use it, mediate an access, release it. Every
    ingredient the two separate checkers choke on. -/
def safeHeapProg : UCmd :=
  .seq (.memop .alloc "buf")
   (.seq (.memop .deref "buf")
    (.seq (.check "db")
     (.seq (.access "db") (.memop .free "buf"))))

/-- **The indexed judgment proves what the conjunction of its parts cannot.** The
    stage-1d checker rejects this program outright — it dereferences — so no NI
    certificate is available from it at any partition; the stage-1i checker accepts it
    but is silent about leaks. `jcheck` certifies both properties at once. This is the
    concrete payoff of stage 1j's counterexample. -/
theorem indexed_beats_the_conjunction :
    ucheckNI Psec safeHeapProg = false
  ∧ slcheck [] safeHeapProg = some []
  ∧ jcheck Psec [] safeHeapProg = some [] := by decide

/-- Spelled out on that program: noninterference through a dereference, and no fault. -/
theorem safeHeapProg_both :
    (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n safeHeapProg π (initU σ))
                       (uexec n safeHeapProg π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n safeHeapProg π (initU σ) = some r → r.1.err = false) :=
  jcheck_gives_both indexed_beats_the_conjunction.2.2

/-- And it runs: the access is mediated, nothing faults, the pointer is released. -/
theorem safeHeapProg_runs :
    ((uexec 9 safeHeapProg (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.err, r.1.dead, r.1.reads, r.1.live))) = some (false, false, ["db"], []) := by
  decide

/-! ## What is still conservative, and why

    Two rules say "no" to programs that are in fact safe, and both refusals were
    argued for before they were implemented rather than after.

    `allocL` is absent: allocation into a *Low* variable needs `fresh` in the
    observation, which is stage 1j's open question about whether addresses are public.
    `allocL_would_be_unsound` is the witness that it cannot simply be added.

    A loop must preserve the tracked set **exactly** (`jcheck` requires
    `jcheck P V c == some V`), so a loop body that allocates without freeing is
    rejected even when the allocation is harmless. The fix is a widening step — start
    from `V` and iterate the body's effect to a fixed point, exactly as brick 30's
    `loopFix` does for the interval domain — and it is a real piece of work rather than
    a missing line, so it is named here instead of hidden. -/

/-- The conservatism is real and worth being able to point at: a loop that allocates is
    rejected, though nothing about it is unsafe. -/
theorem allocating_loop_rejected :
    jcheck Psec [] (.loop (.num 1) (.memop .alloc "secret")) = none := by decide

end ConfTyping
