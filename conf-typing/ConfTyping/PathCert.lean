/-
  The composable core, stage 1q: path traversal — the last coverage row that was
  expressible but unwritten.

  Stage 1o said this row was "the same shape with `/` and `..` in place of the
  delimiter". That was half right, and the half that was wrong is what makes the stage
  worth writing. Injection is about a **count**: how many delimiters reach the sink.
  Traversal is about a **prefix condition**: a path escapes its root when some *prefix*
  of it pops above the root, and no count can see that, because `a/../b` and `../a/b`
  have the same symbol counts and only one of them escapes.

  So the same two-symbol alphabet gets a second reading — `ord` is an ordinary path
  segment, `quote` is the parent segment `..` — and a new property: `walk` runs the
  depth and fails if it ever underflows. `safePath` is "the walk survives".

  **Path safety depends on the taint environment**, and does not factor from it. To
  know that a variable can only *increase* depth, the analysis must know the variable
  contains no parent segments — which is exactly the count-zero fact stage 1o's
  `TaintEnv` records. `path_needs_the_taint_environment` shows the dependency
  concretely: the same program is refused with an empty environment and accepted with
  the variable recorded as count-zero. That is the second dependency in the bundle,
  after noninterference-needs-memory-safety (stage 1j), and unlike that one it is a
  clean layering rather than an entanglement: `PathCert` takes the environment as a
  parameter, so no new indexed judgment is needed.

  **The discipline is per-sink**, which is why stage 1p made the sink record its
  destination. A query and a file path are checked by different rules, and a program
  that emits both is fine: `pcheck fs` constrains only the emits that go to `fs`, and
  `query_sink_untouched_by_path_checker` records that it says nothing about the others.

  The row, as in stage 1o: a real escape (`path_escape_is_real` — the attack emits a
  path that pops above its root), a refusal, an accepted fix, and a guarantee that holds
  for every attacker input rather than the one payload.
-/
import ConfTyping.AllFive

namespace ConfTyping

/-! ## Walking a path -/

/-- Run the depth. `ord` descends into a segment, `quote` is `..` and pops; popping at
    depth zero escapes the root, and there is no recovery from that. -/
def walk (d : Nat) : UStr → Option Nat
  | []           => some d
  | .ord   :: cs => walk (d+1) cs
  | .quote :: cs => match d with
                    | 0      => none
                    | d' + 1 => walk d' cs

/-- A path is safe when the walk survives — no prefix pops above the root. -/
def safePath (t : UStr) : Bool := (walk 0 t).isSome

theorem walk_append : ∀ (t u : UStr) (d : Nat),
    walk d (t ++ u) = (walk d t).bind fun d' => walk d' u
  | [],           _, _ => rfl
  | .ord :: cs,   u, d => by
      show walk (d+1) (cs ++ u) = _
      rw [walk_append cs u (d+1)]; rfl
  | .quote :: cs, u, d => by
      cases d with
      | zero => rfl
      | succ d' =>
          show walk d' (cs ++ u) = _
          rw [walk_append cs u d']; rfl

/-- Starting deeper can only help: the walk still survives, and ends at least as deep. -/
theorem walk_mono : ∀ (t : UStr) (d e d' : Nat), d ≤ e → walk d t = some d' →
    ∃ e', walk e t = some e' ∧ d' ≤ e'
  | [],           d, e, d', hde, h => by
      simp only [walk, Option.some.injEq] at h; subst h
      exact ⟨e, rfl, hde⟩
  | .ord :: cs,   d, e, d', hde, h => by
      show ∃ e', walk (e+1) cs = some e' ∧ d' ≤ e'
      exact walk_mono cs (d+1) (e+1) d' (by omega) h
  | .quote :: cs, d, e, d', hde, h => by
      cases d with
      | zero => simp [walk] at h
      | succ d₀ =>
          cases e with
          | zero => omega
          | succ e₀ =>
              show ∃ e', walk e₀ cs = some e' ∧ d' ≤ e'
              exact walk_mono cs d₀ e₀ d' (by omega) h

/-- A string with no parent segments cannot pop, so the walk always survives it. -/
theorem walk_noQuote : ∀ (u : UStr), qcount u = 0 → ∀ (d : Nat),
    ∃ d', walk d u = some d' ∧ d ≤ d'
  | [],           _, d => ⟨d, rfl, Nat.le_refl d⟩
  | .ord :: cs,   h, d => by
      have h0 : qcount cs = 0 := by simpa [qcount] using h
      obtain ⟨d', hd', hle⟩ := walk_noQuote cs h0 (d+1)
      exact ⟨d', hd', by omega⟩
  | .quote :: cs, h, _ => by simp [qcount] at h

/-! ## Checking a path expression -/

/-- A **lower bound** on the depth the expression leaves you at, or `none` if it might
    escape. A variable is usable only when the taint environment records it as
    containing no parent segments; then it can only descend, so the bound carries. -/
def spath (C : TaintEnv) (d : Nat) : SExpr → Option Nat
  | .lit t   => walk d t
  | .var x   => if lookNat x C == some 0 then some d else none
  | .cat a b => (spath C d a).bind fun d' => spath C d' b
  | .san _   => some d

/-- **The bound is real.** -/
theorem spath_sound {C : TaintEnv} {τ : String → UStr}
    (hC : ∀ p ∈ C, qcount (τ p.1) = p.2) :
    ∀ (e : SExpr) (d d' : Nat), spath C d e = some d' →
      ∃ dd, walk d (evalS τ e) = some dd ∧ d' ≤ dd
  | .lit t, d, d', h => ⟨d', h, Nat.le_refl d'⟩
  | .var x, d, d', h => by
      simp only [spath] at h
      by_cases hx : (lookNat x C == some 0) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        have hx0 : lookNat x C = some 0 := by simpa using hx
        have : qcount (τ x) = 0 := hC (x, 0) (lookNat_mem hx0)
        exact walk_noQuote (τ x) this d
      · rw [if_neg hx] at h; simp at h
  | .cat a b, d, d', h => by
      simp only [spath] at h
      rcases ea : spath C d a with _ | d₁
      · rw [ea] at h; simp at h
      · rw [ea, Option.bind_some] at h
        obtain ⟨da, hda, hle⟩ := spath_sound hC a d d₁ ea
        obtain ⟨db, hdb, hle'⟩ := spath_sound hC b d₁ d' h
        obtain ⟨db', hdb', hle''⟩ := walk_mono (evalS τ b) d₁ da db hle hdb
        refine ⟨db', ?_, by omega⟩
        show walk d (evalS τ a ++ evalS τ b) = some db'
        rw [walk_append, hda, Option.bind_some, hdb']
  | .san a, d, d', h => by
      simp only [spath, Option.some.injEq] at h; subst h
      show ∃ dd, walk d (sanStr (evalS τ a)) = some dd ∧ d ≤ dd
      exact walk_noQuote _ (qcount_sanStr _) d

/-! ## The certificate -/

/-- Every string this command sends **to `fs`** is a path that stays inside its root.
    Emits to other sinks are someone else's problem, by design: see
    `query_sink_untouched_by_path_checker`. -/
structure PathCert (fs : String) (C : TaintEnv) (c : UCmd) (C' : TaintEnv) : Prop where
  env  : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    TaintInv C s → uexec n c π s = some r → TaintInv C' r.1
  path : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    TaintInv C s → uexec n c π s = some r →
    ∀ p ∈ r.1.sink, p ∈ s.sink ∨ (p.1 = fs → safePath p.2 = true)

theorem PathCert.inert {fs : String} {C : TaintEnv} {c : UCmd} (h : StringInert c) :
    PathCert fs C c C :=
  ⟨(TaintCert.inert (C := C) h).env,
   fun n π s r _ hr t ht => Or.inl (by rwa [(h n π s r hr).2.1] at ht)⟩

theorem PathCert.skip {fs : String} {C : TaintEnv} : PathCert fs C .skip C :=
  PathCert.inert StringInert.skip

theorem PathCert.assign {fs : String} {C : TaintEnv} (x : String) (e : Expr) :
    PathCert fs C (.assign x e) C :=
  PathCert.inert (StringInert.assign x e)

theorem PathCert.check {fs : String} {C : TaintEnv} (q : String) :
    PathCert fs C (.check q) C :=
  PathCert.inert (StringInert.check q)

theorem PathCert.access {fs : String} {C : TaintEnv} (q : String) :
    PathCert fs C (.access q) C :=
  PathCert.inert (StringInert.access q)

theorem PathCert.memop {fs : String} {C : TaintEnv} (op : MemOp) (x : String) :
    PathCert fs C (.memop op x) C :=
  PathCert.inert (StringInert.memop op x)

/-- Assignment only moves the environment; the sink is untouched. -/
theorem PathCert.set {fs : String} {C : TaintEnv} (x : String) (e : SExpr) (k : Nat)
    (hk : scount C e = some k) :
    PathCert fs C (.sop .set x e) ((x, k) :: dropPair x C) :=
  ⟨(TaintCert.set x e k hk).env,
   fun n π s r hinv hr t ht =>
     Or.inl (by
       rcases (TaintCert.set x e k hk).sink n π s r hinv hr t ht with h' | h'
       · exact h'
       · simp at h')⟩

theorem PathCert.setUnknown {fs : String} {C : TaintEnv} (x : String) (e : SExpr) :
    PathCert fs C (.sop .set x e) (dropPair x C) :=
  ⟨(TaintCert.setUnknown x e).env,
   fun n π s r hinv hr t ht =>
     Or.inl (by
       rcases (TaintCert.setUnknown x e).sink n π s r hinv hr t ht with h' | h'
       · exact h'
       · simp at h')⟩

/-- **The rule with the obligation.** Emitting to the protected sink requires the
    expression's walk to survive, which requires every variable in it to be recorded as
    free of parent segments. -/
theorem PathCert.emit {fs : String} {C : TaintEnv} (q : String) (e : SExpr) (d : Nat)
    (hd : spath C 0 e = some d) : PathCert fs C (.sop .emit q e) C := by
  constructor
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hdd : s.dead = true
        · simp only [if_pos hdd]; exact hinv
        · simp only [if_neg hdd]; exact hinv
  · intro n π s r hinv hr t ht
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hdd : s.dead = true
        · simp only [if_pos hdd] at ht; exact Or.inl ht
        · have hd0 : s.dead = false := by simpa using hdd
          simp only [if_neg hdd] at ht
          rcases List.mem_cons.mp ht with h' | h'
          · refine Or.inr (fun _ => ?_)
            obtain ⟨dd, hw, _⟩ := spath_sound (hinv hd0) e 0 d hd
            rw [h']
            show (walk 0 (evalS s.sstore e)).isSome = true
            rw [hw]; rfl
          · exact Or.inl h'

/-- Emitting somewhere else is unconstrained: this certificate is about `fs`. -/
theorem PathCert.emitElsewhere {fs : String} {C : TaintEnv} (q : String) (e : SExpr)
    (hq : ¬ (q = fs)) : PathCert fs C (.sop .emit q e) C := by
  constructor
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hdd : s.dead = true
        · simp only [if_pos hdd]; exact hinv
        · simp only [if_neg hdd]; exact hinv
  · intro n π s r _ hr t ht
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hdd : s.dead = true
        · simp only [if_pos hdd] at ht; exact Or.inl ht
        · simp only [if_neg hdd] at ht
          rcases List.mem_cons.mp ht with h' | h'
          · exact Or.inr (fun hfs => absurd (by rw [← hfs, h']) hq)
          · exact Or.inl h'

theorem PathCert.seq {fs : String} {C C₁ C₂ : TaintEnv} {c₁ c₂ : UCmd}
    (h₁ : PathCert fs C c₁ C₁) (h₂ : PathCert fs C₁ c₂ C₂) :
    PathCert fs C (.seq c₁ c₂) C₂ := by
  constructor
  · intro n π s r hinv hr
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
            exact h₂.env n π r₁.1 r₂ (h₁.env n π s r₁ hinv e₁) e₂
  · intro n π s r hinv hr t ht
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
            have hi₁ := h₁.env n π s r₁ hinv e₁
            rcases h₂.path n π r₁.1 r₂ hi₁ e₂ t ht with h' | h'
            · exact h₁.path n π s r₁ hinv e₁ t h'
            · exact Or.inr h'

theorem PathCert.ite {fs : String} {C C₁ C₂ : TaintEnv} {e : Expr} {c₁ c₂ : UCmd}
    (h₁ : PathCert fs C c₁ C₁) (h₂ : PathCert fs C c₂ C₂) :
    PathCert fs C (.ite e c₁ c₂) (interNat C₁ C₂) := by
  constructor
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        rw [uexec_ite_eq] at hr
        by_cases hg : evalE e s.store ≠ 0
        · rw [if_pos hg] at hr
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁] at hr; simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            intro hd p hp
            exact h₁.env n π s r₁ hinv e₁ hd p (interNat_left hp)
        · rw [if_neg hg] at hr
          rcases e₂ : uexec n c₂ π s with _ | r₂
          · rw [e₂] at hr; simp at hr
          · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            intro hd p hp
            exact h₂.env n π s r₂ hinv e₂ hd p (interNat_right hp)
  · intro n π s r hinv hr t ht
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        rw [uexec_ite_eq] at hr
        by_cases hg : evalE e s.store ≠ 0
        · rw [if_pos hg] at hr
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁] at hr; simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            exact h₁.path n π s r₁ hinv e₁ t ht
        · rw [if_neg hg] at hr
          rcases e₂ : uexec n c₂ π s with _ | r₂
          · rw [e₂] at hr; simp at hr
          · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            exact h₂.path n π s r₂ hinv e₂ t ht

/-! ## The checker -/

def pcheck (fs : String) (C : TaintEnv) : UCmd → Option TaintEnv
  | .skip          => some C
  | .assign _ _    => some C
  | .check _       => some C
  | .access _      => some C
  | .memop _ _     => some C
  | .sop .set x e  => match scount C e with
                      | some k => some ((x, k) :: dropPair x C)
                      | none   => some (dropPair x C)
  | .sop .emit q e => if q == fs then
                        match spath C 0 e with
                        | some _ => some C
                        | none   => none
                      else some C
  | .seq c₁ c₂     => (pcheck fs C c₁).bind fun C₁ => pcheck fs C₁ c₂
  | .ite _ c₁ c₂   => match pcheck fs C c₁, pcheck fs C c₂ with
                      | some C₁, some C₂ => some (interNat C₁ C₂)
                      | _, _ => none
  | .loop _ _      => none

theorem pcheck_sound (fs : String) : ∀ (c : UCmd) (C C' : TaintEnv),
    pcheck fs C c = some C' → PathCert fs C c C'
  | .skip, C, C', h => by
      simp only [pcheck, Option.some.injEq] at h; subst h; exact PathCert.skip
  | .assign x e, C, C', h => by
      simp only [pcheck, Option.some.injEq] at h; subst h; exact PathCert.assign x e
  | .check q, C, C', h => by
      simp only [pcheck, Option.some.injEq] at h; subst h; exact PathCert.check q
  | .access q, C, C', h => by
      simp only [pcheck, Option.some.injEq] at h; subst h; exact PathCert.access q
  | .memop op x, C, C', h => by
      simp only [pcheck, Option.some.injEq] at h; subst h; exact PathCert.memop op x
  | .sop .set x e, C, C', h => by
      simp only [pcheck] at h
      rcases hk : scount C e with _ | k
      · rw [hk] at h
        simp only [Option.some.injEq] at h; subst h
        exact PathCert.setUnknown x e
      · rw [hk] at h
        simp only [Option.some.injEq] at h; subst h
        exact PathCert.set x e k hk
  | .sop .emit q e, C, C', h => by
      simp only [pcheck] at h
      by_cases hq : (q == fs) = true
      · rw [if_pos hq] at h
        rcases hd : spath C 0 e with _ | d
        · rw [hd] at h; simp at h
        · rw [hd] at h
          simp only [Option.some.injEq] at h; subst h
          exact PathCert.emit q e d hd
      · rw [if_neg hq] at h
        simp only [Option.some.injEq] at h; subst h
        exact PathCert.emitElsewhere q e (by simpa using hq)
  | .seq c₁ c₂, C, C', h => by
      simp only [pcheck] at h
      rcases e₁ : pcheck fs C c₁ with _ | C₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        exact PathCert.seq (pcheck_sound fs c₁ C C₁ e₁) (pcheck_sound fs c₂ C₁ C' h)
  | .ite e c₁ c₂, C, C', h => by
      simp only [pcheck] at h
      rcases e₁ : pcheck fs C c₁ with _ | C₁
      · rw [e₁] at h; simp at h
      · rcases e₂ : pcheck fs C c₂ with _ | C₂
        · rw [e₁, e₂] at h; simp at h
        · rw [e₁, e₂] at h
          simp only [Option.some.injEq] at h; subst h
          exact PathCert.ite (pcheck_sound fs c₁ C C₁ e₁) (pcheck_sound fs c₂ C C₂ e₂)
  | .loop _ _, _, _, h => by simp [pcheck] at h

/-- **No path escapes its root.** Every string a checked program sends to the protected
    sink stays inside — CWE-22, on the unified machine. -/
theorem pcheck_no_escape {fs : String} {c : UCmd} {C' : TaintEnv}
    (h : pcheck fs [] c = some C') :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n c π s = some r →
      ∀ p ∈ r.1.sink, p.1 = fs → safePath p.2 = true := by
  intro n π s r hs hr p hp hfs
  have hinv : TaintInv [] s := by intro _ q hq; simp at hq
  rcases (pcheck_sound fs c [] C' h).path n π s r hinv hr p hp with h' | h'
  · rw [hs] at h'; simp at h'
  · exact h' hfs

/-! ## The row -/

/-- Serve `root/INPUT` with the input spliced straight in. -/
def vulnPath : UCmd := .sop .emit "fs" (.cat (.lit [.ord]) (.var "input"))

/-- The same, with the one discharge applied. -/
def safePathProg : UCmd := .sop .emit "fs" (.cat (.lit [.ord]) (.san (.var "input")))

/-- An input of `../..`: the traversal payload, in this alphabet. -/
def escapeState : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false, heap := fun _ => 0,
    live := [], fresh := 0, err := false,
    sstore := fun y => if y == "input" then [UCh.quote, UCh.quote] else [], sink := [] }

/-- **The escape is real.** The vulnerable program emits a path that pops above its
    root; the sanitised one does not, on the same payload. -/
theorem path_escape_is_real :
    ((uexec 2 vulnPath (fun _ => true) escapeState).map
      (fun r => r.1.sink.map (fun p => safePath p.2))) = some [false]
  ∧ ((uexec 2 safePathProg (fun _ => true) escapeState).map
      (fun r => r.1.sink.map (fun p => safePath p.2))) = some [true] := by decide

theorem path_escape_rejected : pcheck "fs" [] vulnPath = none := by decide

theorem safe_path_checks : pcheck "fs" [] safePathProg = some [] := by decide

/-- And the guarantee is for every input, not the one payload. -/
theorem safe_path_holds_under_every_input :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n safePathProg π s = some r →
      ∀ p ∈ r.1.sink, p.1 = "fs" → safePath p.2 = true :=
  pcheck_no_escape safe_path_checks

theorem path_row :
    ((uexec 2 vulnPath (fun _ => true) escapeState).map
      (fun r => r.1.sink.map (fun p => safePath p.2))) = some [false]
  ∧ pcheck "fs" [] vulnPath = none
  ∧ pcheck "fs" [] safePathProg = some []
  ∧ (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        s.sink = [] → uexec n safePathProg π s = some r →
        ∀ p ∈ r.1.sink, p.1 = "fs" → safePath p.2 = true) :=
  ⟨path_escape_is_real.1, path_escape_rejected, safe_path_checks,
   safe_path_holds_under_every_input⟩

/-! ## Two things the row shows about the bundle -/

/-- **Path safety does not factor from taint.** The same program is refused with an
    empty environment and accepted once the variable is recorded as containing no
    parent segments — the count-zero fact that stage 1o's environment carries. So this
    certificate *layers on* the taint one rather than sitting beside it, which is the
    second dependency in the bundle after noninterference-needs-memory-safety. Unlike
    that one it is a clean layering: `PathCert` takes the environment as a parameter,
    so no new indexed judgment was needed. -/
theorem path_needs_the_taint_environment :
    pcheck "fs" [] vulnPath = none
  ∧ pcheck "fs" [("input", 0)] vulnPath = some [("input", 0)] := by decide

/-- **The discipline is per-sink.** A query is not a path: the path checker says
    nothing about emits that do not go to the protected sink, which is exactly why
    stage 1p made the sink record its destination. -/
theorem query_sink_untouched_by_path_checker :
    pcheck "fs" [] (.sop .emit "db" (.cat (.lit [.ord]) (.var "input"))) = some [] := by
  decide

/-- And a count cannot decide this row: `a/..` and `../a` carry the same symbols, and
    only one of them escapes. This is why stage 1o's "same shape with `/` and `..`" was
    only half right. -/
theorem counting_cannot_decide_traversal :
    qcount [UCh.ord, UCh.quote] = qcount [UCh.quote, UCh.ord]
  ∧ safePath [UCh.ord, UCh.quote] = true
  ∧ safePath [UCh.quote, UCh.ord] = false := by decide

end ConfTyping
