/-
  The composable core, stage 1o: strings, and injection on the unified machine.

  Every stage since 1h said the same thing about the two remaining coverage rows:
  `UCmd` has no strings, so injection (CWE-89/78/79) and path traversal (CWE-22) are
  not *expressible* here — they are proved in bricks 11–20 on their own languages and
  are not carried by the bundle. This stage adds the missing value domain.

  **The alphabet is two symbols, and that is not a simplification.** An injection
  succeeds by contributing a *delimiter* the query's author did not intend. So `UCh` is
  exactly "delimiter or not", and the guarantee is about how many delimiters reach the
  sink. Everything else about a character is irrelevant to the attack, and keeping the
  alphabet at two symbols keeps every witness a `decide`.

  **The certificate tracks exact counts, not a taint bit.** A taint bit is too coarse to
  be useful: a query variable legitimately *contains* delimiters — `name='` has one —
  so "clean vs tainted" would reject every real query. `TaintEnv` maps a string variable
  to the exact number of delimiters it holds, `scount` computes the count of an
  expression symbolically, and `sanStr` is the single discharge that turns an unknown
  count into zero. The guarantee is then structural: **every emitted string carries
  exactly the number of delimiters the analysis predicted**, so untrusted input cannot
  change the shape of the query.

  `injection_is_real` is the attack, executed: the vulnerable program emits a string
  with three delimiters where two were intended. `injection_rejected` shows the checker
  refuses it, and `sanitised_query_checks` / `sanitised_query_holds_under_attack` show
  the sanitised version is accepted and emits two delimiters *on the same malicious
  input*. Those three together are the row: a real attack, a refusal, and a fix that
  survives the attack.

  Honest scope, three items. The sink is **not** in the noninterference observation, so
  `USecTy`/`JSecTy` still have no rule for `sop` and nothing here says an emitted string
  keeps secrets — a checked program's *structure* is guaranteed, its confidentiality is
  not. Loops have no rule (the count environment would need the same narrowing stage 1l
  gave the tracked set — mechanical, but a stage of its own). And path traversal is
  *now expressible* but not done: it is the same shape with `/` and `..` in place of the
  delimiter, and claiming it without writing it would be exactly the kind of drift the
  guards exist to catch.
-/
import ConfTyping.FullCert

namespace ConfTyping

/-! ## Environments mapping string variables to exact delimiter counts -/

abbrev TaintEnv := List (String × Nat)

def lookNat (x : String) : TaintEnv → Option Nat
  | []           => none
  | (y, k) :: r  => if y == x then some k else lookNat x r

def dropPair (x : String) : TaintEnv → TaintEnv
  | []           => []
  | (y, k) :: r  => if y == x then dropPair x r else (y, k) :: dropPair x r

theorem lookNat_mem {x : String} {k : Nat} :
    ∀ {C : TaintEnv}, lookNat x C = some k → (x, k) ∈ C
  | [],          h => by simp [lookNat] at h
  | (y, j) :: r, h => by
      by_cases hy : y = x
      · rw [lookNat, if_pos (by simp [hy])] at h
        simp only [Option.some.injEq] at h
        subst h; subst hy; exact List.mem_cons_self ..
      · rw [lookNat, if_neg (by simpa using hy)] at h
        exact List.mem_cons_of_mem _ (lookNat_mem h)

theorem dropPair_mem {x : String} {p : String × Nat} :
    ∀ {C : TaintEnv}, p ∈ dropPair x C → p ∈ C
  | [],          h => by simp [dropPair] at h
  | (y, j) :: r, h => by
      by_cases hy : y = x
      · rw [dropPair, if_pos (by simp [hy])] at h
        exact List.mem_cons_of_mem _ (dropPair_mem h)
      · rw [dropPair, if_neg (by simpa using hy)] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact h' ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (dropPair_mem h')

theorem dropPair_ne {x : String} {p : String × Nat} :
    ∀ {C : TaintEnv}, p ∈ dropPair x C → ¬ (p.1 = x)
  | [],          h => by simp [dropPair] at h
  | (y, j) :: r, h => by
      by_cases hy : y = x
      · rw [dropPair, if_pos (by simp [hy])] at h; exact dropPair_ne h
      · rw [dropPair, if_neg (by simpa using hy)] at h
        rcases List.mem_cons.mp h with h' | h'
        · rw [h']; simpa using hy
        · exact dropPair_ne h'

/-- Branch join: keep the variables both branches agree on, *count and all*. -/
def interNat : TaintEnv → TaintEnv → TaintEnv
  | [],          _ => []
  | (y, k) :: r, D => if lookNat y D == some k then (y, k) :: interNat r D
                      else interNat r D

theorem interNat_left {p : String × Nat} :
    ∀ {C D : TaintEnv}, p ∈ interNat C D → p ∈ C
  | [],          _, h => by simp [interNat] at h
  | (y, k) :: r, D, h => by
      by_cases hy : (lookNat y D == some k) = true
      · rw [interNat, if_pos hy] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact h' ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (interNat_left h')
      · rw [interNat, if_neg hy] at h
        exact List.mem_cons_of_mem _ (interNat_left h)

theorem interNat_right {p : String × Nat} :
    ∀ {C D : TaintEnv}, p ∈ interNat C D → p ∈ D
  | [],          _, h => by simp [interNat] at h
  | (y, k) :: r, D, h => by
      by_cases hy : (lookNat y D == some k) = true
      · rw [interNat, if_pos hy] at h
        rcases List.mem_cons.mp h with h' | h'
        · have : lookNat y D = some k := by simpa using hy
          exact h' ▸ lookNat_mem this
        · exact interNat_right h'
      · rw [interNat, if_neg hy] at h
        exact interNat_right h

/-! ## Counting delimiters symbolically -/

/-- The delimiter count of an expression, if the analysis can pin it down. A variable
    contributes its recorded count; `san` contributes zero; anything unknown makes the
    whole expression unknown. -/
def scount (C : TaintEnv) : SExpr → Option Nat
  | .lit t   => some (qcount t)
  | .var x   => lookNat x C
  | .cat a b => match scount C a, scount C b with
                | some m, some n => some (m + n)
                | _, _           => none
  | .san _   => some 0

/-- The invariant the environment describes — **while the run is live**. A refused run
    stops updating the string store, so a recorded count need not survive an abort;
    conditioning on `dead` is the same shape `MemInv` needed for the heap, and for the
    same reason. Getting this wrong made the `set` rule unsound in a first draft. -/
def TaintInv (C : TaintEnv) (s : UState) : Prop :=
  s.dead = false → ∀ p ∈ C, qcount (s.sstore p.1) = p.2

/-- **The symbolic count is the real count.** -/
theorem scount_sound {C : TaintEnv} {τ : String → UStr}
    (hC : ∀ p ∈ C, qcount (τ p.1) = p.2) :
    ∀ (e : SExpr) (k : Nat), scount C e = some k → qcount (evalS τ e) = k
  | .lit t, k, h => by
      simp only [scount, Option.some.injEq] at h; subst h; rfl
  | .var x, k, h => by
      simp only [scount] at h
      exact hC (x, k) (lookNat_mem h)
  | .cat a b, k, h => by
      simp only [scount] at h
      rcases ea : scount C a with _ | m
      · rw [ea] at h; simp at h
      · rcases eb : scount C b with _ | n
        · rw [ea, eb] at h; simp at h
        · rw [ea, eb] at h
          simp only [Option.some.injEq] at h
          subst h
          show qcount (evalS τ a ++ evalS τ b) = m + n
          rw [qcount_append, scount_sound hC a m ea, scount_sound hC b n eb]
  | .san a, k, h => by
      simp only [scount, Option.some.injEq] at h; subst h
      exact qcount_sanStr _

/-! ## The certificate -/

/-- **A structural-integrity certificate.** It threads a count environment — the same
    Hoare-triple shape as the authorization set and the tracked pointer set, a *fourth*
    instance — and accumulates the list of delimiter counts the program may emit.
    `Ks` composing by `++` is a fifth accumulation monoid, after `+`, threading,
    conjunction and the ledger's append. -/
structure TaintCert (C : TaintEnv) (c : UCmd) (C' : TaintEnv) (Ks : List Nat) : Prop where
  env  : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    TaintInv C s → uexec n c π s = some r → TaintInv C' r.1
  sink : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    TaintInv C s → uexec n c π s = some r →
    ∀ t ∈ r.1.sink, t ∈ s.sink ∨ qcount t.2 ∈ Ks

/-! ### Commands that do not touch strings -/

/-- A command that touches neither the string store nor the sink, and cannot resurrect
    a dead run. Named rather than inlined so the *path* certificate of stage 1q can
    reuse the same five proofs. -/
def StringInert (c : UCmd) : Prop :=
  ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    uexec n c π s = some r →
      r.1.sstore = s.sstore ∧ r.1.sink = s.sink ∧ (r.1.dead = false → s.dead = false)

theorem TaintCert.inert {C : TaintEnv} {c : UCmd} (h : StringInert c) :
    TaintCert C c C [] :=
  ⟨fun n π s r hinv hr => by
      intro hd p hp
      rw [(h n π s r hr).1]
      exact hinv ((h n π s r hr).2.2 hd) p hp,
   fun n π s r _ hr t ht => Or.inl (by rwa [(h n π s r hr).2.1] at ht)⟩

theorem StringInert.skip  : StringInert (.skip) := by
    intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; exact ⟨by simp, by simp, id⟩

theorem TaintCert.skip {C : TaintEnv} : TaintCert C (.skip) C [] :=
  TaintCert.inert (StringInert.skip)

theorem StringInert.assign (x : String) (e : Expr) : StringInert (.assign x e) := by
    intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd]; exact ⟨by simp, by simp, id⟩
        · simp only [if_neg hd]; exact ⟨by simp, by simp, fun _ => by simpa using hd⟩

theorem TaintCert.assign {C : TaintEnv} (x : String) (e : Expr) :
    TaintCert C (.assign x e) C [] :=
  TaintCert.inert (StringInert.assign x e)

theorem StringInert.check (q : String) : StringInert ((.check q)) := by
    intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd]; exact ⟨by simp, by simp, id⟩
        · simp only [if_neg hd]
          by_cases hp : π q = true
          · simp only [if_pos hp]; exact ⟨by simp, by simp, fun _ => by simpa using hd⟩
          · simp only [if_neg hp]; exact ⟨by simp, by simp, fun h => absurd h (by simp)⟩

theorem TaintCert.check {C : TaintEnv} (q : String) : TaintCert C ((.check q)) C [] :=
  TaintCert.inert (StringInert.check q)

theorem StringInert.access (q : String) : StringInert ((.access q)) := by
    intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd]; exact ⟨by simp, by simp, id⟩
        · simp only [if_neg hd]; exact ⟨by simp, by simp, fun _ => by simpa using hd⟩

theorem TaintCert.access {C : TaintEnv} (q : String) : TaintCert C ((.access q)) C [] :=
  TaintCert.inert (StringInert.access q)

theorem StringInert.memop (op : MemOp) (x : String) : StringInert (.memop op x) := by
    intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd]; exact ⟨by simp, by simp, id⟩
        · simp only [if_neg hd]
          cases op with
          | alloc => exact ⟨by simp, by simp, fun _ => by simpa using hd⟩
          | allocS => exact ⟨by simp, by simp, fun _ => by simpa using hd⟩
          | deref =>
              by_cases hl : memInt (s.store x) s.live = true
              · simp only [if_pos hl]; exact ⟨by simp, by simp, fun _ => by simpa using hd⟩
              · simp only [if_neg hl]; exact ⟨by simp, by simp, fun h => absurd h (by simp)⟩
          | free =>
              by_cases hl : memInt (s.store x) s.live = true
              · simp only [if_pos hl]; exact ⟨by simp, by simp, fun _ => by simpa using hd⟩
              · simp only [if_neg hl]; exact ⟨by simp, by simp, fun h => absurd h (by simp)⟩

theorem TaintCert.memop {C : TaintEnv} (op : MemOp) (x : String) :
    TaintCert C (.memop op x) C [] :=
  TaintCert.inert (StringInert.memop op x)

theorem StringInert.hop (op : HOp) (x y : String) : StringInert (.hop op x y) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨by simp, by simp, id⟩
      · simp only [if_neg hd]
        cases op with
        | load =>
            by_cases hl : memInt (s.store y) s.live = true
            · simp only [if_pos hl]; exact ⟨by simp, by simp, fun _ => by simpa using hd⟩
            · simp only [if_neg hl]; exact ⟨by simp, by simp, fun h => absurd h (by simp)⟩
        | store =>
            by_cases hl : memInt (s.store x) s.live = true
            · simp only [if_pos hl]; exact ⟨by simp, by simp, fun _ => by simpa using hd⟩
            · simp only [if_neg hl]; exact ⟨by simp, by simp, fun h => absurd h (by simp)⟩

theorem TaintCert.hop {C : TaintEnv} (op : HOp) (x y : String) :
    TaintCert C (.hop op x y) C [] :=
  TaintCert.inert (StringInert.hop op x y)

/-! ### The two string rules -/

/-- Assigning to a string variable records its new count — or forgets the variable if
    the count cannot be pinned down. Forgetting is always available, so `set` never
    fails; it is `emit` that has an obligation. -/
theorem TaintCert.set {C : TaintEnv} (x : String) (e : SExpr) (k : Nat)
    (hk : scount C e = some k) :
    TaintCert C (.sop .set x e) ((x, k) :: dropPair x C) [] := by
  constructor
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd]
          intro hc
          exact absurd (hd ▸ hc) (by simp)
        · have hd0 : s.dead = false := by simpa using hd
          simp only [if_neg hd]
          intro _ p hp
          rcases List.mem_cons.mp hp with h' | h'
          · subst h'
            show qcount (updSU s.sstore x (evalS s.sstore e) x) = k
            simp only [updSU, if_pos rfl]
            exact scount_sound (hinv hd0) e k hk
          · have hne : ¬ (p.1 = x) := dropPair_ne h'
            show qcount (updSU s.sstore x (evalS s.sstore e) p.1) = p.2
            simp only [updSU, if_neg hne]
            exact hinv hd0 p (dropPair_mem h')
  · intro n π s r _ hr t ht
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd] at ht; exact Or.inl ht
        · simp only [if_neg hd] at ht; exact Or.inl ht

/-- Assigning a value whose count cannot be pinned down simply *forgets* the variable.
    So `set` never fails — the obligation is entirely on `emit`, which is where an
    injection actually happens. -/
theorem TaintCert.setUnknown {C : TaintEnv} (x : String) (e : SExpr) :
    TaintCert C (.sop .set x e) (dropPair x C) [] := by
  constructor
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd]; intro hc; exact absurd (hd ▸ hc) (by simp)
        · have hd0 : s.dead = false := by simpa using hd
          simp only [if_neg hd]
          intro _ p hp
          have hne : ¬ (p.1 = x) := dropPair_ne hp
          show qcount (updSU s.sstore x (evalS s.sstore e) p.1) = p.2
          simp only [updSU, if_neg hne]
          exact hinv hd0 p (dropPair_mem hp)
  · intro n π s r _ hr t ht
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd] at ht; exact Or.inl ht
        · simp only [if_neg hd] at ht; exact Or.inl ht

/-- **The rule with the obligation.** Emitting is allowed only when the delimiter count
    of the expression is *known*, and then the emitted string carries exactly that
    many. An expression mentioning an unrecorded variable has no count, so it cannot be
    emitted — that is the refusal that stops injection. -/
theorem TaintCert.emit {C : TaintEnv} (q : String) (e : SExpr) (k : Nat)
    (hk : scount C e = some k) : TaintCert C (.sop .emit q e) C [k] := by
  constructor
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd]; exact hinv
        · simp only [if_neg hd]; exact hinv
  · intro n π s r hinv hr t ht
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr; subst hr
        by_cases hd : s.dead = true
        · simp only [if_pos hd] at ht; exact Or.inl ht
        · have hd0 : s.dead = false := by simpa using hd
          simp only [if_neg hd] at ht
          rcases List.mem_cons.mp ht with h' | h'
          · exact Or.inr (by rw [h', scount_sound (hinv hd0) e k hk]; simp)
          · exact Or.inl h'

/-! ### Composition -/

theorem TaintCert.seq {C C₁ C₂ : TaintEnv} {c₁ c₂ : UCmd} {K₁ K₂ : List Nat}
    (h₁ : TaintCert C c₁ C₁ K₁) (h₂ : TaintCert C₁ c₂ C₂ K₂) :
    TaintCert C (.seq c₁ c₂) C₂ (K₁ ++ K₂) := by
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
            rcases h₂.sink n π r₁.1 r₂ hi₁ e₂ t ht with h' | h'
            · rcases h₁.sink n π s r₁ hinv e₁ t h' with h'' | h''
              · exact Or.inl h''
              · exact Or.inr (by simp [h''])
            · exact Or.inr (by simp [h'])

theorem TaintCert.ite {C C₁ C₂ : TaintEnv} {e : Expr} {c₁ c₂ : UCmd} {K₁ K₂ : List Nat}
    (h₁ : TaintCert C c₁ C₁ K₁) (h₂ : TaintCert C c₂ C₂ K₂) :
    TaintCert C (.ite e c₁ c₂) (interNat C₁ C₂) (K₁ ++ K₂) := by
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
            rcases h₁.sink n π s r₁ hinv e₁ t ht with h' | h'
            · exact Or.inl h'
            · exact Or.inr (by simp [h'])
        · rw [if_neg hg] at hr
          rcases e₂ : uexec n c₂ π s with _ | r₂
          · rw [e₂] at hr; simp at hr
          · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            rcases h₂.sink n π s r₂ hinv e₂ t ht with h' | h'
            · exact Or.inl h'
            · exact Or.inr (by simp [h'])

/-! ## The checker -/

def tcheck (C : TaintEnv) : UCmd → Option (TaintEnv × List Nat)
  | .skip          => some (C, [])
  | .assign _ _    => some (C, [])
  | .check _       => some (C, [])
  | .access _      => some (C, [])
  | .memop _ _     => some (C, [])
  | .hop _ _ _     => some (C, [])
  | .sop .set x e  => match scount C e with
                      | some k => some ((x, k) :: dropPair x C, [])
                      | none   => some (dropPair x C, [])
  | .sop .emit _ e => match scount C e with
                      | some k => some (C, [k])
                      | none   => none
  | .seq c₁ c₂     => (tcheck C c₁).bind fun p₁ =>
                        (tcheck p₁.1 c₂).map fun p₂ => (p₂.1, p₁.2 ++ p₂.2)
  | .ite _ c₁ c₂   => match tcheck C c₁, tcheck C c₂ with
                      | some p₁, some p₂ => some (interNat p₁.1 p₂.1, p₁.2 ++ p₂.2)
                      | _, _ => none
  | .loop _ _      => none   -- see the scope note in the header

theorem tcheck_sound : ∀ (c : UCmd) (C C' : TaintEnv) (Ks : List Nat),
    tcheck C c = some (C', Ks) → TaintCert C c C' Ks
  | .skip, C, C', Ks, h => by
      simp only [tcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact TaintCert.skip
  | .assign x e, C, C', Ks, h => by
      simp only [tcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact TaintCert.assign x e
  | .check q, C, C', Ks, h => by
      simp only [tcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact TaintCert.check q
  | .access q, C, C', Ks, h => by
      simp only [tcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact TaintCert.access q
  | .memop op x, C, C', Ks, h => by
      simp only [tcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact TaintCert.memop op x
  | .hop op x y, C, C', Ks, h => by
      simp only [tcheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact TaintCert.hop op x y
  | .sop .set x e, C, C', Ks, h => by
      simp only [tcheck] at h
      rcases hk : scount C e with _ | k
      · rw [hk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact TaintCert.setUnknown x e
      · rw [hk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact TaintCert.set x e k hk
  | .sop .emit q e, C, C', Ks, h => by
      simp only [tcheck] at h
      rcases hk : scount C e with _ | k
      · rw [hk] at h; simp at h
      · rw [hk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact TaintCert.emit q e k hk
  | .seq c₁ c₂, C, C', Ks, h => by
      simp only [tcheck] at h
      rcases e₁ : tcheck C c₁ with _ | p₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        rcases e₂ : tcheck p₁.1 c₂ with _ | p₂
        · rw [e₂] at h; simp at h
        · rw [e₂] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact TaintCert.seq (tcheck_sound c₁ C p₁.1 p₁.2 (by rw [e₁]))
                              (tcheck_sound c₂ p₁.1 p₂.1 p₂.2 (by rw [e₂]))
  | .ite e c₁ c₂, C, C', Ks, h => by
      simp only [tcheck] at h
      rcases e₁ : tcheck C c₁ with _ | p₁
      · rw [e₁] at h; simp at h
      · rcases e₂ : tcheck C c₂ with _ | p₂
        · rw [e₁, e₂] at h; simp at h
        · rw [e₁, e₂] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact TaintCert.ite (tcheck_sound c₁ C p₁.1 p₁.2 (by rw [e₁]))
                              (tcheck_sound c₂ C p₂.1 p₂.2 (by rw [e₂]))
  | .loop _ _, _, _, _, h => by simp [tcheck] at h

/-- The general form: from any state whose sink starts empty. The empty environment
    is satisfied by *every* state, so nothing is assumed about the attacker's input. -/
theorem tcheck_no_injection_from {c : UCmd} {C' : TaintEnv} {Ks : List Nat}
    (h : tcheck [] c = some (C', Ks)) :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n c π s = some r → ∀ t ∈ r.1.sink, qcount t.2 ∈ Ks := by
  intro n π s r hs hr t ht
  have hinv : TaintInv [] s := by intro _ p hp; simp at hp
  rcases (tcheck_sound c [] C' Ks h).sink n π s r hinv hr t ht with h' | h'
  · rw [hs] at h'; simp at h'
  · exact h'

/-- **Structural integrity.** Every string a checked program emits carries a delimiter
    count the analysis predicted. Untrusted input cannot change the shape of the
    query — which is what an injection *is*. -/
theorem tcheck_no_injection {c : UCmd} {C' : TaintEnv} {Ks : List Nat}
    (h : tcheck [] c = some (C', Ks)) :
    ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n c π (initU σ) = some r → ∀ t ∈ r.1.sink, qcount t.2 ∈ Ks := by
  intro n π σ r hr t ht
  have hinv : TaintInv [] (initU σ) := by intro _ p hp; simp at hp
  rcases (tcheck_sound c [] C' Ks h).sink n π (initU σ) r hinv hr t ht with h' | h'
  · simp [initU] at h'
  · exact h'


/-! ## The row: a real attack, a refusal, and a fix that survives it -/

/-- `... name = ' INPUT '` — the untrusted value spliced straight in. -/
def vulnQuery : UCmd :=
  .seq (.sop .set "q" (.cat (.lit [.ord, .quote]) (.cat (.var "input") (.lit [.quote]))))
       (.sop .emit "db" (.var "q"))

/-- The same query with the one available discharge applied. -/
def safeQuery : UCmd :=
  .seq (.sop .set "q" (.cat (.lit [.ord, .quote])
                        (.cat (.san (.var "input")) (.lit [.quote]))))
       (.sop .emit "db" (.var "q"))

/-- An input carrying a delimiter: the attack payload, in this alphabet. -/
def attackState : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false, heap := fun _ => 0,
    live := [], fresh := 0, err := false, freed := [], hlab := fun _ => false,
    sstore := fun y => if y == "input" then [UCh.quote] else [], sink := [] }

/-- **The attack is real.** Run the vulnerable program on the malicious input and the
    emitted string carries **three** delimiters where the query's author wrote two. The
    shape of the query changed — that is the injection, not a proxy for it. -/
theorem injection_is_real :
    ((uexec 3 vulnQuery (fun _ => true) attackState).map
      (fun r => r.1.sink.map (fun p => qcount p.2))) = some [3]
  ∧ ((uexec 3 safeQuery (fun _ => true) attackState).map
      (fun r => r.1.sink.map (fun p => qcount p.2))) = some [2] := by decide

/-- **And the checker refuses it.** The count of `var "input"` is unknown, so the
    concatenation has no count, so `q` is forgotten and the emit has no rule to appeal
    to. The refusal lands on the `emit` — where the injection happens — rather than on
    the assignment. -/
theorem injection_rejected : tcheck [] vulnQuery = none := by decide

/-- **The fix checks**, and the analysis pins the count at two. -/
theorem sanitised_query_checks : tcheck [] safeQuery = some ([("q", 2)], [2]) := by decide

/-- **And the guarantee is not about one input.** For *every* state with an empty sink
    — every attacker input, however chosen — the sanitised query emits strings with
    exactly two delimiters. `injection_is_real` shows the vulnerable version failing
    this on a concrete payload. -/
theorem sanitised_query_holds_under_every_input :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n safeQuery π s = some r → ∀ t ∈ r.1.sink, qcount t.2 = 2 := by
  intro n π s r hs hr t ht
  have := tcheck_no_injection_from sanitised_query_checks n π s r hs hr t ht
  simpa using this

/-- The three together, as the row asks: the attack succeeds on the vulnerable program,
    the checker rejects it, and the fix is accepted and holds under the same payload. -/
theorem injection_row :
    ((uexec 3 vulnQuery (fun _ => true) attackState).map
      (fun r => r.1.sink.map (fun p => qcount p.2))) = some [3]
  ∧ tcheck [] vulnQuery = none
  ∧ tcheck [] safeQuery = some ([("q", 2)], [2])
  ∧ (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        s.sink = [] → uexec n safeQuery π s = some r → ∀ t ∈ r.1.sink, qcount t.2 = 2) :=
  ⟨injection_is_real.1, injection_rejected, sanitised_query_checks,
   sanitised_query_holds_under_every_input⟩

/-- Sanitising is the *only* discharge, and it is not vacuous: `san` really does remove
    every delimiter, whatever the input. -/
theorem sanitisation_is_the_discharge (t : UStr) : qcount (sanStr t) = 0 :=
  qcount_sanStr t

end ConfTyping
