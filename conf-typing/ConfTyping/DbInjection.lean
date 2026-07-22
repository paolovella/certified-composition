/-
  Stored / second-order injection — brick 16: taint that persists.

  Brick 15's taint checker handles injection within one request: input flows
  through variables to a query sink. But the sharpest, most commonly-missed
  injection class is **stored (second-order) injection**: untrusted data is
  written to the database in one request, then read back in a later request and
  concatenated into a query — where a per-request analysis has forgotten it was
  ever tainted.

  This brick extends the machine with a **persistent store** (`db`) and proves
  two things:
  * a **naive** checker that treats database reads as fresh/untrusted-free
    (`dbcheckNaive`) *accepts* a stored-injection program that genuinely leaks
    (`naive_accepts_stored` + `stored_injection_leaks`) — it is **unsound**;
  * the **sound** checker (`dbcheck`) tracks taint *per database cell* — a cell
    is tainted once tainted data is written to it, and a read of a tainted cell
    yields a tainted variable — so it *rejects* the stored-injection program
    (`sound_rejects_stored`), and its acceptance is proved injection-free across
    the persistent store (`dbcheck_ni`, `db_injection_free_of_check`).

  The moral, as a theorem: injection-freedom does not survive persistence unless
  taint does — the discipline that catches second-order injection is exactly
  per-cell taint tracking, and the per-request shortcut is unsound.
-/
import ConfTyping.InjectionReal

namespace ConfTyping

/-! ## The machine with a persistent store -/

abbrev Loc := Nat   -- variable and cell identifiers

def updN (σ : Loc → Str) (x : Loc) (v : Str) : Loc → Str :=
  fun y => if y = x then v else σ y

def lrem (x : Loc) (T : List Loc) : List Loc := T.filter (fun y => decide (y ≠ x))

theorem mem_of_mem_lrem {z x : Loc} {T} (h : z ∈ lrem x T) : z ∈ T :=
  (List.mem_filter.mp h).1
theorem mem_lrem {z x : Loc} {T} (h1 : z ∈ T) (h2 : z ≠ x) : z ∈ lrem x T :=
  List.mem_filter.mpr ⟨h1, by simp [h2]⟩

/-- Request-local variables, a persistent database, and the emitted queries. -/
structure DbState where
  store : Loc → Str
  db    : Loc → Str
  out   : List (List Str)

/-- Commands, now with `dbwrite`/`dbread` crossing the persistence boundary. -/
inductive DCmd where
  | input   : Loc → DCmd
  | lit     : Loc → Str → DCmd
  | concat  : Loc → Loc → Loc → DCmd
  | dbwrite : Loc → Loc → DCmd          -- db[k] := store[x]
  | dbread  : Loc → Loc → DCmd          -- store[x] := db[k]
  | emitC   : Loc → DCmd
  | emitP   : Str → Str → Loc → DCmd
  | seq     : DCmd → DCmd → DCmd

def dexec (inp : Str) : DCmd → DbState → DbState
  | .input x,      s => ⟨updN s.store x inp, s.db, s.out⟩
  | .lit x v,      s => ⟨updN s.store x v, s.db, s.out⟩
  | .concat x y z, s => ⟨updN s.store x (s.store y ++ s.store z), s.db, s.out⟩
  | .dbwrite k x,  s => ⟨s.store, updN s.db k (s.store x), s.out⟩
  | .dbread x k,   s => ⟨updN s.store x (s.db k), s.db, s.out⟩
  | .emitC x,      s => ⟨s.store, s.db, s.out ++ [skeleton (s.store x)]⟩
  | .emitP pre suf x, s => ⟨s.store, s.db, s.out ++ [paramStructure pre suf (s.store x)]⟩
  | .seq c₁ c₂,    s => dexec inp c₂ (dexec inp c₁ s)

/-! ## The sound checker: taint persists per cell -/

/-- Checker state: tainted variables `T` and tainted cells `D`. -/
def dbcheck : List Loc × List Loc → DCmd → Option (List Loc × List Loc)
  | (T, D), .input x      => some (x :: T, D)
  | (T, D), .lit x _      => some (lrem x T, D)
  | (T, D), .concat x y z =>
      some (if (decide (y ∈ T) || decide (z ∈ T)) then x :: T else lrem x T, D)
  | (T, D), .dbwrite k x  => some (T, if x ∈ T then k :: D else lrem k D)
  | (T, D), .dbread x k   => some (if k ∈ D then x :: T else lrem x T, D)  -- KEY: read of tainted cell taints
  | (T, D), .emitC x      => if x ∈ T then none else some (T, D)
  | (T, D), .emitP _ _ _  => some (T, D)
  | TD,     .seq c₁ c₂    => (dbcheck TD c₁).bind (fun TD₁ => dbcheck TD₁ c₂)

/-! ## Soundness across persistence -/

/-- Two-run relation: untainted variables and untainted cells hold equal
    strings, and the emitted output agrees. -/
def DbRel (TD : List Loc × List Loc) (s s' : DbState) : Prop :=
  (∀ x, x ∉ TD.1 → s.store x = s'.store x) ∧
  (∀ k, k ∉ TD.2 → s.db k = s'.db k) ∧
  s.out = s'.out

theorem dbcheck_ni :
    ∀ (c : DCmd) (TD TD' : List Loc × List Loc) (inp inp' : Str) (s s' : DbState),
      dbcheck TD c = some TD' → DbRel TD s s' →
      DbRel TD' (dexec inp c s) (dexec inp' c s') := by
  intro c
  induction c with
  | input x =>
      intro ⟨T, D⟩ TD' inp inp' s s' hchk hrel
      simp only [dbcheck, Option.some.injEq] at hchk; subst hchk
      refine ⟨fun z hz => ?_, hrel.2.1, hrel.2.2⟩
      have hzx : z ≠ x := fun e => by rw [e] at hz; exact hz (by simp)
      have hzT : z ∉ T := fun h => hz (List.mem_cons_of_mem x h)
      simp only [dexec, updN, if_neg hzx]; exact hrel.1 z hzT
  | lit x v =>
      intro ⟨T, D⟩ TD' inp inp' s s' hchk hrel
      simp only [dbcheck, Option.some.injEq] at hchk; subst hchk
      refine ⟨fun z hz => ?_, hrel.2.1, hrel.2.2⟩
      simp only [dexec, updN]
      by_cases hzx : z = x
      · rw [if_pos hzx, if_pos hzx]
      · rw [if_neg hzx, if_neg hzx]
        exact hrel.1 z (fun hzT => hz (mem_lrem hzT hzx))
  | concat x y z =>
      intro ⟨T, D⟩ TD' inp inp' s s' hchk hrel
      simp only [dbcheck, Option.some.injEq] at hchk
      by_cases hyz : (decide (y ∈ T) || decide (z ∈ T)) = true
      · rw [if_pos hyz] at hchk; subst hchk
        refine ⟨fun w hw => ?_, hrel.2.1, hrel.2.2⟩
        have hwx : w ≠ x := fun e => by rw [e] at hw; exact hw (by simp)
        have hwT : w ∉ T := fun h => hw (List.mem_cons_of_mem x h)
        simp only [dexec, updN, if_neg hwx]; exact hrel.1 w hwT
      · rw [if_neg hyz] at hchk; subst hchk
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hyz
        refine ⟨fun w hw => ?_, hrel.2.1, hrel.2.2⟩
        simp only [dexec, updN]
        by_cases hwx : w = x
        · rw [if_pos hwx, if_pos hwx, hrel.1 y hyz.1, hrel.1 z hyz.2]
        · rw [if_neg hwx, if_neg hwx]
          exact hrel.1 w (fun hwT => hw (mem_lrem hwT hwx))
  | dbwrite k x =>
      intro ⟨T, D⟩ TD' inp inp' s s' hchk hrel
      simp only [dbcheck, Option.some.injEq] at hchk
      by_cases hxT : x ∈ T
      · rw [if_pos hxT] at hchk; subst hchk
        refine ⟨hrel.1, fun j hj => ?_, hrel.2.2⟩
        have hjk : j ≠ k := fun e => by rw [e] at hj; exact hj (by simp)
        have hjD : j ∉ D := fun h => hj (List.mem_cons_of_mem k h)
        simp only [dexec, updN, if_neg hjk]; exact hrel.2.1 j hjD
      · rw [if_neg hxT] at hchk; subst hchk
        refine ⟨hrel.1, fun j hj => ?_, hrel.2.2⟩
        simp only [dexec, updN]
        by_cases hjk : j = k
        · rw [if_pos hjk, if_pos hjk, hrel.1 x hxT]
        · rw [if_neg hjk, if_neg hjk]
          exact hrel.2.1 j (fun hjD => hj (mem_lrem hjD hjk))
  | dbread x k =>
      intro ⟨T, D⟩ TD' inp inp' s s' hchk hrel
      simp only [dbcheck, Option.some.injEq] at hchk
      by_cases hkD : k ∈ D
      · rw [if_pos hkD] at hchk; subst hchk
        refine ⟨fun z hz => ?_, hrel.2.1, hrel.2.2⟩
        have hzx : z ≠ x := fun e => by rw [e] at hz; exact hz (by simp)
        have hzT : z ∉ T := fun h => hz (List.mem_cons_of_mem x h)
        simp only [dexec, updN, if_neg hzx]; exact hrel.1 z hzT
      · rw [if_neg hkD] at hchk; subst hchk
        refine ⟨fun z hz => ?_, hrel.2.1, hrel.2.2⟩
        simp only [dexec, updN]
        by_cases hzx : z = x
        · rw [if_pos hzx, if_pos hzx, hrel.2.1 k hkD]
        · rw [if_neg hzx, if_neg hzx]
          exact hrel.1 z (fun hzT => hz (mem_lrem hzT hzx))
  | emitC x =>
      intro ⟨T, D⟩ TD' inp inp' s s' hchk hrel
      simp only [dbcheck] at hchk
      by_cases hxT : x ∈ T
      · rw [if_pos hxT] at hchk; simp at hchk
      · rw [if_neg hxT, Option.some.injEq] at hchk; subst hchk
        refine ⟨hrel.1, hrel.2.1, ?_⟩
        simp only [dexec]; rw [hrel.2.2, hrel.1 x hxT]
  | emitP pre suf x =>
      intro ⟨T, D⟩ TD' inp inp' s s' hchk hrel
      simp only [dbcheck, Option.some.injEq] at hchk; subst hchk
      refine ⟨hrel.1, hrel.2.1, ?_⟩
      simp only [dexec, paramStructure]; rw [hrel.2.2]
  | seq c₁ c₂ ih₁ ih₂ =>
      intro TD TD' inp inp' s s' hchk hrel
      simp only [dbcheck, Option.bind_eq_bind] at hchk
      cases hTD₁ : dbcheck TD c₁ with
      | none => rw [hTD₁] at hchk; simp at hchk
      | some TD₁ =>
          rw [hTD₁, Option.bind_some] at hchk
          exact ih₂ TD₁ TD' inp inp' _ _ hchk (ih₁ TD TD₁ inp inp' s s' hTD₁ hrel)

/-- **Injection-freedom across persistence.** A checked program emits the same
    queries for every untrusted input — even with data flowing through the
    database. -/
theorem db_injection_free_of_check {c : DCmd} {TD' : List Loc × List Loc}
    (h : dbcheck ([], []) c = some TD') (inp inp' : Str) (σ₀ δ₀ : Loc → Str) :
    (dexec inp c ⟨σ₀, δ₀, []⟩).out = (dexec inp' c ⟨σ₀, δ₀, []⟩).out :=
  (dbcheck_ni c ([], []) TD' inp inp' ⟨σ₀, δ₀, []⟩ ⟨σ₀, δ₀, []⟩ h
    ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩).2.2

/-! ## The unsound shortcut: a per-request checker that ignores stored taint -/

/-- A **naive** checker: identical to `dbcheck` except a database read is treated
    as producing fresh, untainted data (the per-request bug — it forgets what
    was stored). Everything else is the same. -/
def dbcheckNaive : List Loc × List Loc → DCmd → Option (List Loc × List Loc)
  | (T, D), .input x      => some (x :: T, D)
  | (T, D), .lit x _      => some (lrem x T, D)
  | (T, D), .concat x y z =>
      some (if (decide (y ∈ T) || decide (z ∈ T)) then x :: T else lrem x T, D)
  | (T, D), .dbwrite _ _  => some (T, D)
  | (T, D), .dbread x _   => some (lrem x T, D)   -- BUG: read is always "clean"
  | (T, D), .emitC x      => if x ∈ T then none else some (T, D)
  | (T, D), .emitP _ _ _  => some (T, D)
  | TD,     .seq c₁ c₂    => (dbcheckNaive TD c₁).bind (fun TD₁ => dbcheckNaive TD₁ c₂)

/-! ## The stored-injection witness -/

/-- Second-order injection: store the untrusted input in cell 100, read it back
    into variable 1 in a "later request", concatenate it into a query, emit.
    `input 0; dbwrite 100 0; dbread 1 100; concat 2 3 1; emitC 2`, where var 3
    is a trusted template literal. -/
def Stored : DCmd :=
  .seq (.input 0)
    (.seq (.dbwrite 100 0)
      (.seq (.lit 3 [.c 1])
        (.seq (.dbread 1 100)
          (.seq (.concat 2 3 1) (.emitC 2)))))

/-- **The naive checker accepts it** — it forgot the data was tainted when it
    came back out of the database. This is the missed second-order injection. -/
theorem naive_accepts_stored : (dbcheckNaive ([], []) Stored).isSome = true := by decide

/-- **The sound checker rejects it** — cell 100 is tainted at the write, so the
    read taints variable 1, the concat taints the query, and the emit is
    flagged. Per-cell taint catches what the per-request shortcut misses. -/
theorem sound_rejects_stored : dbcheck ([], []) Stored = none := by decide

/-- **And it really leaks.** A benign input vs. an injection payload `' R`,
    routed through the database, emit different query skeletons — so the naive
    checker's acceptance is genuinely unsound and the sound checker is right to
    reject. -/
theorem stored_injection_leaks :
    (dexec [.c 0] Stored ⟨fun _ => [], fun _ => [], []⟩).out
      ≠ (dexec [.q, .c 3] Stored ⟨fun _ => [], fun _ => [], []⟩).out := by decide

end ConfTyping
