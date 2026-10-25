/-
  Injection in a running program — brick 15: the taint-flow linter.

  Brick 14 made injection real for two `build` functions in the abstract. This
  brick connects it to an actual *program*: untrusted input flows through
  variables and string concatenation to a query sink, and a flow-sensitive
  **taint checker** decides whether the emitted query can be influenced by the
  input. The soundness theorem is real injection-freedom: an accepted program
  emits the *same* query command structure for *every* untrusted input.

  This is the shape of a real static analyzer for SQL injection — the kind that
  flags `q = "… WHERE n='" + name + "'"; exec(q)` and blesses
  `exec_param("… WHERE n=?", name)` — with the flagging proved sound.

  * `qexec` runs a string-manipulating program (`input`, `lit`, `concat`,
    `emitC` = emit a built query, `emitP` = emit a parameterized query) against
    an untrusted input, accumulating the emitted command skeletons;
  * `qcheck` tracks the tainted variables and rejects `emitC` of a tainted
    query — the injectable sink — while always accepting `emitP`;
  * `qcheck_ni` proves the two-run noninterference: a checked program's emitted
    output is a function of the trusted program text alone, never the input;
  * `injection_free_of_check` is the top-level guarantee, and
    `unsafe_leaks`/`unsafe_rejected` the witness that a concatenated tainted
    query both leaks and is rejected.

  Variables are `Nat` identifiers (so the concrete witnesses reduce under
  `decide`); nothing else depends on the choice.
-/
import ConfTyping.InjectionReal

namespace ConfTyping

/-! ## The string-program machine -/

abbrev Var := Nat

/-- String-valued variable store. -/
abbrev QStore := Var → Str

def updS (σ : QStore) (x : Var) (v : Str) : QStore :=
  fun y => if y = x then v else σ y

/-- Remove a variable from a tainted set (filter-based, clean membership). -/
def vremove (x : Var) (T : List Var) : List Var := T.filter (fun y => decide (y ≠ x))

theorem mem_of_mem_vremove {z x : Var} {T} (h : z ∈ vremove x T) : z ∈ T :=
  (List.mem_filter.mp h).1

theorem ne_of_mem_vremove {z x : Var} {T} (h : z ∈ vremove x T) : z ≠ x := by
  have := (List.mem_filter.mp h).2; simpa using of_decide_eq_true this

theorem mem_vremove {z x : Var} {T} (h1 : z ∈ T) (h2 : z ≠ x) : z ∈ vremove x T :=
  List.mem_filter.mpr ⟨h1, by simp [h2]⟩

/-- Program state: the store and the list of emitted query skeletons (the
    observable sink). -/
structure QState where
  store : QStore
  out   : List (List Str)

/-- A string-manipulating program. `emitC` sends a built query string to the
    database (its skeleton is the executed command); `emitP` sends a
    parameterized query (the value is bound, structure fixed). -/
inductive QCmd where
  | lit    : Var → Str → QCmd            -- x := trusted literal
  | input  : Var → QCmd                  -- x := untrusted input
  | concat : Var → Var → Var → QCmd      -- x := y ++ z
  | emitC  : Var → QCmd                  -- emit skeleton of query x
  | emitP  : Str → Str → Var → QCmd      -- emit parameterized [pre,suf] binding x
  | seq    : QCmd → QCmd → QCmd

/-- Run a program against a fixed untrusted `inp`. -/
def qexec (inp : Str) : QCmd → QState → QState
  | .lit x s,      st => ⟨updS st.store x s, st.out⟩
  | .input x,      st => ⟨updS st.store x inp, st.out⟩
  | .concat x y z, st => ⟨updS st.store x (st.store y ++ st.store z), st.out⟩
  | .emitC x,      st => ⟨st.store, st.out ++ [skeleton (st.store x)]⟩
  | .emitP pre suf x, st => ⟨st.store, st.out ++ [paramStructure pre suf (st.store x)]⟩
  | .seq c₁ c₂,    st => qexec inp c₂ (qexec inp c₁ st)

/-! ## The taint checker -/

/-- Flow-sensitive taint: `qcheck T c` threads the set of tainted variables and
    returns `none` if `c` emits a tainted (injectable) query. -/
def qcheck (T : List Var) : QCmd → Option (List Var)
  | .lit x _      => some (vremove x T)
  | .input x      => some (x :: T)
  | .concat x y z =>
      some (if (decide (y ∈ T) || decide (z ∈ T)) then x :: T else vremove x T)
  | .emitC x      => if x ∈ T then none else some T
  | .emitP _ _ _  => some T
  | .seq c₁ c₂    => (qcheck T c₁).bind (fun T₁ => qcheck T₁ c₂)

/-! ## Soundness: checked programs are injection-free -/

/-- Two-run relation: untainted variables hold equal strings, and the emitted
    output so far agrees. -/
def QRel (T : List Var) (st st' : QState) : Prop :=
  (∀ x, x ∉ T → st.store x = st'.store x) ∧ st.out = st'.out

/-- **Noninterference of the emitted queries.** Running a checked program on two
    untrusted inputs from related states yields related states — in particular
    the emitted output is unchanged. The tainted set precisely bounds what the
    input can influence, and the sink (`emitC`) is gated on untainted data. -/
theorem qcheck_ni :
    ∀ (c : QCmd) (T T' : List Var) (inp inp' : Str) (st st' : QState),
      qcheck T c = some T' → QRel T st st' →
      QRel T' (qexec inp c st) (qexec inp' c st') := by
  intro c
  induction c with
  | lit x s =>
      intro T T' inp inp' st st' hchk hrel
      simp only [qcheck, Option.some.injEq] at hchk; subst hchk
      refine ⟨fun z hz => ?_, hrel.2⟩
      simp only [qexec, updS]
      by_cases hzx : z = x
      · rw [ite_eq_left hzx, ite_eq_left hzx]
      · rw [ite_eq_right hzx, ite_eq_right hzx]
        exact hrel.1 z (fun hzT => hz (mem_vremove hzT hzx))
  | input x =>
      intro T T' inp inp' st st' hchk hrel
      simp only [qcheck, Option.some.injEq] at hchk; subst hchk
      refine ⟨fun z hz => ?_, hrel.2⟩
      have hzx : z ≠ x := fun e => by rw [e] at hz; exact hz (by simp)
      have hzT : z ∉ T := fun h => hz (List.mem_cons_of_mem x h)
      simp only [qexec, updS, ite_eq_right hzx]
      exact hrel.1 z hzT
  | concat x y z =>
      intro T T' inp inp' st st' hchk hrel
      simp only [qcheck, Option.some.injEq] at hchk
      by_cases hyz : (decide (y ∈ T) || decide (z ∈ T)) = true
      · rw [ite_eq_left hyz] at hchk; subst hchk
        refine ⟨fun w hw => ?_, hrel.2⟩
        have hwx : w ≠ x := fun e => by rw [e] at hw; exact hw (by simp)
        have hwT : w ∉ T := fun h => hw (List.mem_cons_of_mem x h)
        simp only [qexec, updS, ite_eq_right hwx]
        exact hrel.1 w hwT
      · rw [ite_eq_right hyz] at hchk; subst hchk
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hyz
        refine ⟨fun w hw => ?_, hrel.2⟩
        simp only [qexec, updS]
        by_cases hwx : w = x
        · rw [ite_eq_left hwx, ite_eq_left hwx, hrel.1 y hyz.1, hrel.1 z hyz.2]
        · rw [ite_eq_right hwx, ite_eq_right hwx]
          exact hrel.1 w (fun hwT => hw (mem_vremove hwT hwx))
  | emitC x =>
      intro T T' inp inp' st st' hchk hrel
      simp only [qcheck] at hchk
      by_cases hxT : x ∈ T
      · rw [ite_eq_left hxT] at hchk; simp at hchk
      · rw [ite_eq_right hxT, Option.some.injEq] at hchk; subst hchk
        refine ⟨hrel.1, ?_⟩
        simp only [qexec]
        rw [hrel.2, hrel.1 x hxT]
  | emitP pre suf x =>
      intro T T' inp inp' st st' hchk hrel
      simp only [qcheck, Option.some.injEq] at hchk; subst hchk
      refine ⟨hrel.1, ?_⟩
      simp only [qexec, paramStructure]
      rw [hrel.2]
  | seq c₁ c₂ ih₁ ih₂ =>
      intro T T' inp inp' st st' hchk hrel
      simp only [qcheck, Option.bind_eq_bind] at hchk
      cases hT₁ : qcheck T c₁ with
      | none => rw [hT₁] at hchk; simp at hchk
      | some T₁ =>
          rw [hT₁, Option.bind_some] at hchk
          exact ih₂ T₁ T' inp inp' _ _ hchk (ih₁ T T₁ inp inp' st st' hT₁ hrel)

/-- **Injection-freedom, top level.** A checked program emits the identical
    query command structure for *every* untrusted input — the executed commands
    are a function of the trusted program text alone. -/
theorem injection_free_of_check {c : QCmd} {T' : List Var}
    (h : qcheck [] c = some T') (inp inp' : Str) (σ₀ : QStore) :
    (qexec inp c ⟨σ₀, []⟩).out = (qexec inp' c ⟨σ₀, []⟩).out :=
  (qcheck_ni c [] T' inp inp' ⟨σ₀, []⟩ ⟨σ₀, []⟩ h ⟨fun _ _ => rfl, rfl⟩).2

/-! ## Witnesses: the injectable program is caught -/

/-- The unsafe program: read input into `0`, concatenate it after a template
    `1`, emit the built query. This is `q = template + input; exec(q)`. -/
def Unsafe : QCmd :=
  .seq (.input 0)
    (.seq (.lit 1 [.c 1])
      (.seq (.concat 2 1 0) (.emitC 2)))

/-- **The checker rejects it** — the emitted query `2` is tainted (it
    concatenates the untrusted `0`). This is the injection warning. -/
theorem unsafe_rejected : qcheck [] Unsafe = none := by decide

/-- **And it really leaks.** Running `Unsafe` on a benign input vs. an injection
    payload `' R` emits different query skeletons — the untrusted input changed
    the executed command. So the checker's rejection is warranted. -/
theorem unsafe_leaks :
    (qexec [.c 0] Unsafe ⟨fun _ => [], []⟩).out
      ≠ (qexec [.q, .c 3] Unsafe ⟨fun _ => [], []⟩).out := by decide

/-- The safe program: read input into `0`, emit it as a *parameterized* query.
    This is `exec_param(template, input)`. -/
def Safe : QCmd :=
  .seq (.input 0) (.emitP [.c 1] [.c 2] 0)

/-- **The checker accepts it**, and (by `injection_free_of_check`) it is
    injection-free: the emitted query is the same for every input. -/
theorem safe_accepted : (qcheck [] Safe).isSome = true := by decide

theorem safe_injection_free (inp inp' : Str) (σ₀ : QStore) :
    (qexec inp Safe ⟨σ₀, []⟩).out = (qexec inp' Safe ⟨σ₀, []⟩).out := by
  obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.mp safe_accepted
  exact injection_free_of_check hT' inp inp' σ₀

end ConfTyping
