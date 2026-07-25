/-
  A second real sink — brick 27: OS command injection (CWE-78).

  Brick 17 showed that brick 14's "make a channel real" method is not
  injection-specific by re-running it for path traversal. This brick adds a
  *third* real sink and a genuinely different metacharacter, closing one of the
  named "more sink classes" follow-ons: **OS command injection**.

  A shell command string is tokenized into an argument vector (`argv`) by
  splitting on the **argument separator** (a space): `n` separators give `n+1`
  arguments, `argv[0]` the program and the rest its arguments. As with SQL, the
  *executed structure* is the even-positioned (structural) argv elements — the
  program and the fixed argument positions — and an intended value lives in a
  data slot. Command injection is precisely **an untrusted value changing that
  structure**: a separator inside the value splits it into extra argv elements,
  displacing the structure. The space here plays the role the quote played for
  SQL.

  Two ways to build a command from a trusted program and an untrusted value:
  * **concatenation** splices the value as raw text and re-splits the whole
    thing — so a value containing a separator breaks out of its argument and
    injects structure (`cmd_concat_injectable`, the real CWE-78 mechanism);
  * **argv parameterization** binds the value as one opaque argv element that is
    never re-split — so the executed structure is a function of the program
    alone (`argv_immune`), and for benign values the two agree (`argv_correct`).

  The security statement is integrity noninterference with a real command sink:
  the executed structure must not depend on the untrusted value. Argv-binding
  satisfies it (`argv_noninterference`); concatenation does not
  (`cmd_concat_leaks`). Same discipline as SQL injection and path traversal —
  data must not become structure — now for a second, different channel.
-/
import ConfTyping.InjectionReal

namespace ConfTyping

/-! ## Characters, strings, and the argv splitter -/

/-- A command character: the argument separator (a space), or an ordinary
    character carrying a code. -/
inductive ACh where
  | sep : ACh          -- the argument separator (space)
  | c   : Nat → ACh    -- an ordinary character
deriving DecidableEq

abbrev AStr := List ACh

/-- Does the string contain a separator? -/
def hasSep : AStr → Bool
  | [] => false
  | .sep :: _ => true
  | .c _ :: r => hasSep r

/-- Split a command string into its argument vector on separators: `argvOf`
    returns the maximal separator-free runs (including empty ones), so `n`
    separators give `n+1` arguments — exactly how a shell parses
    `prog arg1 arg2`. -/
def argvOf : AStr → List AStr
  | [] => [[]]
  | .sep :: r => [] :: argvOf r
  | .c n :: r =>
      match argvOf r with
      | a :: as => (.c n :: a) :: as
      | []      => [[.c n]]

/-- The even-indexed argv elements (positions 0, 2, 4, …) — the structural ones. -/
def aevens : List AStr → List AStr
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: aevens xs

/-- The **executed structure**: the structural argv elements (the program and
    the fixed argument positions). Injection = the untrusted value changing this. -/
def cmdSkeleton (s : AStr) : List AStr := aevens (argvOf s)

/-! ## The two builds -/

/-- **Concatenation build.** Splice the untrusted value `v` after the trusted
    program with a separator, then hand the *whole string* to the splitter. This
    is the injectable one — `system("prog " + userInput)`. -/
def buildCmdConcat (prog v : AStr) : AStr := prog ++ .sep :: v

/-- **Argv-parameterized build.** The value is bound as one opaque argument; the
    executed structure is the program alone, *by construction independent of any
    separators inside the value*. This models `execv(prog, [value])`. -/
def argvParam (prog : AStr) (_v : AStr) : List AStr := [prog]

/-! ## Splitter lemmas -/

theorem argvOf_ne_nil (s : AStr) : argvOf s ≠ [] := by
  cases s with
  | nil => simp [argvOf]
  | cons ch r =>
      cases ch with
      | sep => simp [argvOf]
      | c n => simp only [argvOf]; cases argvOf r with
        | nil => simp
        | cons _ _ => simp

/-- A separator-free string is a single argument. -/
theorem argv_sepfree : ∀ {s : AStr}, hasSep s = false → argvOf s = [s]
  | [], _ => rfl
  | .sep :: _, h => by simp [hasSep] at h
  | .c n :: r, h => by
      have hr : hasSep r = false := by simpa [hasSep] using h
      simp only [argvOf, argv_sepfree hr]

/-- Splitting after a separator-free prefix: `argvOf (a ++ sep·b) = a :: argvOf b`. -/
theorem argv_append_sep : ∀ {a : AStr}, hasSep a = false → ∀ b : AStr,
    argvOf (a ++ .sep :: b) = a :: argvOf b
  | [], _, b => rfl
  | .sep :: _, h, _ => by simp [hasSep] at h
  | .c n :: a', h, b => by
      have hr : hasSep a' = false := by simpa [hasSep] using h
      simp only [List.cons_append, argvOf, argv_append_sep hr b]

/-! ## Argv parameterization is injection-safe -/

/-- **Argv-binding is immune to injection.** The executed structure does not
    depend on the untrusted value — true *by construction*, because the value is
    never re-split. -/
theorem argv_immune (prog v v' : AStr) :
    argvParam prog v = argvParam prog v' := rfl

/-- **Argv-binding computes the right command.** For a well-behaved
    (separator-free) value and program, the bound structure equals what a correct
    split of the concatenated command would produce — so parameterization is
    faithful, and stays immune when the value is adversarial. -/
theorem argv_correct {prog v : AStr}
    (hprog : hasSep prog = false) (hv : hasSep v = false) :
    cmdSkeleton (buildCmdConcat prog v) = argvParam prog v := by
  have h1 : argvOf (buildCmdConcat prog v) = [prog, v] := by
    show argvOf (prog ++ .sep :: v) = [prog, v]
    rw [argv_append_sep hprog v, argv_sepfree hv]
  simp only [cmdSkeleton, h1, aevens, argvParam]

/-- **Argv-binding satisfies integrity noninterference.** The executed structure
    is invariant under any change to the untrusted value. -/
theorem argv_noninterference (prog : AStr) :
    ∀ v v', argvParam prog v = argvParam prog v' :=
  fun v v' => argv_immune prog v v'

/-! ## Concatenation is injectable -/

/-- Witness data: a benign value, and an injection payload `x y` (a separator
    that breaks the argument, then more structural text — a second argument or,
    with a `;`-like separator, a second command). -/
def cBenign : AStr := [.c 0]
def cPayload : AStr := [.c 3, .sep, .c 4]   -- separator injects structure
def cProg : AStr := [.c 1]

/-- **Concatenation is injectable.** With the same trusted program, a benign
    value and a payload with a separator produce *different executed structures* —
    the payload's text lands in a new structural position and the real structure
    is displaced. OS command injection as a theorem. -/
theorem cmd_concat_injectable :
    cmdSkeleton (buildCmdConcat cProg cBenign) ≠ cmdSkeleton (buildCmdConcat cProg cPayload) := by
  decide

/-- The benign value yields the intended structure (just the program) — the
    injection is the *difference*, not mere nonequality. -/
theorem cmd_benign_correct : cmdSkeleton (buildCmdConcat cProg cBenign) = [cProg] := by
  decide

/-! ## Integrity noninterference, with a real command sink

    Two runs share the trusted program but may differ on the untrusted value.
    Command-injection-freedom is: the executed structure is the same — integrity
    noninterference, over a real command construction. -/

/-- **Concatenation violates integrity noninterference.** Some trusted program
    and two untrusted values give different executed structures — the untrusted
    input influences the trusted sink, exactly the CWE-78 leak. -/
theorem cmd_concat_leaks :
    ∃ (prog v v' : AStr),
      cmdSkeleton (buildCmdConcat prog v) ≠ cmdSkeleton (buildCmdConcat prog v') :=
  ⟨cProg, cBenign, cPayload, cmd_concat_injectable⟩

/-- **The by-construction fix, as integrity NI.** Argv-binding makes the executed
    structure a constant function of the untrusted value (High-invariant), i.e. it
    satisfies the taint form of injection-freedom T1 identifies as the unique
    admissible 2-safety formulation — here on a real command. The sink factors
    through the trusted program alone. -/
theorem argv_sink_trusted (prog : AStr) :
    ∃ f : Unit → List AStr, ∀ v, argvParam prog v = f () :=
  ⟨fun _ => [prog], fun _ => rfl⟩

end ConfTyping
