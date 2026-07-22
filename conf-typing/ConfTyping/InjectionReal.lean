/-
  Injection, for real — brick 14: the property shape becomes a query.

  Brick 1 handled injection as a *property shape*: T1 (`taint_is_JNI`) said the
  taint form of injection-freedom is integrity noninterference, T2
  (`blacklist_not_admissible`) said output blacklists fail A3. Honest, but
  abstract — there was no query, no parser, no quote. This brick makes the
  channel real.

  A query is a character string tokenized the way a database does it: a quote
  `'` toggles in/out of a string literal, so the string splits into alternating
  **structural** segments (keywords, operators — the command) and **data**
  segments (literal contents). The *skeleton* — the structural segments — is the
  executed command; injection is precisely **untrusted data changing the
  skeleton**.

  Two ways to build a query from a trusted template and an untrusted value:
  * **concatenation** splices the value as raw text and re-tokenizes the whole
    thing — so a value containing a quote breaks out of its literal and injects
    structure (`concat_injectable`, the real SQLi mechanism, `' OR '1'='1`);
  * **parameterization** binds the value as a data leaf that is never
    re-tokenized — so the skeleton is a function of the template alone
    (`param_immune`), and for benign values the two agree (`param_correct`).

  The security statement is integrity noninterference with a *real* sink: the
  executed skeleton must not depend on the untrusted value. Parameterization
  satisfies it (`param_noninterference`); concatenation does not
  (`concat_leaks`). This is T1's abstract "unique admissible 2-safety form of
  injection-freedom", now instantiated on an actual query construction — and the
  by-construction fix (prepared statements) proved correct.
-/
import ConfTyping.Integrity

namespace ConfTyping

/-! ## Characters, strings, and the tokenizer -/

/-- A character: a quote `'`, or an ordinary character carrying a code. -/
inductive Ch where
  | q : Ch            -- the quote `'`
  | c : Nat → Ch      -- an ordinary character
deriving DecidableEq

abbrev Str := List Ch

/-- Does the string contain a quote? -/
def hasQ : Str → Bool
  | [] => false
  | .q :: _ => true
  | .c _ :: r => hasQ r

/-- Tokenize into segments split on quotes: `segs` returns the maximal
    quote-free runs (including empty ones), so `n` quotes give `n+1` segments.
    Even-indexed segments are structural, odd-indexed are literal contents —
    exactly how a database parses `... = 'DATA' ...`. -/
def segs : Str → List Str
  | [] => [[]]
  | .q :: r => [] :: segs r
  | .c n :: r =>
      match segs r with
      | s :: ss => (.c n :: s) :: ss
      | [] => [[.c n]]

/-- The even-indexed elements (positions 0, 2, 4, …). -/
def evens : List Str → List Str
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evens xs

/-- The **skeleton**: the structural segments — the executed command. Injection
    = the untrusted value changing this. -/
def skeleton (s : Str) : List Str := evens (segs s)

/-! ## The two builds -/

/-- **Concatenation build.** Splice the untrusted value `v` between quotes into
    a trusted template `pre ... suf`, then hand the *whole string* to the
    tokenizer. This is the injectable one. -/
def buildConcat (pre suf v : Str) : Str := pre ++ (.q :: (v ++ (.q :: suf)))

/-- **Parameterized build.** The value is bound as an opaque data leaf; the
    executed structure is the template's two structural segments, *by
    construction independent of the value*. This models a prepared statement. -/
def paramStructure (pre suf : Str) (_v : Str) : List Str := [pre, suf]

/-! ## Tokenizer lemmas -/

theorem segs_ne_nil (s : Str) : segs s ≠ [] := by
  cases s with
  | nil => simp [segs]
  | cons ch r =>
      cases ch with
      | q => simp [segs]
      | c n => simp only [segs]; cases segs r with
        | nil => simp
        | cons _ _ => simp

/-- A quote-free string is a single segment. -/
theorem segs_qfree : ∀ {s : Str}, hasQ s = false → segs s = [s]
  | [], _ => rfl
  | .q :: _, h => by simp [hasQ] at h
  | .c n :: r, h => by
      have hr : hasQ r = false := by simpa [hasQ] using h
      simp only [segs, segs_qfree hr]

/-- Splitting after a quote-free prefix: `segs (a ++ '·b) = a :: segs b`. -/
theorem segs_append_q : ∀ {a : Str}, hasQ a = false → ∀ b : Str,
    segs (a ++ .q :: b) = a :: segs b
  | [], _, b => rfl
  | .q :: _, h, _ => by simp [hasQ] at h
  | .c n :: a', h, b => by
      have hr : hasQ a' = false := by simpa [hasQ] using h
      simp only [List.cons_append, segs, segs_append_q hr b]

/-! ## Parameterization is injection-safe -/

/-- **Parameterization is immune to injection.** The executed structure does
    not depend on the untrusted value — the security property, true *by
    construction* because the value is never tokenized. -/
theorem param_immune (pre suf v v' : Str) :
    paramStructure pre suf v = paramStructure pre suf v' := rfl

/-- **Parameterization computes the right structure.** For a well-behaved
    (quote-free) value, the parameterized structure equals what a correct
    execution of the concatenated query would produce — so parameterization is
    not cheating by computing the wrong thing; it computes the intended
    structure, and stays immune when the value is adversarial. -/
theorem param_correct {pre suf v : Str}
    (hpre : hasQ pre = false) (hv : hasQ v = false) (hsuf : hasQ suf = false) :
    skeleton (buildConcat pre suf v) = paramStructure pre suf v := by
  have h1 : segs (buildConcat pre suf v) = pre :: v :: [suf] := by
    show segs (pre ++ .q :: (v ++ .q :: suf)) = _
    rw [segs_append_q hpre, segs_append_q hv, segs_qfree hsuf]
  simp only [skeleton, h1, evens, paramStructure]

/-! ## Concatenation is injectable -/

/-- Witness data: a benign value, and an injection payload `' R` (a quote that
    breaks out of the literal, then structural text). -/
def benign : Str := [.c 0]
def payload : Str := [.q, .c 3]        -- `'` then a structural char
def tPre : Str := [.c 1]
def tSuf : Str := [.c 2]

/-- **Concatenation is injectable.** With the same trusted template, a benign
    value and an injection payload produce *different skeletons* — the payload's
    text lands in a structural position and the real suffix is displaced. This
    is SQL injection (`' OR …`) as a theorem. -/
theorem concat_injectable :
    skeleton (buildConcat tPre tSuf benign) ≠ skeleton (buildConcat tPre tSuf payload) := by
  decide

/-! ## Integrity noninterference, with a real sink

    Two runs share the trusted template but may differ on the untrusted value.
    Injection-freedom is: the executed skeleton is the same — integrity
    noninterference (T1's unique admissible 2-safety form), now over a real
    query construction rather than an abstract observation. -/

/-- **Parameterization satisfies integrity noninterference.** The executed
    structure is invariant under any change to the untrusted value. -/
theorem param_noninterference (pre suf : Str) :
    ∀ v v', paramStructure pre suf v = paramStructure pre suf v' :=
  fun v v' => param_immune pre suf v v'

/-- **Concatenation violates it.** Some trusted template and two untrusted
    values give different executed structures — the untrusted input influences
    the trusted sink, exactly the leak T1 forbids. -/
theorem concat_leaks :
    ∃ (pre suf v v' : Str),
      skeleton (buildConcat pre suf v) ≠ skeleton (buildConcat pre suf v') :=
  ⟨tPre, tSuf, benign, payload, concat_injectable⟩

/-- **The by-construction fix, stated as integrity NI.** Model the executed
    skeleton as a sink observation of the untrusted value; parameterization
    makes it a constant function of the value (High-invariant), i.e. it
    satisfies the taint form of injection-freedom that T1 (`taint_is_JNI`,
    `admissible_taint_is_Jtaint`) identifies as the unique admissible 2-safety
    formulation — here on a real query. The `LowQuery`-style statement: the sink
    factors through the trusted template alone. -/
theorem param_sink_trusted (pre suf : Str) :
    ∃ f : Unit → List Str, ∀ v, paramStructure pre suf v = f () :=
  ⟨fun _ => [pre, suf], fun _ => rfl⟩

end ConfTyping
