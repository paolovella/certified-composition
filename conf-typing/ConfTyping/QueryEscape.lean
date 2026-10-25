/-
  String literals with escapes — brick 31: why escaping is a *ledger entry* and
  parameterization is a *theorem*.

  Bricks 14 and 26 made injection real on a tokenizer with no escape mechanism:
  a quote always toggles in/out of a literal, so the only safe value is a
  quote-free one. Every real database disagrees — a literal may *contain* a
  quote, written with an escape convention. That was the last named depth
  follow-on on the injection axis, and it is where the actual CVEs live: not in
  "they forgot to escape", but in "they escaped against the wrong convention".

  This brick puts escapes in the model and proves four things.

  * **Conservative extension.** The escape-aware tokenizer `segsE` (backslash
    convention: inside a literal `\` escapes the next character) agrees with
    brick 14's `segs` on every backslash-free string (`segsT_noBS`,
    `skeletonE_eq_skeleton`). Bricks 14 and 26 are re-derived, not replaced
    (`param_correct_esc`, `concat_injectable_esc`).

  * **Escaping, done completely, works — and is faithful.** The complete
    escaper `esc` (escape the quote *and* the escape character) makes the
    tokenized query exactly `[pre, v, suf]` for **every** value `v`, with no
    hypothesis on `v` at all (`segsE_buildEsc`). So the skeleton is constant
    (`esc_immune` — integrity noninterference) and the data segment delivered
    to the database is `v` unchanged (`esc_faithful`).

  * **The classic bug is exactly the unescaped escape character.**
    `escBad` escapes `'` but not `\`; `escBad_injectable` is the real attack
    (`\'` — the backslash consumes the escaper's backslash, the quote breaks
    out), and `escBad_noBS_ok` proves it is nevertheless sound on
    backslash-free values. The boundary is a theorem in both directions.

  * **The point.** Escaping's soundness is a *relation between the escaper and
    the sink's tokenizer*, not a property of the escaper. Against the
    SQL-standard doubled-quote tokenizer `segsD`, the backslash escaper is
    injectable (`esc_mismatch_injectable`), and against the backslash tokenizer
    the doubling escaper is injectable (`escDouble_mismatch_injectable`) —
    while each is sound for its own convention (`esc_skeleton`,
    `escDouble_skeleton`). So escaping carries an assumption, and this repo
    already has the machinery for that: `escaping_no_silent_discharge` is
    brick 4's `ledger_no_silent_discharge` on the injection channel — the
    conditional guarantee holds for every tokenizer *assuming* the convention
    matches, and the unconditional one is false at a tokenizer where it does
    not. Parameterization needs the **empty** ledger (`param_immune_no_ledger`):
    the value is never tokenized, so there is no convention to agree about.

  Verdict impact for VULN-COVERAGE row 3: escaping is REDUCIBLE — sound given a
  named, load-bearing assumption that now sits in the ledger; parameterization
  stays IN, and the gap between the two is these theorems.
-/
import ConfTyping.QueryGrammar
import ConfTyping.Ledger

namespace ConfTyping

/-! ## The escape character

    Brick 14's alphabet already has ordinary characters carrying a code; the
    backslash is the one at ASCII 92. No new character type is introduced, so
    every brick-14/26 string is a string here. -/

/-- The backslash, in brick 14's alphabet. -/
def bs : Ch := .c 92

/-- Push a character onto the front of the current (head) segment — the
    accumulation brick 14's `segs` performs inline. -/
def consHead (ch : Ch) : List Str → List Str
  | s :: ss => (ch :: s) :: ss
  | []      => [[ch]]

theorem segs_cons_c (n : Nat) (r : Str) : segs (.c n :: r) = consHead (.c n) (segs r) := by
  simp only [segs, consHead]
  cases segs r <;> rfl

/-- Does the string contain a backslash? -/
def noBS : Str → Bool
  | []        => true
  | .q :: r   => noBS r
  | .c n :: r => (n != 92) && noBS r

/-! ## Tokenizer 1: the backslash convention

    A three-state scanner. `out` — outside a literal, where a quote opens one
    and a backslash is an ordinary character (MySQL's actual behaviour). `inn` —
    inside a literal, where an unescaped quote closes it and a backslash arms
    the escape. `esc` — inside a literal with the escape armed: the next
    character is data, whatever it is. -/

/-- Scanner state for the backslash convention. -/
inductive TState where
  | out | inn | esc
  deriving DecidableEq

/-- Escape-aware segmentation, backslash convention. As in brick 14, a segment
    ends where the next one begins, so `n` literal delimiters give `n+1`
    segments and even indices are structural. Escaped characters are *decoded*
    into the data segment — the value the database receives. -/
def segsT : TState → Str → List Str
  | _,    []          => [[]]
  | .out, .q :: r     => [] :: segsT .inn r
  | .out, .c n :: r   => consHead (.c n) (segsT .out r)
  | .inn, .q :: r     => [] :: segsT .out r
  | .inn, .c n :: r   => if n == 92 then segsT .esc r else consHead (.c n) (segsT .inn r)
  | .esc, ch :: r     => consHead ch (segsT .inn r)

/-- Tokenize a query under the backslash convention. -/
def segsE (s : Str) : List Str := segsT .out s

/-- The executed skeleton under the backslash convention. -/
def skeletonE (s : Str) : List Str := evens (segsE s)

/-- The data segments (odd indices) — the literal values the database sees. -/
def odds : List Str → List Str
  | []          => []
  | [_]         => []
  | _ :: y :: r => y :: odds r

/-- The literal values delivered by a query, under the backslash convention. -/
def dataSegs (s : Str) : List Str := odds (segsE s)

/-! ## Conservative extension: brick 14's tokenizer is the backslash-free case -/

/-- **The escape-aware tokenizer extends brick 14's conservatively.** On a
    string with no backslash the two agree, in either literal state — the
    escape machinery is inert exactly where brick 14 was defined. -/
theorem segsT_noBS : ∀ (s : Str), noBS s = true → ∀ t : TState, t ≠ .esc →
    segsT t s = segs s := by
  intro s
  induction s with
  | nil => intro _ t _; cases t <;> rfl
  | cons ch r ih =>
      intro h t ht
      cases ch with
      | q =>
          have hr : noBS r = true := by simpa [noBS] using h
          cases t with
          | out => simpa [segsT, segs] using ih hr .inn (by simp)
          | inn => simpa [segsT, segs] using ih hr .out (by simp)
          | esc => exact absurd rfl ht
      | c n =>
          obtain ⟨hn, hr⟩ : ¬ n = 92 ∧ noBS r = true := by simpa [noBS] using h
          have hn' : ¬ (n == 92) = true := by simpa using hn
          cases t with
          | out => simp only [segsT, segs_cons_c, ih hr .out (by simp)]
          | inn =>
              simp only [segsT, segs_cons_c, ite_eq_right hn', ih hr .inn (by simp)]
          | esc => exact absurd rfl ht

/-- The skeletons agree on backslash-free queries: bricks 14 and 26 transfer
    into the richer model unchanged. -/
theorem skeletonE_eq_skeleton {s : Str} (h : noBS s = true) : skeletonE s = skeleton s := by
  simp only [skeletonE, segsE, skeleton, segsT_noBS s h .out (by simp)]

/-! ## Escapers -/

/-- **The complete escaper.** Prefix a backslash to every quote *and* to every
    backslash. Escaping the escape character is the part real code forgets. -/
def esc : Str → Str
  | []        => []
  | .q :: r   => bs :: .q :: esc r
  | .c n :: r => if n == 92 then bs :: bs :: esc r else .c n :: esc r

/-- **The classic buggy escaper.** Escapes the quote, leaves the escape
    character alone — the CWE-89 mitigation that does not mitigate. -/
def escBad : Str → Str
  | []        => []
  | .q :: r   => bs :: .q :: escBad r
  | .c n :: r => .c n :: escBad r

/-- **The SQL-standard escaper**: a quote inside a literal is written doubled,
    and there is no escape character at all. -/
def escDouble : Str → Str
  | []        => []
  | .q :: r   => .q :: .q :: escDouble r
  | .c n :: r => .c n :: escDouble r

/-- Build a query by splicing an *escaped* untrusted value into a trusted
    template, then handing the whole string to the sink's tokenizer. With
    `E = id` this is brick 14's `buildConcat`. -/
def buildEsc (E : Str → Str) (pre suf v : Str) : Str := pre ++ .q :: (E v ++ .q :: suf)

theorem buildEsc_id (pre suf v : Str) : buildEsc id pre suf v = buildConcat pre suf v := rfl

/-! ## Scanning lemmas -/

/-- Push a whole string onto the front of the current segment. -/
def prependHead : Str → List Str → List Str
  | [],      L => L
  | ch :: r, L => consHead ch (prependHead r L)

theorem prependHead_cons : ∀ (v x : Str) (L : List Str),
    prependHead v (x :: L) = (v ++ x) :: L
  | [],      _, _ => rfl
  | ch :: r, x, L => by simp only [prependHead, prependHead_cons r x L, consHead,
                                   List.cons_append]

/-- A quote-free string scanned outside a literal is one structural segment
    (backslashes are ordinary there, so no hypothesis on them). -/
theorem segsT_out_qfree : ∀ {s : Str}, hasQ s = false → segsT .out s = [s]
  | [],        _ => rfl
  | .q :: _,   h => by simp [hasQ] at h
  | .c n :: r, h => by
      have hr : hasQ r = false := by simpa [hasQ] using h
      simp only [segsT, segsT_out_qfree hr, consHead]

/-- Splitting after a quote-free prefix, outside a literal: the prefix is the
    first structural segment and the scanner enters the literal. -/
theorem segsT_out_append_q : ∀ {a : Str}, hasQ a = false → ∀ rest : Str,
    segsT .out (a ++ .q :: rest) = a :: segsT .inn rest
  | [],        _, _    => rfl
  | .q :: _,   h, _    => by simp [hasQ] at h
  | .c n :: a', h, rest => by
      have hr : hasQ a' = false := by simpa [hasQ] using h
      simp only [List.cons_append, segsT, segsT_out_append_q hr rest, consHead]

/-- **The heart of the brick.** Scanning a completely-escaped value inside a
    literal consumes exactly the value — every character of `v` lands in the
    data segment, decoded, and the scanner is still inside the literal
    afterwards. Neither a quote nor a backslash in `v` can escape the literal,
    because `esc` neutralises both. No hypothesis on `v`. -/
theorem segsT_esc : ∀ (v rest : Str),
    segsT .inn (esc v ++ rest) = prependHead v (segsT .inn rest)
  | [],      _    => rfl
  | .q :: r, rest => by
      show segsT .inn (bs :: .q :: (esc r ++ rest)) = _
      simp only [bs, segsT, prependHead, segsT_esc r rest]
      rfl
  | .c n :: r, rest => by
      by_cases hn : (n == 92) = true
      · have hn' : n = 92 := by simpa using hn
        subst hn'
        show segsT .inn (bs :: bs :: (esc r ++ rest)) = _
        simp only [bs, segsT, prependHead, segsT_esc r rest]
        rfl
      · show segsT .inn ((if (n == 92) then bs :: bs :: esc r else .c n :: esc r) ++ rest) = _
        rw [ite_eq_right hn]
        simp only [List.cons_append, segsT, ite_eq_right hn, prependHead, segsT_esc r rest]

/-! ## Escaping, done completely, is sound and faithful -/

/-- **The escaped query tokenizes to exactly `[pre, v, suf]`, for every value.**
    No quote-freeness hypothesis on `v` — that was brick 14's restriction, and
    this is what lifting it costs: a complete escaper. -/
theorem segsE_buildEsc {pre suf : Str} (hpre : hasQ pre = false) (hsuf : hasQ suf = false)
    (v : Str) : segsE (buildEsc esc pre suf v) = [pre, v, suf] := by
  show segsT .out (pre ++ .q :: (esc v ++ .q :: suf)) = _
  rw [segsT_out_append_q hpre, segsT_esc v (.q :: suf)]
  show pre :: prependHead v ([] :: segsT .out suf) = _
  rw [segsT_out_qfree hsuf, prependHead_cons]
  simp

/-- **Escaping is immune to injection**: the executed skeleton is the two
    structural pieces, for every untrusted value. -/
theorem esc_skeleton {pre suf : Str} (hpre : hasQ pre = false) (hsuf : hasQ suf = false)
    (v : Str) : skeletonE (buildEsc esc pre suf v) = [pre, suf] := by
  simp only [skeletonE, segsE_buildEsc hpre hsuf v, evens]

/-- **Integrity noninterference for the escaping build**, under the tokenizer it
    was written for: the sink's structure does not depend on the value. -/
theorem esc_immune {pre suf : Str} (hpre : hasQ pre = false) (hsuf : hasQ suf = false)
    (v v' : Str) :
    skeletonE (buildEsc esc pre suf v) = skeletonE (buildEsc esc pre suf v') := by
  rw [esc_skeleton hpre hsuf v, esc_skeleton hpre hsuf v']

/-- **Escaping is faithful**: the value the database receives is `v` itself —
    the escaper is not buying safety by corrupting data. -/
theorem esc_faithful {pre suf : Str} (hpre : hasQ pre = false) (hsuf : hasQ suf = false)
    (v : Str) : dataSegs (buildEsc esc pre suf v) = [v] := by
  simp only [dataSegs, segsE_buildEsc hpre hsuf v, odds]

/-! ## The classic bug: the unescaped escape character -/

/-- `tPre`/`tSuf` are brick 14's trusted template pieces. -/
theorem tPre_qfree : hasQ tPre = false := by decide
theorem tSuf_qfree : hasQ tSuf = false := by decide

/-- The real payload: a backslash, then a quote, then structural text. The
    backslash eats the escaper's backslash, so the quote arrives unescaped. -/
def payloadBS : Str := [bs, .q, .c 3]

/-- **The buggy escaper is injectable.** Same trusted template, benign value
    versus `\'…`: different executed skeletons. This is the escaping-based
    "fix" failing, as a theorem — and it fails against the very tokenizer it
    was written for, so it is a genuine bug, not a convention mismatch. -/
theorem escBad_injectable :
    skeletonE (buildEsc escBad tPre tSuf benign) ≠
      skeletonE (buildEsc escBad tPre tSuf payloadBS) := by decide

/-- On backslash-free values the buggy escaper coincides with the complete
    one — the defect is exactly the unhandled escape character. -/
theorem escBad_eq_esc : ∀ {v : Str}, noBS v = true → escBad v = esc v
  | [],      _ => rfl
  | .q :: r, h => by
      have hr : noBS r = true := by simpa [noBS] using h
      simp only [escBad, esc, escBad_eq_esc hr]
  | .c n :: r, h => by
      obtain ⟨hn0, hr⟩ : ¬ n = 92 ∧ noBS r = true := by simpa [noBS] using h
      have hn : ¬ (n == 92) = true := by simpa using hn0
      simp only [escBad, esc, ite_eq_right hn, escBad_eq_esc hr]

/-- **The precise boundary.** The buggy escaper is sound on every
    backslash-free value and unsound in general: the vulnerability is located,
    not merely exhibited. -/
theorem escBad_noBS_ok {pre suf : Str} (hpre : hasQ pre = false) (hsuf : hasQ suf = false)
    {v : Str} (hv : noBS v = true) : skeletonE (buildEsc escBad pre suf v) = [pre, suf] := by
  show skeletonE (pre ++ .q :: (escBad v ++ .q :: suf)) = _
  rw [escBad_eq_esc hv]
  exact esc_skeleton hpre hsuf v

/-! ## Tokenizer 2: the SQL-standard doubled-quote convention

    No escape character exists; a quote inside a literal is written twice. The
    scanner needs a state for "saw a quote inside a literal, do not know yet
    whether it closes". -/

/-- Scanner state for the doubled-quote convention. -/
inductive DState where
  | out | inn | qq
  deriving DecidableEq

/-- Segmentation under the doubled-quote convention. -/
def segsD : DState → Str → List Str
  | .out, []        => [[]]
  | .inn, []        => [[]]
  | .qq,  []        => [] :: [[]]
  | .out, .q :: r   => [] :: segsD .inn r
  | .out, .c n :: r => consHead (.c n) (segsD .out r)
  | .inn, .q :: r   => segsD .qq r
  | .inn, .c n :: r => consHead (.c n) (segsD .inn r)
  | .qq,  .q :: r   => consHead .q (segsD .inn r)
  | .qq,  .c n :: r => [] :: consHead (.c n) (segsD .out r)

/-- Tokenize a query under the doubled-quote convention. -/
def segsDoubled (s : Str) : List Str := segsD .out s

/-- The executed skeleton under the doubled-quote convention. -/
def skeletonD (s : Str) : List Str := evens (segsDoubled s)

theorem segsD_out_qfree : ∀ {s : Str}, hasQ s = false → segsD .out s = [s]
  | [],        _ => rfl
  | .q :: _,   h => by simp [hasQ] at h
  | .c n :: r, h => by
      have hr : hasQ r = false := by simpa [hasQ] using h
      simp only [segsD, segsD_out_qfree hr, consHead]

theorem segsD_out_append_q : ∀ {a : Str}, hasQ a = false → ∀ rest : Str,
    segsD .out (a ++ .q :: rest) = a :: segsD .inn rest
  | [],        _, _     => rfl
  | .q :: _,   h, _     => by simp [hasQ] at h
  | .c n :: a', h, rest => by
      have hr : hasQ a' = false := by simpa [hasQ] using h
      simp only [List.cons_append, segsD, segsD_out_append_q hr rest, consHead]

/-- A pending quote followed by quote-free text: the literal closes and the
    remaining text is one structural segment. -/
theorem segsD_qq_qfree : ∀ {s : Str}, hasQ s = false → segsD .qq s = [] :: [s]
  | [],        _ => rfl
  | .q :: _,   h => by simp [hasQ] at h
  | .c n :: r, h => by
      have hr : hasQ r = false := by simpa [hasQ] using h
      simp only [segsD, segsD_out_qfree hr, consHead]

/-- The doubling escaper's scanning lemma, mirroring `segsT_esc`. -/
theorem segsD_escDouble : ∀ (v rest : Str),
    segsD .inn (escDouble v ++ rest) = prependHead v (segsD .inn rest)
  | [],        _    => rfl
  | .q :: r,   rest => by
      show segsD .inn (.q :: .q :: (escDouble r ++ rest)) = _
      simp only [segsD, prependHead, segsD_escDouble r rest]
  | .c n :: r, rest => by
      show segsD .inn (.c n :: (escDouble r ++ rest)) = _
      simp only [segsD, prependHead, segsD_escDouble r rest]

/-- **The doubling escaper is sound — for the doubled-quote convention.** Same
    shape as `esc_skeleton`, different tokenizer. -/
theorem escDouble_skeleton {pre suf : Str} (hpre : hasQ pre = false) (hsuf : hasQ suf = false)
    (v : Str) : skeletonD (buildEsc escDouble pre suf v) = [pre, suf] := by
  have hseg : segsDoubled (buildEsc escDouble pre suf v) = [pre, v, suf] := by
    show segsD .out (pre ++ .q :: (escDouble v ++ .q :: suf)) = _
    rw [segsD_out_append_q hpre, segsD_escDouble v (.q :: suf)]
    show pre :: prependHead v (segsD .qq suf) = _
    rw [segsD_qq_qfree hsuf, prependHead_cons]
    simp
  simp only [skeletonD, hseg, evens]

/-! ## The point: escaping is a relation between escaper and tokenizer

    Each escaper above is sound for its own convention. Swap the conventions
    and each is injectable — with the *same* single-quote payload that the
    escaper was written to neutralise. -/

/-- A bare quote: the value every escaper claims to handle. -/
def quoteVal : Str := [.q]

/-- **The backslash escaper is injectable against the doubled-quote sink.**
    `\'` is not an escaped quote there — the backslash is data and the quote
    closes the literal. -/
theorem esc_mismatch_injectable :
    skeletonD (buildEsc esc tPre tSuf benign) ≠
      skeletonD (buildEsc esc tPre tSuf quoteVal) := by decide

/-- **The doubling escaper is injectable against the backslash sink.** `''` is
    a closed-then-reopened literal there, not a data quote. -/
theorem escDouble_mismatch_injectable :
    skeletonE (buildEsc escDouble tPre tSuf benign) ≠
      skeletonE (buildEsc escDouble tPre tSuf quoteVal) := by decide

/-- **Neither escaper is safe simpliciter.** Each is sound for one convention
    and injectable for the other — so "the value is escaped" is not a security
    property of the value or of the escaper; it is a property of the pair. -/
theorem escaping_is_convention_relative :
    (∀ v v', skeletonE (buildEsc esc tPre tSuf v) = skeletonE (buildEsc esc tPre tSuf v'))
  ∧ (skeletonD (buildEsc esc tPre tSuf benign) ≠ skeletonD (buildEsc esc tPre tSuf quoteVal))
  ∧ (∀ v v', skeletonD (buildEsc escDouble tPre tSuf v)
              = skeletonD (buildEsc escDouble tPre tSuf v'))
  ∧ (skeletonE (buildEsc escDouble tPre tSuf benign)
      ≠ skeletonE (buildEsc escDouble tPre tSuf quoteVal)) :=
  ⟨fun v v' => esc_immune tPre_qfree tSuf_qfree v v',
   esc_mismatch_injectable,
   fun v v' => by
     rw [escDouble_skeleton tPre_qfree tSuf_qfree v,
         escDouble_skeleton tPre_qfree tSuf_qfree v'],
   escDouble_mismatch_injectable⟩

/-! ## So escaping is a ledger entry (brick 4), and parameterization is not -/

/-- The sink's tokenizer — the thing an escaper must agree with. -/
abbrev Tokenizer := Str → List Str

/-- Injection-freedom of a build against a *given* sink tokenizer: the executed
    skeleton is invariant under the untrusted value. -/
def EscImmune (T : Tokenizer) (E : Str → Str) (pre suf : Str) : Prop :=
  ∀ v v', evens (T (buildEsc E pre suf v)) = evens (T (buildEsc E pre suf v'))

/-- Injection-freedom of the parameterized build — no tokenizer appears,
    because the value is never tokenized. -/
def ParamImmune (pre suf : Str) : Prop :=
  ∀ v v', paramStructure pre suf v = paramStructure pre suf v'

/-- **The conditional certificate.** For *every* sink tokenizer, escaping is
    injection-free relative to the one-entry ledger "the sink uses the
    backslash convention". Brick 4's `CondBoundary`, on the injection
    channel. -/
theorem esc_cond_immune {pre suf : Str} (hpre : hasQ pre = false) (hsuf : hasQ suf = false)
    (T : Tokenizer) : Sat [T = segsE] → EscImmune T esc pre suf := by
  intro hsat v v'
  have hT : T = segsE := hsat.1
  subst hT
  exact esc_immune hpre hsuf v v'

/-- **The unconditional certificate is false**, at a sink whose convention
    differs: the ledger entry is load-bearing. -/
theorem esc_not_unconditional : ¬ EscImmune segsDoubled esc tPre tSuf := by
  intro h
  have := h benign quoteVal
  exact esc_mismatch_injectable this

/-- **No silent discharge, on the injection channel.** The conditional
    guarantee holds for every tokenizer assuming the convention matches, yet
    the unconditional guarantee fails at a tokenizer where it does not. An
    escaping-based mitigation therefore *cannot* be certified with the
    convention assumption dropped — it is brick 4's
    `ledger_no_silent_discharge`, instantiated on a real query sink. -/
theorem escaping_no_silent_discharge :
    (∀ T, Sat [T = segsE] → EscImmune T esc tPre tSuf)
  ∧ ¬ EscImmune segsDoubled esc tPre tSuf :=
  ⟨fun T => esc_cond_immune tPre_qfree tSuf_qfree T, esc_not_unconditional⟩

/-- **Parameterization needs the empty ledger.** Brick 4: the empty ledger is
    exactly the unconditional certificate. The prepared statement's structure
    is a constant function of the value with no assumption about the sink's
    lexical conventions, because no value ever reaches the tokenizer. -/
theorem param_immune_no_ledger (pre suf : Str) : Sat ([] : Ledger) → ParamImmune pre suf :=
  fun _ _ _ => rfl

/-- **The verdict, as one theorem.** Escaping is REDUCIBLE — injection-free
    given a named assumption that is provably load-bearing; parameterization is
    IN — injection-free with an empty trusted base. The gap between "escape
    your inputs" and "use prepared statements" is exactly one ledger entry, and
    the entry cannot be discharged by inspecting the application. -/
theorem escaping_reducible_parameterization_in :
    ((∀ T, Sat [T = segsE] → EscImmune T esc tPre tSuf) ∧ ¬ EscImmune segsDoubled esc tPre tSuf)
  ∧ (∀ pre suf, Sat ([] : Ledger) → ParamImmune pre suf) :=
  ⟨escaping_no_silent_discharge, param_immune_no_ledger⟩

/-! ## Bricks 14 and 26 survive the richer tokenizer -/

/-- Brick 14's correctness statement, re-proved against the escape-aware
    tokenizer: on a quote-free, backslash-free value the concatenated query's
    skeleton is the parameterized structure. -/
theorem param_correct_esc {pre suf v : Str}
    (hpre : hasQ pre = false) (hv : hasQ v = false) (hsuf : hasQ suf = false)
    (bpre : noBS pre = true) (bv : noBS v = true) (bsuf : noBS suf = true) :
    skeletonE (buildConcat pre suf v) = paramStructure pre suf v := by
  have hnb : noBS (buildConcat pre suf v) = true := by
    have hap : ∀ a b : Str, noBS a = true → noBS b = true → noBS (a ++ b) = true := by
      intro a
      induction a with
      | nil => intro _ _ hb; simpa using hb
      | cons ch a' ih =>
          intro b ha hb
          cases ch with
          | q => simpa [noBS] using ih b (by simpa [noBS] using ha) hb
          | c n =>
              obtain ⟨h1, h2⟩ : ¬ n = 92 ∧ noBS a' = true := by simpa [noBS] using ha
              simp only [List.cons_append, noBS]
              exact Bool.and_eq_true_iff.mpr ⟨by simpa using h1, ih b h2 hb⟩
    exact hap pre _ bpre (by simpa [noBS] using hap v _ bv (by simpa [noBS] using bsuf))
  rw [skeletonE_eq_skeleton hnb]
  exact param_correct hpre hv hsuf

/-- Brick 14's attack, re-proved against the escape-aware tokenizer: raw
    concatenation is still injectable when nothing is escaped. -/
theorem concat_injectable_esc :
    skeletonE (buildConcat tPre tSuf benign) ≠ skeletonE (buildConcat tPre tSuf payload) := by
  decide

end ConfTyping
