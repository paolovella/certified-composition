/-
  A lexer — brick 22: the source pipeline reaches characters.

  Brick 21's parser starts from a token stream; a real front-end starts from a
  character string. This brick adds the missing layer — a **lexer** from
  characters to tokens — with its own round-trip correctness, and chains
  lexer + parser + checker into an end-to-end guarantee about an actual
  character-string source:

  > if a character string lexes and parses to a program and the taint checker
  > accepts it, running it leaks nothing of the untrusted input
  > (`source_string_injection_free`).

  The alphabet is small (one character per token: `i c t e ;`, digits for
  variable ids, and spaces the lexer skips), so lexing is a clean character
  scan; the point is the *complete* character-to-guarantee pipeline with a proved
  lexer round trip, not a production lexer. Together with brick 21 the whole
  chain — string → lex → parse → check → theorem — is machine-checked, so the
  security claim attaches to source *characters*.
-/
import ConfTyping.ParseSource

namespace ConfTyping

/-! ## Characters and lexing -/

/-- Source characters: keyword letters, `;`, a space, and digits (variable ids). -/
inductive LCh where
  | ci | cc | ct | ce | csemi | csp
  | cd : Nat → LCh
deriving DecidableEq

/-- The token a character denotes (`none` for a space, which is skipped). -/
def tokOf : LCh → Option Tok
  | .ci    => some .kwInput
  | .cc    => some .kwConst
  | .ct    => some .kwCat
  | .ce    => some .kwEmit
  | .csemi => some .semi
  | .cd n  => some (.id n)
  | .csp   => none

/-- The lexer: scan characters into tokens, skipping spaces. -/
def lex : List LCh → List Tok
  | []     => []
  | c :: r => match tokOf c with
              | some t => t :: lex r
              | none   => lex r

/-! ## Lexer correctness: the round trip -/

/-- One character per token. -/
def printCh : Tok → LCh
  | .kwInput => .ci
  | .kwConst => .cc
  | .kwCat   => .ct
  | .kwEmit  => .ce
  | .semi    => .csemi
  | .id n    => .cd n

theorem tokOf_printCh (t : Tok) : tokOf (printCh t) = some t := by
  cases t <;> rfl

/-- **Lexer correctness (round trip).** Lexing the printed characters of any
    token stream recovers it exactly — the lexer is a left inverse of the
    per-token printer. -/
theorem lex_print (toks : List Tok) : lex (toks.map printCh) = toks := by
  induction toks with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, lex, tokOf_printCh, ih]

/-- Spaces are skipped: interspersing a space changes nothing lexed. -/
theorem lex_skip_space (a b : List LCh) : lex (a ++ .csp :: b) = lex a ++ lex b := by
  induction a with
  | nil => rfl
  | cons c r ih =>
      show lex (c :: (r ++ .csp :: b)) = lex (c :: r) ++ lex b
      cases hc : tokOf c with
      | none => simp only [lex, hc, ih]
      | some t => simp only [lex, hc, ih, List.cons_append]

/-! ## End to end: from a character string to injection-freedom -/

/-- **The security guarantee, on a character string.** If a character source
    lexes and parses to a program and the taint checker accepts it, the emitted
    output is a function of the trusted program alone — the untrusted input
    cannot influence it. The claim now attaches to source *characters*, through
    the full `lex`/`parse`/`scheck` pipeline. -/
theorem source_string_injection_free {chars : List LCh} {c : SCmd} {T : List Nat}
    (hlex : parse (lex chars) = some c) (hchk : scheck [] c = some T)
    (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp c (σ₀, [])).2 = (sexec inp' c (σ₀, [])).2 :=
  source_injection_free hlex hchk inp inp' σ₀

/-! ## Witnesses: an actual character-string source -/

/-- The character string `i0;t210;e2` — read input into 0, concatenate it into a
    query 2, emit 2 — the injectable program as a source a lexer would receive. -/
def unsafeChars : List LCh :=
  [.ci, .cd 0, .csemi, .ct, .cd 2, .cd 1, .cd 0, .csemi, .ce, .cd 2]

/-- **It lexes and parses** to the expected program. -/
theorem unsafe_chars_parse :
    parse (lex unsafeChars) = some (.seq (.input 0) (.seq (.cat 2 1 0) (.one (.emit 2)))) := by
  decide

/-- **And the checker rejects it** — injection caught, from a character string. -/
theorem unsafe_chars_rejected :
    scheck [] (.seq (.input 0) (.seq (.cat 2 1 0) (.one (.emit 2)))) = none := by decide

/-- The same source with spaces (`i 0 ; t 2 1 0 ; e 2`) lexes identically — the
    lexer skips whitespace. -/
def unsafeCharsSpaced : List LCh :=
  [.ci, .csp, .cd 0, .csp, .csemi, .csp, .ct, .csp, .cd 2, .csp, .cd 1, .csp, .cd 0,
   .csp, .csemi, .csp, .ce, .csp, .cd 2]

theorem spaced_lexes_same : lex unsafeCharsSpaced = lex unsafeChars := by decide

/-- A safe character source `i0;c2;e2` (emit a trusted constant): lexes, parses,
    checks, and is injection-free end to end from its characters. -/
def safeChars : List LCh :=
  [.ci, .cd 0, .csemi, .cc, .cd 2, .csemi, .ce, .cd 2]

theorem safe_chars_parse :
    parse (lex safeChars) = some (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) := by
  decide

theorem safe_chars_accepted :
    (scheck [] (.seq (.input 0) (.seq (.const 2) (.one (.emit 2))))).isSome = true := by decide

theorem safe_chars_injection_free (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) (σ₀, [])).2
      = (sexec inp' (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) (σ₀, [])).2 := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp safe_chars_accepted
  exact source_string_injection_free safe_chars_parse hT inp inp' σ₀

end ConfTyping
