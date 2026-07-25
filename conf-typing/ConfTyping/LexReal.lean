/-
  A richer alphabet — brick 25: multi-character tokens and maximal munch.

  Brick 22's lexer had an honest limit stated in its own header: **one character
  per token**. That makes lexing a trivial one-to-one character scan and dodges
  the actual difficulty of a real front-end — a lexeme spans *several* characters,
  adjacent lexemes must be separated, and the scanner must take the **longest
  match** (maximal munch) at each point. This brick closes that edge: real
  multi-letter keywords (`in`, `co`, `ca`, `em`), whitespace-delimited
  identifiers that are a *run* of digit characters (so an id spans as many
  characters as its value), and a maximal-munch scanner — with the round trip
  re-proved against a printer that is **no longer injective on characters** (the
  space separators and the run lengths carry the token boundaries).

  The point is that the security claim survives the richer surface: the same
  `parse`/`scheck` pipeline runs on top, so an accepted rich-character source
  still leaks nothing of the untrusted input (`rich_source_injection_free`).

  Honest limit carried forward: identifier values are read as a **run length**
  (`id n` prints as `n+1` digit marks), not yet decimal — a decimal digit codec
  is the next front-end depth follow-on. What is new and load-bearing here is
  maximal munch and the separator discipline, with a proved longest-match round
  trip.
-/
import ConfTyping.LexSource

namespace ConfTyping

/-! ## A multi-character alphabet -/

/-- Source characters: the seven keyword letters, a semicolon, a digit mark, and
    a space. Keywords are two letters; an identifier is a run of digit marks;
    tokens are separated by spaces. -/
inductive RCh where
  | li | ln | lc | lo | la | le | lm   -- keyword letters (i,n,c,o,a,e,m)
  | rsemi                              -- `;`
  | dg                                 -- a digit mark (run length = id value + 1)
  | rsp                                -- a space
deriving DecidableEq

/-! ## The printer (no longer injective on single characters) -/

/-- The lexeme of a token — several characters, and *not* separated. -/
def printTokR : Tok → List RCh
  | .kwInput => [.li, .ln]
  | .kwConst => [.lc, .lo]
  | .kwCat   => [.lc, .la]
  | .kwEmit  => [.le, .lm]
  | .semi    => [.rsemi]
  | .id n    => List.replicate (n + 1) .dg

/-- Print a token stream with a space after every token. -/
def printReal : List Tok → List RCh
  | []      => []
  | t :: ts => printTokR t ++ .rsp :: printReal ts

/-! ## The maximal-munch scanner -/

/-- Count a maximal leading run of digit marks, returning the count and the rest. -/
def runDg : List RCh → Nat × List RCh
  | .dg :: r => let (k, r') := runDg r; (k + 1, r')
  | r        => (0, r)

/-- Read one token by longest match: a two-letter keyword, a semicolon, or a
    maximal run of digit marks (`id`). Returns the token and the unconsumed
    characters, or `none` if no token starts here. -/
def readTok : List RCh → Option (Tok × List RCh)
  | .li :: .ln :: r => some (.kwInput, r)
  | .lc :: .lo :: r => some (.kwConst, r)
  | .lc :: .la :: r => some (.kwCat, r)
  | .le :: .lm :: r => some (.kwEmit, r)
  | .rsemi :: r     => some (.semi, r)
  | .dg :: r        => let (k, r') := runDg r; some (.id k, r')
  | _               => none

/-- The lexer: skip spaces, read a token, recurse. Fuel is the character budget
    (one per character consumed); `lexR` supplies the length, which suffices. -/
def lexFuel : Nat → List RCh → List Tok
  | 0,    _      => []
  | _+1,  []     => []
  | f+1,  c :: r =>
      if c = RCh.rsp then lexFuel f r
      else match readTok (c :: r) with
           | some (t, rest) => t :: lexFuel f rest
           | none           => []

def lexR (l : List RCh) : List Tok := lexFuel l.length l

/-! ## Scanner correctness: the maximal-munch round trip -/

/-- A digit run of length `n` followed by a non-digit reads back as `n`. -/
theorem runDg_replicate (n : Nat) (c : RCh) (hc : c ≠ .dg) (r : List RCh) :
    runDg (List.replicate n .dg ++ c :: r) = (n, c :: r) := by
  induction n with
  | zero => simp only [List.replicate, List.nil_append]; cases c <;> simp_all [runDg]
  | succ k ih =>
      simp only [List.replicate, List.cons_append, runDg, ih]

/-- Reading a printed token off the front of `lexeme ++ ' ' :: rest` recovers the
    token and leaves the separator and the rest — longest match at each token. -/
theorem readTok_printTokR (t : Tok) (r : List RCh) :
    readTok (printTokR t ++ .rsp :: r) = some (t, .rsp :: r) := by
  cases t with
  | kwInput => rfl
  | kwConst => rfl
  | kwCat   => rfl
  | kwEmit  => rfl
  | semi    => rfl
  | id n =>
      show readTok (List.replicate (n + 1) .dg ++ .rsp :: r) = _
      simp only [List.replicate, List.cons_append, readTok,
        runDg_replicate n .rsp (by decide) r]

/-- Every lexeme is non-empty and never starts with a space. -/
theorem printTokR_ne_sp (t : Tok) : ∃ c r, printTokR t = c :: r ∧ c ≠ RCh.rsp := by
  cases t with
  | kwInput => exact ⟨_, _, rfl, by decide⟩
  | kwConst => exact ⟨_, _, rfl, by decide⟩
  | kwCat   => exact ⟨_, _, rfl, by decide⟩
  | kwEmit  => exact ⟨_, _, rfl, by decide⟩
  | semi    => exact ⟨_, _, rfl, by decide⟩
  | id n    => exact ⟨.dg, List.replicate n .dg, by simp [printTokR, List.replicate], by decide⟩

/-- **Scanner correctness (round trip), fuel-parametric.** With enough fuel the
    maximal-munch lexer recovers any token stream from its printed characters. -/
theorem lexFuel_printReal :
    ∀ (ts : List Tok) (fuel : Nat), (printReal ts).length ≤ fuel →
      lexFuel fuel (printReal ts) = ts := by
  intro ts
  induction ts with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons t ts ih =>
      intro fuel hf
      obtain ⟨c, cs, hpt, hc⟩ := printTokR_ne_sp t
      -- fuel is at least the whole printed length, hence positive
      have hlen : (printReal (t :: ts)).length
          = (printTokR t).length + 1 + (printReal ts).length := by
        simp only [printReal, List.length_append, List.length_cons]; omega
      have hpos : (printTokR t).length ≥ 1 := by rw [hpt]; simp
      cases fuel with
      | zero => rw [hlen] at hf; omega
      | succ f =>
          -- the stream starts with the first lexeme character, not a space
          have hhead : printReal (t :: ts) = c :: (cs ++ .rsp :: printReal ts) := by
            simp only [printReal, hpt, List.cons_append]
          rw [hhead]
          have hcsp : ¬ (c = RCh.rsp) := hc
          simp only [lexFuel, if_neg hcsp]
          -- longest match reads token t, leaving the separator + rest
          have hread : readTok (c :: (cs ++ .rsp :: printReal ts))
              = some (t, .rsp :: printReal ts) := by
            have h := readTok_printTokR t (printReal ts)
            rw [hpt] at h; simp only [List.cons_append] at h; exact h
          simp only [hread]
          -- now skip the separator and recurse
          have hf1 : (printReal ts).length + 1 ≤ f := by
            rw [hlen] at hf; omega
          cases f with
          | zero => omega
          | succ g =>
              have hstep : lexFuel (g + 1) (RCh.rsp :: printReal ts)
                  = lexFuel g (printReal ts) := rfl
              rw [hstep, ih g (by omega)]

/-- **Scanner correctness (round trip).** Lexing the printed characters of any
    token stream recovers it exactly. -/
theorem lexR_printReal (ts : List Tok) : lexR (printReal ts) = ts :=
  lexFuel_printReal ts (printReal ts).length (Nat.le_refl _)

/-! ## End to end: from rich source characters to injection-freedom -/

/-- **The security guarantee, on rich source characters.** If a multi-character
    source lexes and parses to a program the taint checker accepts, the emitted
    output is a function of the trusted program alone. The claim attaches to a
    real, whitespace-delimited character source, through the full
    `lexR`/`parse`/`scheck` pipeline. -/
theorem rich_source_injection_free {chars : List RCh} {c : SCmd} {T : List Nat}
    (hlex : parse (lexR chars) = some c) (hchk : scheck [] c = some T)
    (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp c (σ₀, [])).2 = (sexec inp' c (σ₀, [])).2 :=
  source_injection_free hlex hchk inp inp' σ₀

/-! ## Witnesses: an actual multi-character source -/

/-- The token stream `input 0 ; cat 2 1 0 ; emit 2` — the injectable program. -/
def unsafeToks : List Tok :=
  [.kwInput, .id 0, .semi, .kwCat, .id 2, .id 1, .id 0, .semi, .kwEmit, .id 2]

/-- Its rendering in the rich alphabet: `in d ; ca ddd dd d ; em ddd`
    (keywords two letters, ids digit runs, tokens space-separated). -/
def unsafeRich : List RCh := printReal unsafeToks

/-- **It lexes** back to the token stream — maximal munch recovers multi-letter
    keywords and multi-digit-run identifiers across the separators. -/
theorem unsafe_rich_lexes : lexR unsafeRich = unsafeToks := lexR_printReal unsafeToks

/-- **It lexes and parses** to the expected program. -/
theorem unsafe_rich_parses :
    parse (lexR unsafeRich) = some (.seq (.input 0) (.seq (.cat 2 1 0) (.one (.emit 2)))) := by
  rw [unsafe_rich_lexes]; decide

/-- **And the checker rejects it** — injection caught, from a rich character source. -/
theorem unsafe_rich_rejected :
    scheck [] (.seq (.input 0) (.seq (.cat 2 1 0) (.one (.emit 2)))) = none := by decide

/-- A safe rich source `input 0 ; const 2 ; emit 2` (emit a trusted constant):
    lexes, parses, checks, and is injection-free end to end from its characters. -/
def safeToks : List Tok :=
  [.kwInput, .id 0, .semi, .kwConst, .id 2, .semi, .kwEmit, .id 2]

def safeRich : List RCh := printReal safeToks

theorem safe_rich_parses :
    parse (lexR safeRich) = some (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) := by
  rw [show lexR safeRich = safeToks from lexR_printReal safeToks]; decide

theorem safe_rich_accepted :
    (scheck [] (.seq (.input 0) (.seq (.const 2) (.one (.emit 2))))).isSome = true := by decide

theorem safe_rich_injection_free (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) (σ₀, [])).2
      = (sexec inp' (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) (σ₀, [])).2 := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp safe_rich_accepted
  exact rich_source_injection_free safe_rich_parses hT inp inp' σ₀

end ConfTyping
