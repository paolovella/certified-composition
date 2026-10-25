/-
  Decimal identifiers — brick 28: the codec brick 25 deferred.

  Brick 25 made lexemes multi-character and the scanner maximal-munch, but named
  one residual: identifier *values* were read as a run length (`id n` printed as
  `n+1` marks), not decimal. This brick closes it with a **verified decimal
  codec** and a lexer that reads real multi-digit decimal identifiers.

  The codec is mathlib-free: `toDigits` (well-founded on `n / 10`) and `ofDigits`
  (a base-10 fold), with the round trip `ofDigits (toDigits n) = n` proved by the
  definition's own induction principle. The scanner reads a **maximal run of
  decimal digit characters** and folds it, and its round trip is re-proved: a
  printed identifier lexes back to the same natural number, across the whitespace
  separators, with the printer no longer injective on characters (leading
  structure is carried by the separators, the value by the base-10 fold).

  The security claim survives: the same `parse`/`scheck` pipeline runs on top, so
  an accepted decimal-character source still leaks nothing of the untrusted input
  (`decimal_source_injection_free`). With this, brick 25's residual is closed —
  identifiers carry genuine decimal values, not run lengths.
-/
import ConfTyping.LexSource

namespace ConfTyping

/-! ## A verified decimal codec -/

/-- Base-10 value of a big-endian digit list: `[1,2,3] ↦ 123`. -/
def ofDigits (ds : List (Fin 10)) : Nat := ds.foldl (fun acc d => acc * 10 + d.val) 0

theorem ofDigits_snoc (ds : List (Fin 10)) (d : Fin 10) :
    ofDigits (ds ++ [d]) = ofDigits ds * 10 + d.val := by
  simp [ofDigits, List.foldl_append]

/-- Big-endian decimal digits of a natural number (no leading zeros; `0 ↦ [0]`). -/
def toDigits (n : Nat) : List (Fin 10) :=
  if h : n < 10 then [⟨n, h⟩]
  else toDigits (n / 10) ++ [⟨n % 10, Nat.mod_lt n (by omega)⟩]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem toDigits_ne_nil (n : Nat) : toDigits n ≠ [] := by
  rw [toDigits]; split
  · simp
  · simp

/-- **Codec round trip.** Reading the decimal digits of any natural number
    recovers it — `ofDigits` is a left inverse of `toDigits`. -/
theorem ofDigits_toDigits (n : Nat) : ofDigits (toDigits n) = n := by
  induction n using toDigits.induct with
  | case1 n h => rw [toDigits]; simp [h, ofDigits]
  | case2 n h ih =>
      rw [toDigits, dite_eq_right h, ofDigits_snoc, ih]
      simp only [Fin.val_mk]
      omega

/-! ## A decimal alphabet -/

/-- Source characters: keyword letters, a semicolon, a **decimal digit**, a space. -/
inductive DCh where
  | li | ln | lc | lo | la | le | lm   -- keyword letters (i,n,c,o,a,e,m)
  | dsemi                              -- `;`
  | ddig : Fin 10 → DCh                -- a decimal digit 0–9
  | dsp                                -- a space
deriving DecidableEq

/-- The lexeme of a token; an identifier is its decimal digits, not a unary run. -/
def printTokD : Tok → List DCh
  | .kwInput => [.li, .ln]
  | .kwConst => [.lc, .lo]
  | .kwCat   => [.lc, .la]
  | .kwEmit  => [.le, .lm]
  | .semi    => [.dsemi]
  | .id n    => (toDigits n).map DCh.ddig

def printD : List Tok → List DCh
  | []      => []
  | t :: ts => printTokD t ++ .dsp :: printD ts

/-! ## The maximal-munch scanner with a decimal reader -/

/-- Collect a maximal leading run of decimal digit characters, big-endian. -/
def spanDigits : List DCh → List (Fin 10) × List DCh
  | .ddig d :: r => let (ds, rest) := spanDigits r; (d :: ds, rest)
  | r            => ([], r)

def readTokD : List DCh → Option (Tok × List DCh)
  | .li :: .ln :: r => some (.kwInput, r)
  | .lc :: .lo :: r => some (.kwConst, r)
  | .lc :: .la :: r => some (.kwCat, r)
  | .le :: .lm :: r => some (.kwEmit, r)
  | .dsemi :: r     => some (.semi, r)
  | .ddig d :: r    => let (ds, rest) := spanDigits (.ddig d :: r); some (.id (ofDigits ds), rest)
  | _               => none

def lexFuelD : Nat → List DCh → List Tok
  | 0,    _      => []
  | _+1,  []     => []
  | f+1,  c :: r =>
      if c = DCh.dsp then lexFuelD f r
      else match readTokD (c :: r) with
           | some (t, rest) => t :: lexFuelD f rest
           | none           => []

def lexD (l : List DCh) : List Tok := lexFuelD l.length l

/-! ## Scanner correctness -/

/-- A digit run followed by a non-digit reads back exactly (maximal munch). -/
theorem spanDigits_map (ds : List (Fin 10)) (c : DCh) (hc : ∀ d, c ≠ .ddig d) (r : List DCh) :
    spanDigits (ds.map DCh.ddig ++ c :: r) = (ds, c :: r) := by
  induction ds with
  | nil =>
      simp only [List.map_nil, List.nil_append]
      cases c <;> first | rfl | exact absurd rfl (hc _)
  | cons d ds ih =>
      simp only [List.map_cons, List.cons_append, spanDigits, ih]

/-- Reading a printed token off `lexeme ++ ' ' :: rest` recovers it — the digit
    case combines maximal munch with the codec round trip. -/
theorem readTokD_printTokD (t : Tok) (r : List DCh) :
    readTokD (printTokD t ++ .dsp :: r) = some (t, .dsp :: r) := by
  cases t with
  | kwInput => rfl
  | kwConst => rfl
  | kwCat   => rfl
  | kwEmit  => rfl
  | semi    => rfl
  | id n =>
      obtain ⟨d0, ds, hds⟩ : ∃ d0 ds, toDigits n = d0 :: ds := by
        cases h : toDigits n with
        | nil => exact absurd h (toDigits_ne_nil n)
        | cons d0 ds => exact ⟨d0, ds, rfl⟩
      show readTokD ((toDigits n).map DCh.ddig ++ .dsp :: r) = some (.id n, .dsp :: r)
      rw [hds]
      simp only [List.map_cons, List.cons_append, readTokD, spanDigits,
        spanDigits_map ds .dsp (fun d => DCh.noConfusion) r]
      rw [← hds, ofDigits_toDigits]

theorem printTokD_ne_sp (t : Tok) : ∃ c r, printTokD t = c :: r ∧ c ≠ DCh.dsp := by
  cases t with
  | kwInput => exact ⟨_, _, rfl, by decide⟩
  | kwConst => exact ⟨_, _, rfl, by decide⟩
  | kwCat   => exact ⟨_, _, rfl, by decide⟩
  | kwEmit  => exact ⟨_, _, rfl, by decide⟩
  | semi    => exact ⟨_, _, rfl, by decide⟩
  | id n    =>
      obtain ⟨d0, ds, hds⟩ : ∃ d0 ds, toDigits n = d0 :: ds := by
        cases h : toDigits n with
        | nil => exact absurd h (toDigits_ne_nil n)
        | cons d0 ds => exact ⟨d0, ds, rfl⟩
      exact ⟨.ddig d0, ds.map DCh.ddig, by simp [printTokD, hds], by intro h; exact DCh.noConfusion h⟩

/-- **Scanner correctness (round trip), fuel-parametric.** -/
theorem lexFuelD_printD :
    ∀ (ts : List Tok) (fuel : Nat), (printD ts).length ≤ fuel →
      lexFuelD fuel (printD ts) = ts := by
  intro ts
  induction ts with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons t ts ih =>
      intro fuel hf
      obtain ⟨c, cs, hpt, hc⟩ := printTokD_ne_sp t
      have hlen : (printD (t :: ts)).length
          = (printTokD t).length + 1 + (printD ts).length := by
        simp only [printD, List.length_append, List.length_cons]; omega
      have hpos : (printTokD t).length ≥ 1 := by rw [hpt]; simp
      cases fuel with
      | zero => rw [hlen] at hf; omega
      | succ f =>
          have hhead : printD (t :: ts) = c :: (cs ++ .dsp :: printD ts) := by
            simp only [printD, hpt, List.cons_append]
          rw [hhead]
          simp only [lexFuelD, ite_eq_right hc]
          have hread : readTokD (c :: (cs ++ .dsp :: printD ts))
              = some (t, .dsp :: printD ts) := by
            have h := readTokD_printTokD t (printD ts)
            rw [hpt] at h; simp only [List.cons_append] at h; exact h
          simp only [hread]
          have hf1 : (printD ts).length + 1 ≤ f := by rw [hlen] at hf; omega
          cases f with
          | zero => omega
          | succ g =>
              have hstep : lexFuelD (g + 1) (DCh.dsp :: printD ts)
                  = lexFuelD g (printD ts) := rfl
              rw [hstep, ih g (by omega)]

/-- **Scanner correctness (round trip).** -/
theorem lexD_printD (ts : List Tok) : lexD (printD ts) = ts :=
  lexFuelD_printD ts (printD ts).length (Nat.le_refl _)

/-! ## End to end: from decimal source characters to injection-freedom -/

/-- **The security guarantee, on decimal source characters.** If a decimal-digit
    source lexes and parses to a program the taint checker accepts, the emitted
    output is a function of the trusted program alone. -/
theorem decimal_source_injection_free {chars : List DCh} {c : SCmd} {T : List Nat}
    (hlex : parse (lexD chars) = some c) (hchk : scheck [] c = some T)
    (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp c (σ₀, [])).2 = (sexec inp' c (σ₀, [])).2 :=
  source_injection_free hlex hchk inp inp' σ₀

/-! ## Witnesses: multi-digit decimal identifiers -/

/-- `input 12 ; cat 45 3 12 ; emit 45` — multi-digit ids; the tainted input `12`
    flows into the query `45` (via `cat`'s source `12`), which is emitted. -/
def unsafeToksD : List Tok :=
  [.kwInput, .id 12, .semi, .kwCat, .id 45, .id 3, .id 12, .semi, .kwEmit, .id 45]

def unsafeDecimal : List DCh := printD unsafeToksD

/-- **It lexes** back — the scanner reads `12`, `45`, `3` as single decimal
    identifiers across the separators, not digit-by-digit. -/
theorem unsafe_decimal_lexes : lexD unsafeDecimal = unsafeToksD := lexD_printD unsafeToksD

/-- **It lexes and parses** to the expected program. -/
theorem unsafe_decimal_parses :
    parse (lexD unsafeDecimal) = some (.seq (.input 12) (.seq (.cat 45 3 12) (.one (.emit 45)))) := by
  rw [unsafe_decimal_lexes]; decide

/-- **And the checker rejects it** — injection caught, from a decimal source. -/
theorem unsafe_decimal_rejected :
    scheck [] (.seq (.input 12) (.seq (.cat 45 3 12) (.one (.emit 45)))) = none := by decide

/-- A safe decimal source `input 7 ; const 20 ; emit 20`: injection-free end to
    end from its multi-digit characters. -/
def safeToksD : List Tok :=
  [.kwInput, .id 7, .semi, .kwConst, .id 20, .semi, .kwEmit, .id 20]

def safeDecimal : List DCh := printD safeToksD

theorem safe_decimal_parses :
    parse (lexD safeDecimal) = some (.seq (.input 7) (.seq (.const 20) (.one (.emit 20)))) := by
  rw [show lexD safeDecimal = safeToksD from lexD_printD safeToksD]; decide

theorem safe_decimal_accepted :
    (scheck [] (.seq (.input 7) (.seq (.const 20) (.one (.emit 20))))).isSome = true := by decide

theorem safe_decimal_injection_free (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp (.seq (.input 7) (.seq (.const 20) (.one (.emit 20)))) (σ₀, [])).2
      = (sexec inp' (.seq (.input 7) (.seq (.const 20) (.one (.emit 20)))) (σ₀, [])).2 := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp safe_decimal_accepted
  exact decimal_source_injection_free safe_decimal_parses hT inp inp' σ₀

end ConfTyping
