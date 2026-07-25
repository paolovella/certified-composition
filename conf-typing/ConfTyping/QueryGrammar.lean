/-
  A fuller query grammar — brick 26: beyond a single literal.

  Brick 14 made injection real, but on the smallest possible grammar: one
  quote-delimited literal spliced into a two-piece template (`… = 'DATA'`). Its
  honest limit — named in VULN-COVERAGE as a depth follow-on — is a query with
  *more structure*. This brick generalizes the tokenizer argument to a template
  with **`n` literal slots**: `s₀ 'v₀' s₁ 'v₁' … 'v_{n-1}' s_n` — e.g.
  `… WHERE a='…' AND b='…'` — parameterized by a *vector* of values.

  The discipline is exactly brick 14's, now n-ary:
  * **parameterization** keeps the executed skeleton equal to the `n+1`
    structural pieces `S`, *by construction independent of the whole value
    vector* (`param_immune_N`), and for quote-free values it computes the
    intended structure (`param_correct_N` — the skeleton of the concatenated
    query is `S`, proved by induction over the interleaving with brick 14's
    `segs_append_q`/`segs_qfree`);
  * **concatenation** re-tokenizes the spliced string, so a quote in *any* slot
    displaces the structure (`concat_injectable_N`) — injection in an arbitrary
    literal position, as a theorem.

  Integrity noninterference with the real sink is then n-ary: the executed
  skeleton is invariant under any change to the value vector for the
  parameterized build (`param_noninterference_N`), and not for concatenation
  (`concat_leaks_N`).
-/
import ConfTyping.InjectionReal

namespace ConfTyping

/-! ## The n-ary builds -/

/-- Concatenation build over a value vector: interleave `n+1` structural pieces
    with `n` quote-wrapped values, then re-tokenize the whole string. With
    `S = [s₀,…,s_n]` and `V = [v₀,…,v_{n-1}]` this is
    `s₀ 'v₀' s₁ 'v₁' … 'v_{n-1}' s_n`. -/
def buildN : List Str → List Str → Str
  | s :: S, v :: V => s ++ .q :: (v ++ .q :: buildN S V)
  | s :: _, []     => s
  | [],     _      => []

/-- Parameterized build: the executed structure is the structural pieces `S`,
    *by construction* independent of the value vector (a prepared statement with
    `n` bound parameters). -/
def paramStructureN (S : List Str) (_V : List Str) : List Str := S

/-- The segment list a correct tokenization of `buildN S V` should produce:
    `[s₀, v₀, s₁, v₁, …, s_n]` — structural and data segments alternating. -/
def segsN : List Str → List Str → List Str
  | s :: S, v :: V => s :: v :: segsN S V
  | s :: _, []     => [s]
  | [],     _      => [[]]

/-- Every string in the list is quote-free. -/
def noQ (L : List Str) : Prop := ∀ s ∈ L, hasQ s = false

theorem noQ_tail {a : Str} {L : List Str} (h : noQ (a :: L)) : noQ L :=
  fun s hs => h s (by simp [hs])

theorem noQ_head {a : Str} {L : List Str} (h : noQ (a :: L)) : hasQ a = false :=
  h a (by simp)

/-! ## Tokenizing the concatenated query -/

/-- **The tokenizer recovers the alternating segments.** For quote-free pieces
    and a well-formed vector (`|S| = |V| + 1`), tokenizing `buildN S V` yields
    exactly the interleaving `segsN S V` — each value stays inside its own
    literal, so no structure leaks between slots. Proved by induction over the
    interleaving with brick 14's quote-split lemmas. -/
theorem segs_buildN : ∀ (V S : List Str), noQ S → noQ V → S.length = V.length + 1 →
    segs (buildN S V) = segsN S V := by
  intro V
  induction V with
  | nil =>
      intro S hS _ hlen
      match S, hlen with
      | [s], _ =>
          have hs : hasQ s = false := noQ_head hS
          show segs s = [s]
          exact segs_qfree hs
  | cons v V ih =>
      intro S hS hV hlen
      match S, hlen with
      | s :: S', hlen =>
          have hs : hasQ s = false := noQ_head hS
          have hv : hasQ v = false := noQ_head hV
          have hlen' : S'.length = V.length + 1 := by
            simp only [List.length_cons] at hlen; omega
          show segs (s ++ .q :: (v ++ .q :: buildN S' V)) = s :: v :: segsN S' V
          rw [segs_append_q hs, segs_append_q hv, ih S' (noQ_tail hS) (noQ_tail hV) hlen']

/-- The even-indexed segments of the interleaving are exactly the structural
    pieces `S`. -/
theorem evens_segsN : ∀ (V S : List Str), S.length = V.length + 1 →
    evens (segsN S V) = S := by
  intro V
  induction V with
  | nil =>
      intro S hlen
      match S, hlen with
      | [s], _ => rfl
  | cons v V ih =>
      intro S hlen
      match S, hlen with
      | s :: S', hlen =>
          have hlen' : S'.length = V.length + 1 := by
            simp only [List.length_cons] at hlen; omega
          show evens (s :: v :: segsN S' V) = s :: S'
          simp only [evens, ih S' hlen']

/-! ## Parameterization is injection-safe, n-ary -/

/-- **Parameterization is immune to injection** across the whole value vector —
    the executed structure never depends on any value. -/
theorem param_immune_N (S V V' : List Str) :
    paramStructureN S V = paramStructureN S V' := rfl

/-- **Parameterization computes the right structure.** For quote-free values and
    a well-formed vector, the parameterized structure equals the skeleton a
    correct execution of the concatenated query would produce — so it is faithful
    to the template, and stays immune when values are adversarial. -/
theorem param_correct_N {S V : List Str}
    (hS : noQ S) (hV : noQ V) (hlen : S.length = V.length + 1) :
    skeleton (buildN S V) = paramStructureN S V := by
  simp only [skeleton, segs_buildN V S hS hV hlen, evens_segsN V S hlen, paramStructureN]

/-- **Parameterization satisfies integrity noninterference**, n-ary: the executed
    structure is invariant under any change to the value vector. -/
theorem param_noninterference_N (S : List Str) :
    ∀ V V', paramStructureN S V = paramStructureN S V' :=
  fun V V' => param_immune_N S V V'

/-! ## Concatenation is injectable — in an arbitrary slot -/

/-- A three-piece template (`s₀ 'v₀' s₁ 'v₁' s₂`, two literal slots), a benign
    value vector, and a payload with a quote in the *first* slot. -/
def gS : List Str := [[.c 1], [.c 2], [.c 3]]
def gBenign : List Str := [[.c 0], [.c 0]]
def gPayload : List Str := [[.q, .c 4], [.c 0]]   -- `'` breaks out of slot 0

/-- **Concatenation is injectable in an arbitrary literal position.** With the
    same trusted multi-slot template, a benign vector and a payload with a quote
    in one slot produce *different skeletons* — the payload's text lands in a
    structural position and the following structure is displaced. Injection in a
    non-final literal, as a theorem. -/
theorem concat_injectable_N :
    skeleton (buildN gS gBenign) ≠ skeleton (buildN gS gPayload) := by decide

/-- The benign vector tokenizes back to the template structure — the injection is
    the *difference*, not mere nonequality to `S`. -/
theorem concat_benign_correct : skeleton (buildN gS gBenign) = gS := by decide

/-- **Concatenation violates integrity noninterference**, n-ary. -/
theorem concat_leaks_N :
    ∃ (S V V' : List Str), skeleton (buildN S V) ≠ skeleton (buildN S V') :=
  ⟨gS, gBenign, gPayload, concat_injectable_N⟩

end ConfTyping
