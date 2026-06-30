/-
  The transport calculus — a common interface for transport theorems, with its composition law.

  A certified transport morphism (`Bridge`) is a map bundled with a *certificate*:
  a grade `c` and a proof that the map contracts the ambient distance by `c`.
  Composition is composition *of certificates*: it MULTIPLIES the grades and
  threads the two contraction proofs into the composite's — accumulation is the
  primitive, never silent discharge.

  ── Eighth catch, delivered by a real instance (not by me) ──
  v1 of this file used a single type `G` for both the grade and the distance,
  with one `mul : G → G → G`. That was over-identification: mathlib's actual
  `LipschitzWith` carries grades in `ℝ≥0` and distances in `ℝ≥0∞` — TWO types,
  the certificate a scalar *action* of the grade on the distance. The `Nat`
  instance hid this because there grade and distance coincide (`M = D`). The
  real instance does not *refute* the single-type version (it fits via the
  coercion `ℝ≥0 ↪ ℝ≥0∞`) — it reveals the conflation. The faithful structure,
  below, separates a grade monoid `M` acting monotonically on a distance order
  `D`; `Nat` is recovered as the degenerate `M = D` coincidence.

  Mathlib-free, by design: the corrected interface compiles with no reals and no
  measure theory, so that structure is incidental to it. The Markov-kernel /
  Dobrushin instance (`M = ℝ≥0`, `D = ℝ≥0∞`, `act = ↑· * ·`, contraction = the
  strong data-processing inequality — not in mathlib, a real formalization) is a
  separate artifact; the interface here only has to *receive* it.
-/

namespace TransportCalculus

/-- The earned abstraction, corrected by contact with `LipschitzWith`: a grade
    monoid `M` acting on a distance order `D`. Exactly what `Bridge.comp` uses —
    grade composition `mul`, a monotone action `act`, transitivity. No addition,
    no triangle inequality, no identity, no `M = D`. A bundle passed explicitly,
    so the operations the proof needs are visible and nothing is conflated. -/
structure GradedAction (M : Type) (D : Type) where
  mul      : M → M → M                                   -- grade composition
  le       : D → D → Prop                                -- distance order
  act      : M → D → D                                   -- a grade scales a distance
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  act_mul  : ∀ m₁ m₂ d, act (mul m₁ m₂) d = act m₁ (act m₂ d)
  act_mono : ∀ (m : M) {d d' : D}, le d d' → le (act m d) (act m d')

/-- A **certified transport morphism**: a map, a grade `cert : M`, and a
    certificate that the map contracts the distance `dist : X → X → D` by the
    *action* of `cert`. The map bundled with its hypotheses, not the map alone. -/
structure Bridge (X M D : Type) (GA : GradedAction M D) (dist : X → X → D) where
  map       : X → X
  cert     : M
  contracts : ∀ x y, GA.le (dist (map x) (map y)) (GA.act cert (dist x y))

/-- **The composition law.** Composing two certified bridges yields
    a certified bridge whose grade is the *product* of the two, and whose
    contraction proof is *threaded from* the two inputs via the action's
    compatibility `act_mul` and monotonicity. Drop the multiplication and the
    certificate no longer type-checks. -/
def Bridge.comp {X M D : Type} {GA : GradedAction M D} {dist : X → X → D}
    (g f : Bridge X M D GA dist) : Bridge X M D GA dist where
  map   := g.map ∘ f.map
  cert := GA.mul g.cert f.cert
  contracts := fun x y => by
    have h1 := g.contracts (f.map x) (f.map y)
    have h2 := GA.act_mono g.cert (f.contracts x y)
    have h3 := GA.le_trans h1 h2
    rw [← GA.act_mul] at h3
    exact h3

/-- The composite's grade is exactly the product — accumulation, definitionally. -/
theorem Bridge.comp_cert {X M D : Type} {GA : GradedAction M D} {dist : X → X → D}
    (g f : Bridge X M D GA dist) :
    (g.comp f).cert = GA.mul g.cert f.cert := rfl

/-! ## The hunt for a non-associative accumulation witness — resolved negatively

The proposed boundary "find a transport phenomenon whose accumulation is
non-associative" is malformed: the interface **cannot host** non-associativity.
`act_mul` makes `act` a homomorphism `(M, mul) → (D → D, ∘)`, and function
composition is associative — so the two bracketings of any triple act *identically
on every distance*. A non-associative `mul` is therefore **unobservable** through
any `Bridge`, and a *faithful* action forces `mul` itself associative. So no
`Bridge` can ever witness non-associativity; the witness does not exist, by a
two-line proof rather than by failure to search. -/

/-- The accumulation is associative *as observed* — for any `mul` whatsoever. -/
theorem GradedAction.act_assoc {M D : Type} (GA : GradedAction M D) (a b c : M) (d : D) :
    GA.act (GA.mul (GA.mul a b) c) d = GA.act (GA.mul a (GA.mul b c)) d := by
  simp only [GA.act_mul]

/-- And a *faithful* action forces `mul` genuinely associative: `act_mul` plus
    injectivity ⟹ associativity. So one cannot even *construct* a `GradedAction`
    that witnesses non-associativity with a faithful action — the `act_mul`
    obligation would be unprovable. -/
theorem GradedAction.mul_assoc_of_faithful {M D : Type} (GA : GradedAction M D)
    (faithful : ∀ m m', (∀ d, GA.act m d = GA.act m' d) → m = m')
    (a b c : M) : GA.mul (GA.mul a b) c = GA.mul a (GA.mul b c) :=
  faithful _ _ (fun d => GA.act_assoc a b c d)

/-! ## Where non-factorization actually lives: lossy summaries, not phenomena

The DP case locates the real boundary precisely, and it is *not* a phenomenon.

- The privacy-loss distribution / f-DP trade-off function is a **composable
  invariant**: it tensors associatively (Dong–Roth–Su), and advanced composition
  is a *corollary*. Advanced composition's bound is uniform over all `(ε,δ)`
  mechanisms — it depends on the count and the certificates, not on the maps — so
  it factors through this invariant. DP, on the f-DP/PLD certificate, is **inside**.
- `(ε, δ)` is a **lossy projection** of that invariant. Two mechanisms with equal
  `(ε,δ)` but different privacy-loss distributions compose to different `(ε',δ')`,
  so `(ε,δ)` admits **no** `mul` reconstructing the composite — it is not a
  composable invariant.

So non-factorization is a property of the *chosen summary*, not the phenomenon —
the exact separability story of `../conf-typing` (the join composes; the lossy
per-channel projection does not), now a third time. The witness below makes it
abstract and mathlib-free: a composable monoid whose lossy summary provably
does not compose. -/

/-- The composable invariant: `ℕ × ℕ` under coordinatewise addition (associative,
    a clean monoid — stands in for the PLD / the join). -/
def invar (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

/-- A lossy (non-injective) summary of it: the product of coordinates — stands in
    for `(ε,δ)` / a per-channel projection. -/
def summary (a : Nat × Nat) : Nat := a.1 * a.2

/-- **The summary is not a composable invariant.** No binary operation on
    summaries reconstructs the composite summary from the components': `(1,2)` and
    `(2,1)` share summary `2`, yet composed (via `invar`) with `(1,0)` their
    summaries diverge — `4 ≠ 3`. This is the `(ε,δ)`-vs-PLD obstruction in
    miniature, and the transport-side instance of `conf-typing`'s separability: a
    lossy projection of a composable invariant need not itself compose. The
    *invariant* fits the interface; the *summary* is the genuine non-example — and
    it is a non-example of "this summary composes," not of `GradedAction`. -/
theorem summary_not_composable :
    ¬ ∃ muS : Nat → Nat → Nat, ∀ a b, muS (summary a) (summary b) = summary (invar a b) := by
  rintro ⟨muS, h⟩
  have h1 : muS 2 0 = 4 := h (1, 2) (1, 0)
  have h2 : muS 2 0 = 3 := h (2, 1) (1, 0)
  omega

/-! ## The universal `GradedAction` — factorization is *forced* (the transport Cayley)

"Is factorizability forced, the way faithfulness forces associativity?" Yes — via
a universal instance. The monotone self-maps of `D` under composition form a
`GradedAction`, and **every** `GradedAction`'s `act` is a monoid homomorphism into
it (`repr`, `repr_mul`). So the certificates of any instance are a *representation*
of monotone-self-map monoids; `act_assoc` is that representation landing in an
associative monoid (`∘`), and `mul_assoc_of_faithful` is a faithful representation
being injective — literally Cayley.

Consequence (`Bridge.ofModulus`): any map carrying a monotone `D`-bound on its
distance effect — and the *modulus of continuity* is one, by construction — is a
`Bridge` in `universalGA`. So every **monotone-bounded** contraction-transport
phenomenon factors: the interface's `Rbad` is empty *as a theorem* on this class,
not as a search result. What is **not** ruled out: a phenomenon whose distance
admits no monotone modulus at all (a `D` lacking the suprema to form one) — there
the universal instance has nothing to represent, and that is exactly where any true
escapee must live. Located, not closed. -/

/-- Monotone self-maps of `(D, le)`. -/
structure Mono (D : Type) (le : D → D → Prop) where
  toFun : D → D
  mono  : ∀ {a b}, le a b → le (toFun a) (toFun b)

def Mono.comp {D : Type} {le : D → D → Prop} (φ ψ : Mono D le) : Mono D le where
  toFun := fun d => φ.toFun (ψ.toFun d)
  mono  := fun h => φ.mono (ψ.mono h)

theorem Mono.ext {D : Type} {le : D → D → Prop} {φ ψ : Mono D le}
    (h : φ.toFun = ψ.toFun) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

/-- **The universal `GradedAction`:** monotone self-maps of `D` under composition.
    `act_mul` is *definitional* — it is function composition. -/
def universalGA {D : Type} (le : D → D → Prop)
    (le_trans : ∀ {a b c}, le a b → le b c → le a c) : GradedAction (Mono D le) D where
  mul      := Mono.comp
  le       := le
  act      := fun φ d => φ.toFun d
  le_trans := le_trans
  act_mul  := fun _ _ _ => rfl
  act_mono := fun φ {_ _} h => φ.mono h

/-- **Factorization is forced.** Any map with a monotone modulus `φ` is a `Bridge`
    in `universalGA` — no proof work beyond the bound. The modulus of continuity is
    monotone by construction, so every monotone-bounded phenomenon factors. -/
def Bridge.ofModulus {X D : Type} {le : D → D → Prop}
    (le_trans : ∀ {a b c}, le a b → le b c → le a c) {dist : X → X → D}
    (f : X → X) (φ : Mono D le)
    (bound : ∀ x y, le (dist (f x) (f y)) (φ.toFun (dist x y))) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist where
  map       := f
  cert      := φ
  contracts := bound

/-- `act` packaged as a monotone self-map: the representation of a certificate. -/
def GradedAction.repr {M D : Type} (GA : GradedAction M D) (m : M) : Mono D GA.le :=
  ⟨GA.act m, fun h => GA.act_mono m h⟩

/-- **`act` is the representation homomorphism.** For any `GradedAction`, sending a
    certificate to its action is a monoid hom into `universalGA`. So every
    instance's certificates *represent* monotone-self-map monoids; `act_assoc` and
    `mul_assoc_of_faithful` are the standard facts about such a representation. -/
theorem GradedAction.repr_mul {M D : Type} (GA : GradedAction M D) (a b : M) :
    GA.repr (GA.mul a b) = (GA.repr a).comp (GA.repr b) :=
  Mono.ext (funext (fun d => GA.act_mul a b d))

/-! ## The non-monotone frontier dissolves into Cayley over a complete lattice

`f` factors through `universalGA` iff it has a *monotone dominator*, and the
canonical one is the modulus of continuity `ω_f(t) = ⨆ {dist(fx,fy) : dist x y ≤ t}`
— monotone by construction, dominating, **whenever the sup exists**. So the whole
"non-monotone escapee" question collapses to one line: does `D` have the suprema?

If `D` is a complete lattice (`sSup` on predicate-sets with the two universal
laws — passed explicitly, so the boundary is visible in the statement), `ω_f`
always exists, so **every** map factors. `ℝ≥0∞`, `ℕ∞`, every standard extended-
metric codomain is a complete lattice, so the escapee **cannot live in any
standard metric space** — it would need a `D` that is *not* a complete lattice,
with a modulus-set bounded but lacking a least upper bound. -/

def factors_of_completeness {X D : Type} (le : D → D → Prop)
    (le_refl : ∀ a, le a a)
    (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (sSup : (D → Prop) → D)
    (le_sSup : ∀ (S : D → Prop) a, S a → le a (sSup S))
    (sSup_le : ∀ (S : D → Prop) b, (∀ a, S a → le a b) → le (sSup S) b)
    (dist : X → X → D) (f : X → X) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist := by
  refine Bridge.ofModulus (le := le) (dist := dist) le_trans f ?φ ?bound
  case φ =>
    refine ⟨fun t => sSup (fun d => ∃ x y, le (dist x y) t ∧ d = dist (f x) (f y)), ?_⟩
    intro a b hab
    refine sSup_le _ _ (fun c hc => ?_)
    obtain ⟨x, y, hxy, rfl⟩ := hc
    exact le_sSup _ _ ⟨x, y, le_trans hxy hab, rfl⟩
  case bound =>
    intro x y
    exact le_sSup _ _ ⟨x, y, le_refl _, rfl⟩

/-! ## The degenerate instance that hid the conflation: `M = D = Nat`

Distance `|a-b|`, grade = Lipschitz constant — *both* `Nat`, the action *is*
multiplication. This is the `M = D` coincidence. The doubling map is Lipschitz-2;
two compose to Lipschitz-4, the grade multiplied, by `rfl`. -/

def natGA : GradedAction Nat Nat where
  mul      := Nat.mul
  le       := Nat.le
  act      := Nat.mul
  le_trans := Nat.le_trans
  act_mul  := Nat.mul_assoc
  act_mono := fun m {_ _} h => Nat.mul_le_mul (Nat.le_refl m) h

def dist (a b : Nat) : Nat := (a - b) + (b - a)

def double : Bridge Nat Nat Nat natGA dist where
  map   := fun n => 2 * n
  cert := 2
  contracts := fun x y => by
    show dist (2 * x) (2 * y) ≤ 2 * dist x y
    unfold dist
    omega

/-- Accumulation, concretely: two Lipschitz-2 bridges compose to Lipschitz-4. -/
example : (double.comp double).cert = 4 := rfl

end TransportCalculus
