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

/-! ## Carrying several certificates at once — the product action

Five instance families now inhabit the interface (Lipschitz, Hölder, finite and
measure-theoretic Dobrushin, quantum channels), and the security program adds cost
budgets. Each accumulates *one* kind of certificate. But a real artifact wants a
**bundle**: this map is 2-Lipschitz *and* costs at most 40 *and* mediates every
access. Until now the interface could not say that.

The product supplies it, and — this is the content — the composition law stays the
same one: `Bridge.comp` on a product bridge is componentwise `Bridge.comp`, so
accumulating a bundle is accumulating each certificate separately, with no new
proof obligation and no interaction term. -/

/-- The **product** of two graded actions: two certificates carried side by side,
    ordered and acted on componentwise. -/
def GradedAction.prod {M₁ D₁ M₂ D₂ : Type}
    (GA₁ : GradedAction M₁ D₁) (GA₂ : GradedAction M₂ D₂) :
    GradedAction (M₁ × M₂) (D₁ × D₂) where
  mul m m'  := (GA₁.mul m.1 m'.1, GA₂.mul m.2 m'.2)
  le  d d'  := GA₁.le d.1 d'.1 ∧ GA₂.le d.2 d'.2
  act m d   := (GA₁.act m.1 d.1, GA₂.act m.2 d.2)
  le_trans  := fun h₁ h₂ => ⟨GA₁.le_trans h₁.1 h₂.1, GA₂.le_trans h₁.2 h₂.2⟩
  act_mul   := fun m₁ m₂ d => by
    simp only [Prod.mk.injEq]
    exact ⟨GA₁.act_mul m₁.1 m₂.1 d.1, GA₂.act_mul m₁.2 m₂.2 d.2⟩
  act_mono  := by
    intro m d d' h
    exact ⟨GA₁.act_mono m.1 h.1, GA₂.act_mono m.2 h.2⟩

/-- **Bundling.** Two bridges over the *same map* pair into one bridge in the product
    action, whose certificate is the pair. The `hmap` hypothesis is the whole content
    of "the same artifact carries both guarantees". -/
def Bridge.pair {X M₁ D₁ M₂ D₂ : Type}
    {GA₁ : GradedAction M₁ D₁} {GA₂ : GradedAction M₂ D₂}
    {d₁ : X → X → D₁} {d₂ : X → X → D₂}
    (b₁ : Bridge X M₁ D₁ GA₁ d₁) (b₂ : Bridge X M₂ D₂ GA₂ d₂)
    (hmap : b₂.map = b₁.map) :
    Bridge X (M₁ × M₂) (D₁ × D₂) (GA₁.prod GA₂) (fun x y => (d₁ x y, d₂ x y)) where
  map       := b₁.map
  cert      := (b₁.cert, b₂.cert)
  contracts := fun x y => ⟨b₁.contracts x y, by
    have := b₂.contracts x y; rwa [hmap] at this⟩

theorem Bridge.pair_cert {X M₁ D₁ M₂ D₂ : Type}
    {GA₁ : GradedAction M₁ D₁} {GA₂ : GradedAction M₂ D₂}
    {d₁ : X → X → D₁} {d₂ : X → X → D₂}
    (b₁ : Bridge X M₁ D₁ GA₁ d₁) (b₂ : Bridge X M₂ D₂ GA₂ d₂) (hmap : b₂.map = b₁.map) :
    (b₁.pair b₂ hmap).cert = (b₁.cert, b₂.cert) := rfl

/-- **Bundles accumulate componentwise.** Composing two paired bridges gives exactly
    the pair of the composites' certificates: no interaction term, no extra
    hypothesis. So carrying `n` guarantees through a composition costs `n` independent
    accumulations and nothing more — which is what makes bundling usable at scale.

    **Scope, added after a downstream counterexample.** This says the *composition* of
    a pair costs nothing extra. It does not say two properties can always be
    *established* independently. `conf-typing`'s stage 1j found a case where they
    cannot: noninterference of a heap dereference is conditional on memory safety
    (`ConfTyping.ni_and_memory_do_not_factor`), so the two certificates have to be
    built by one judgment indexed by the tracked set, and only then paired. Bundling
    the results is still free; deriving them separately is not always possible. -/
theorem Bridge.pair_comp_cert {X M₁ D₁ M₂ D₂ : Type}
    {GA₁ : GradedAction M₁ D₁} {GA₂ : GradedAction M₂ D₂}
    {d₁ : X → X → D₁} {d₂ : X → X → D₂}
    (g₁ f₁ : Bridge X M₁ D₁ GA₁ d₁) (g₂ f₂ : Bridge X M₂ D₂ GA₂ d₂)
    (hg : g₂.map = g₁.map) (hf : f₂.map = f₁.map) :
    ((g₁.pair g₂ hg).comp (f₁.pair f₂ hf)).cert
      = ((g₁.comp f₁).cert, (g₂.comp f₂).cert) := rfl

/-- And the bundled map is the bundled composite's map — the artifact is one artifact,
    not two travelling together. -/
theorem Bridge.pair_comp_map {X M₁ D₁ M₂ D₂ : Type}
    {GA₁ : GradedAction M₁ D₁} {GA₂ : GradedAction M₂ D₂}
    {d₁ : X → X → D₁} {d₂ : X → X → D₂}
    (g₁ f₁ : Bridge X M₁ D₁ GA₁ d₁) (g₂ f₂ : Bridge X M₂ D₂ GA₂ d₂)
    (hg : g₂.map = g₁.map) (hf : f₂.map = f₁.map) :
    ((g₁.pair g₂ hg).comp (f₁.pair f₂ hf)).map = (g₁.comp f₁).map := rfl

/-! ### Non-vacuity: a bundle whose two halves accumulate by different laws

The product would be uninteresting if both components had to accumulate the same
way. They do not — and this is the point of bundling. Below, one certificate is an
additive budget (`+`) and the other a worst-case bound (`max`); a single
`Bridge.comp` advances both, each by its own law. -/

/-- Additive budgets: costs add along a composition. -/
def addGA : GradedAction Nat Nat where
  mul      := (· + ·)
  le       := (· ≤ ·)
  act      := (· + ·)
  le_trans := fun h₁ h₂ => Nat.le_trans h₁ h₂
  act_mul  := fun a b c => Nat.add_assoc a b c
  act_mono := by intro m d d' h; omega

/-- Worst-case bounds: accumulation is `max`, not `+` — a genuinely different
    monoid on the same carrier. -/
def maxGA : GradedAction Nat Nat where
  mul      := max
  le       := (· ≤ ·)
  act      := max
  le_trans := fun h₁ h₂ => Nat.le_trans h₁ h₂
  act_mul  := fun a b c => Nat.max_assoc a b c
  act_mono := by
    intro m d d' h
    exact Nat.max_le.mpr ⟨Nat.le_max_left m d', Nat.le_trans h (Nat.le_max_right m d')⟩

def addBridge (k : Nat) : Bridge Nat Nat Nat addGA (fun x _ => x) where
  map       := id
  cert      := k
  contracts := fun x _ => Nat.le_add_left x k

def maxBridge (k : Nat) : Bridge Nat Nat Nat maxGA (fun x _ => x) where
  map       := id
  cert      := k
  contracts := fun x _ => Nat.le_max_right k x

/-- The bundle carries both certificates. -/
theorem bundle_cert : ((addBridge 3).pair (maxBridge 5) rfl).cert = (3, 5) := rfl

/-- **One composition, two accumulation laws.** The additive half adds (`3 + 4 = 7`),
    the worst-case half takes a maximum (`max 5 2 = 5`), and neither knows about the
    other. This is what `Bridge.pair_comp_cert` says, instantiated. -/
theorem bundle_accumulates_componentwise :
    (((addBridge 3).pair (maxBridge 5) rfl).comp
     ((addBridge 4).pair (maxBridge 2) rfl)).cert = (7, 5) := rfl

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

/-- **The right hypothesis — sharper than a complete lattice.** `ofModulus` does
    not need *all* suprema; it needs only that each **image-family** — the image
    distances over a down-set of `t` — has a *least upper bound* `sup t`. Then `f`
    factors, and leastness alone gives the modulus its monotonicity. This is the
    minimal directed-completeness condition the modulus requires; `factors_of_completeness`
    (complete lattice) and `factors_of_global_bound` (one global bound) are both
    special cases. -/
def factors_of_image_sups {X D : Type} (le : D → D → Prop)
    (le_refl : ∀ a, le a a)
    (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (dist : X → X → D) (f : X → X)
    (sup : D → D)
    (le_sup : ∀ t x y, le (dist x y) t → le (dist (f x) (f y)) (sup t))
    (sup_le : ∀ t b, (∀ x y, le (dist x y) t → le (dist (f x) (f y)) b) → le (sup t) b) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist := by
  refine Bridge.ofModulus (le := le) (dist := dist) le_trans f ⟨sup, ?_⟩ ?_
  · intro a b hab
    exact sup_le a (sup b) (fun x y hxy => le_sup b x y (le_trans hxy hab))
  · intro x y
    exact le_sup (dist x y) x y (le_refl _)

/-! ## Case (b), inhabited: an escapee over an incomplete distance

A map that factors through **no** `GradedAction`. The distance `D3` has a bottom
`dB` and two incomparable maximal elements `dP`, `dQ` with **no common upper
bound** — so `(D3, le3)` is not a complete lattice (`dP ⊔ dQ` does not exist). The
map `fP` expands the `dB`-pair to `dP` and the `dP`-pair to `dQ`; with `dB ≤ dP`,
monotonicity forces any dominator to satisfy `φ dP ≥ dP` **and** `φ dP ≥ dQ`, a
join `no_common_ub` forbids. So no monotone dominator exists — and since every
`GradedAction`'s `act` is monotone (`act_mono`), `fP` is hosted by none.

`fP` *does* have a sound non-monotone bound (each pair's image distance is a
concrete element), so it is a genuine bounded phenomenon, not a degenerate
unbounded one — exactly case (b). **Honest caveat:** `D3` is not a distance
*monoid* — a positively-ordered monoid would give `dP` and `dQ` the common upper
bound `dP + dQ`, restoring directedness and killing this (finite) obstruction. So
the escapee inhabits the interface *as formalized* (preorder `D`), and pinpoints
that directedness is the missing hypothesis; whether directedness kills *every*
escapee (an infinite obstruction may survive) is the residual. -/

inductive D3 where
  | dB | dP | dQ
deriving DecidableEq

def le3 : D3 → D3 → Prop
  | .dB, _   => True
  | .dP, .dP => True
  | .dQ, .dQ => True
  | _, _     => False

theorem le3_refl : ∀ a, le3 a a := by intro a; cases a <;> trivial

theorem le3_trans : ∀ {a b c}, le3 a b → le3 b c → le3 a c := by
  intro a b c h1 h2; cases a <;> cases b <;> cases c <;> simp_all [le3]

/-- `dP` and `dQ` have no common upper bound — `(D3, le3)` lacks the join. -/
theorem no_common_ub : ¬ ∃ u, le3 .dP u ∧ le3 .dQ u := by
  rintro ⟨u, hp, hq⟩; cases u <;> simp_all [le3]

inductive P4 where | a | b | c | e
deriving DecidableEq

def distP : P4 → P4 → D3
  | .a, .b => .dB
  | .c, .e => .dP
  | .a, .c => .dQ
  | _, _   => .dB

def fP : P4 → P4
  | .a => .c | .b => .e | .c => .a | .e => .c

/-- **The escapee: no monotone dominator.** Hence `fP` is a `Bridge` in no
    `GradedAction` over `(D3, le3)` — the transport `Rbad` is *inhabited*. -/
theorem escapee_no_monotone_dominator :
    ¬ ∃ φ : Mono D3 le3, ∀ x y, le3 (distP (fP x) (fP y)) (φ.toFun (distP x y)) := by
  rintro ⟨φ, h⟩
  have h1 : le3 .dP (φ.toFun .dB) := h .a .b
  have h2 : le3 .dQ (φ.toFun .dP) := h .c .e
  have hmono : le3 (φ.toFun .dB) (φ.toFun .dP) := φ.mono (show le3 .dB .dP from trivial)
  exact no_common_ub ⟨φ.toFun .dP, le3_trans h1 hmono, h2⟩

/-- **The escapee is *unbounded* — it is not a contraction at all.** `fP` has no
    global output bound: `dP` and `dQ` are both output distances with no common
    upper bound. So its image-family has no upper bound, i.e. `fP` is *not*
    bounded-distortion. The only escapee we can build is the non-contraction case;
    what excludes it from a directed distance is **boundedness**, not directedness.
    That reframes the frontier: the operative hypothesis is that image-families are
    bounded (better, have sups — `factors_of_image_sups`), not the algebra of `+`. -/
theorem escapee_unbounded : ¬ ∃ T, ∀ x y, le3 (distP (fP x) (fP y)) T := by
  rintro ⟨T, hT⟩
  exact no_common_ub ⟨T, hT .a .b, hT .c .e⟩

/-- The same, in interface terms: no `Bridge` in `universalGA` has map `fP`. -/
theorem escapee_not_in_universalGA :
    ¬ ∃ B : Bridge P4 (Mono D3 le3) D3 (universalGA le3 @le3_trans) distP, B.map = fP := by
  rintro ⟨B, hB⟩
  refine escapee_no_monotone_dominator ⟨B.cert, fun x y => ?_⟩
  have hc := B.contracts x y
  rw [hB] at hc
  exact hc

/-! ## Strengthening the interface: require a *directed* distance

A directed distance has a chosen common upper bound `cub a b` for any two elements
— which a positively-ordered monoid supplies for free (`cub a b := a + b`, with
`a, b ≤ a + b` by positivity). Every genuine `+`-distance is directed; `D3` is not.
Requiring directedness **excludes the escapee by fiat** (`no_directed_on_D3`), and
buys factorization for every map with a *globally bounded* output
(`factors_of_global_bound`) — which directedness supplies whenever the output range
is finite. What it does **not** settle: unbounded-output maps over a non-complete
directed `D` (the infinite obstruction) — that is the residual `(c)`. -/

/-- The strengthening: a chosen common upper bound, i.e. directedness. -/
structure Directed (D : Type) (le : D → D → Prop) where
  cub          : D → D → D
  le_cub_left  : ∀ a b, le a (cub a b)
  le_cub_right : ∀ a b, le b (cub a b)

/-- **Strengthening excludes the escapee.** `(D3, le3)` admits no `Directed`
    structure: `cub dP dQ` would be the common upper bound `no_common_ub` forbids.
    So an interface requiring a directed distance cannot host the `(b)` witness. -/
theorem no_directed_on_D3 : Directed D3 le3 → False :=
  fun dir => no_common_ub
    ⟨dir.cub .dP .dQ, dir.le_cub_left .dP .dQ, dir.le_cub_right .dP .dQ⟩

/-- **What directedness buys.** A single global upper bound `T` on all output
    distances ⇒ the map factors, via the *constant* modulus `φ ≡ T`. A directed
    `D` supplies such a `T` whenever the output range is finite (iterated `cub`);
    the escapee precisely lacks one — `dP`, `dQ` have no common bound, which a
    directed distance would always provide. -/
def factors_of_global_bound {X D : Type} (le : D → D → Prop)
    (le_refl : ∀ a, le a a)
    (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (dist : X → X → D) (f : X → X)
    (T : D) (hT : ∀ x y, le (dist (f x) (f y)) T) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist := by
  refine Bridge.ofModulus (le := le) (dist := dist) le_trans f ⟨fun _ => T, ?_⟩ ?_
  · intro _ _ _; exact le_refl T
  · intro x y; exact hT x y

/-! ## Trying to build the monoid escapee — the finite obstruction always dies

The frontier: can a directed distance (still more, a `+`-monoid) carry an *infinite*
image-family with no monotone selection? The attempt below shows the **finite**
half is closed by directedness *alone* (no completeness): fold the common upper
bound `cub` over any finite output list to get a global bound, then
`factors_of_global_bound`. So no finite obstruction escapes a directed distance —
the monoid's `cub` (its `+`) defeats every one. An escapee would have to be
genuinely infinite; every finite avenue resolves. (I could not build an infinite
one either — single chains are tracked by iterated `cub`, bounded families always
have upper bounds — so whether the `+`-monoid escapee exists is left open, with
this theorem closing the finite case it would have to avoid.) -/

/-- Fold a chosen common upper bound over a list. -/
def foldCub {D : Type} {le : D → D → Prop} (dir : Directed D le) : D → List D → D
  | acc, []      => acc
  | acc, d :: ds => foldCub dir (dir.cub acc d) ds

theorem le_acc_foldCub {D : Type} {le : D → D → Prop} (dir : Directed D le)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c) :
    ∀ (acc : D) (L : List D), le acc (foldCub dir acc L)
  | acc, []      => le_refl acc
  | acc, d :: ds => le_trans (dir.le_cub_left acc d)
                      (le_acc_foldCub dir le_refl le_trans (dir.cub acc d) ds)

theorem le_mem_foldCub {D : Type} {le : D → D → Prop} (dir : Directed D le)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c) (d : D) :
    ∀ (L : List D) (acc : D), d ∈ L → le d (foldCub dir acc L)
  | [], _, h => nomatch h
  | e :: es, acc, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_trans (dir.le_cub_right acc d)
          (le_acc_foldCub dir le_refl le_trans (dir.cub acc d) es)
      · exact le_mem_foldCub dir le_refl le_trans d es (dir.cub acc e) h'

/-- **No finite escapee in a directed distance.** If every output distance lies in
    `seed :: L` (finitely many), the fold of `cub` over them is a global bound, so
    the map factors — directedness *alone*, no completeness. Every finite
    obstruction resolves; the monoid's `cub` defeats it. -/
def directed_finite_factors {X D : Type} (le : D → D → Prop)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (dir : Directed D le) (dist : X → X → D) (f : X → X)
    (seed : D) (L : List D)
    (hcover : ∀ x y, dist (f x) (f y) = seed ∨ dist (f x) (f y) ∈ L) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist :=
  factors_of_global_bound le le_refl le_trans dist f (foldCub dir seed L)
    (fun x y => by
      rcases hcover x y with h | h
      · rw [h]; exact le_acc_foldCub dir le_refl le_trans seed L
      · exact le_mem_foldCub dir le_refl le_trans _ L seed h)

/-! ## Directed ⇏ dcpo, concretely — and not-dcpo is still not an escapee

The natural sufficient hypothesis for factoring is **dcpo** (directed *and*
directed-complete). A positive monoid gives directed (`+`) but need not give dcpo:
`ℚ≥0` under `+` is the standard witness. `Dm` below is a mathlib-free one: a
directed order (`⊤` bounds everything, so `cub ≡ ⊤` witnesses `Directed`) whose
chain `fin 0 ≤ fin 1 ≤ ⋯` is directed and bounded yet has **no least upper bound**
— `L`, `R` are incomparable minimal upper bounds (`Dm_chain_no_sup`). So
`Directed ⇏ dcpo`, and `factors_of_image_sups`' hypothesis is strictly stronger
than `Directed`. *But `Dm` still factors* — `⊤` overshoots every family
(`Dm_factors`). So not-dcpo is necessary but **not sufficient** for an escapee:
here the missing sup is overshootable. -/

inductive Dm where
  | fin : Nat → Dm
  | L | R | top

def leM : Dm → Dm → Prop
  | .fin m, .fin n => m ≤ n
  | .fin _, .L => True
  | .fin _, .R => True
  | .fin _, .top => True
  | .L, .L => True
  | .L, .top => True
  | .R, .R => True
  | .R, .top => True
  | .top, .top => True
  | _, _ => False

theorem leM_refl : ∀ a, leM a a
  | .fin n => Nat.le_refl n
  | .L => trivial | .R => trivial | .top => trivial

theorem leM_trans : ∀ {a b c}, leM a b → leM b c → leM a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all [leM] <;> omega

theorem leM_top : ∀ a, leM a .top
  | .fin _ => trivial | .L => trivial | .R => trivial | .top => trivial

/-- `Dm` is directed: `⊤` is a common upper bound of everything. -/
def dirM : Directed Dm leM where
  cub := fun _ _ => .top
  le_cub_left := fun a _ => leM_top a
  le_cub_right := fun _ b => leM_top b

/-- **`Dm` is not a dcpo:** the chain `fin n` is directed and bounded (by `L`, `R`)
    yet has no least upper bound — `L`, `R` are incomparable minimal ubs. -/
theorem Dm_chain_no_sup :
    ¬ ∃ s : Dm, (∀ n, leM (.fin n) s) ∧ (∀ u, (∀ n, leM (.fin n) u) → leM s u) := by
  rintro ⟨s, hub, hleast⟩
  cases s with
  | fin k => have h := hub (k + 1); simp only [leM] at h; omega
  | L => have h := hleast .R (fun _ => trivial); simp [leM] at h
  | R => have h := hleast .L (fun _ => trivial); simp [leM] at h
  | top => have h := hleast .L (fun _ => trivial); simp [leM] at h

/-- **Yet `Dm` still factors:** `⊤` overshoots, so every map into `Dm` has the
    constant modulus `⊤`. Not-dcpo is *not* an escapee — the missing sup is
    overshootable. -/
def Dm_factors {X : Type} (dist : X → X → Dm) (f : X → X) :
    Bridge X (Mono Dm leM) Dm (universalGA leM @leM_trans) dist :=
  factors_of_global_bound leM leM_refl @leM_trans dist f .top (fun _ _ => leM_top _)

/-! ## `factors_of_image_sups` is strictly non-minimal — image-suprema are not necessary

`Dm_factors` established that a *not-dcpo* distance can still factor. This sharpens
that into a refutation of the converse: the `factors_of_image_sups` hypothesis is
*sufficient but not necessary*, witnessed, not conjectured. Take the identity map on
`ℕ` with the distance `distMax a b = fin (max a b)`. At threshold `L` its output
family is the entire chain `{fin n : n}` — which by the `L`/`R` obstruction has **no**
least upper bound. So no `sup : Dm → Dm` can satisfy the theorem's hypotheses, yet the
map factors anyway (`Dm_factors`, through the overshoot `⊤`). The canonical
(least-upper-bound) dominator that `factors_of_image_sups` demands does not exist here;
a non-least one does the whole job. Requiring image-family suprema therefore discards
genuine instances — the operative condition is "*some* monotone dominator," of which
least-sups are one non-forced source. -/

/-- Distance whose image-family at threshold `L` is the whole supless chain `{fin n}`. -/
def distMax (a b : Nat) : Dm := .fin (max a b)

/-- **Image-family suprema are not necessary.** The identity on `ℕ` under `distMax`
    factors, but the `factors_of_image_sups` hypothesis is unsatisfiable: `sup L` would
    have to bound every `fin n` while sitting below both incomparable bounds `L` and
    `R`, which nothing does. Factorization runs entirely through a non-least dominator. -/
theorem image_sups_not_necessary :
    Nonempty (Bridge Nat (Mono Dm leM) Dm (universalGA leM @leM_trans) distMax) ∧
    ¬ ∃ sup : Dm → Dm,
        (∀ t x y, leM (distMax x y) t → leM (distMax x y) (sup t)) ∧
        (∀ t b, (∀ x y, leM (distMax x y) t → leM (distMax x y) b) → leM (sup t) b) := by
  refine ⟨⟨Dm_factors distMax id⟩, ?_⟩
  rintro ⟨sup, hle, hleast⟩
  -- `sup L` bounds the whole chain: each `fin n` occurs as `distMax n n`, all `≤ L`.
  have hub : ∀ n, leM (.fin n) (sup .L) := by
    intro n
    simpa [distMax] using hle .L n n (by simp [distMax, leM])
  -- both `L` and `R` bound the family (every `distMax x y` is a `fin _`), so `sup L`
  -- is below each — but nothing is below both `L` and `R` yet above every `fin n`.
  have hL : leM (sup .L) .L := hleast .L .L (fun x y _ => by simp [distMax, leM])
  have hR : leM (sup .L) .R := hleast .L .R (fun x y _ => by simp [distMax, leM])
  cases hs : sup .L with
  | fin k => have h := hub (k + 1); rw [hs] at h; simp only [leM] at h; omega
  | L => rw [hs] at hR; simp [leM] at hR
  | R => rw [hs] at hL; simp [leM] at hL
  | top => rw [hs] at hL; simp [leM] at hL

/-! ## The ℚ≥0 impossibility: a cofinal ℕ-ruler defeats every bounded escapee (no dcpo)

The residual frontier was: does a *directed, top-less, non-dcpo* distance admit a
bounded-image escapee? For `ℚ≥0` — the canonical such distance — the answer is **no**, and
the reason is not directed-completeness but a *coarse* substitute. `ℚ≥0` is Archimedean, so
the naturals `0 ≤ 1 ≤ 2 ≤ ⋯` form a monotone **cofinal ruler**: every element sits below
some `k n`. That ruler alone — no sups, no dcpo — rounds any bounded image-family up to a
*monotone* modulus. Send each threshold `t` to `k (least n whose ruler value bounds the
family at t)`: leastness makes the index monotone in `t` (a larger down-set is a superset,
so its least bounding index is not smaller), and cofinality makes `k` of it dominate. So over
any distance carrying such a ruler, every map whose image-families are bounded factors — and
`ℚ≥0` carries one while failing to be a dcpo.

This is a sufficient hypothesis **incomparable** to directed-completeness: `ℚ≥0` has the
ruler but is not a dcpo; an uncountable dcpo has completeness but no `ω`-ruler. So dcpo is not
*dethroned* — it and the ruler are two **incomparable** sufficient routes, and `ℚ≥0` travels
the ruler. dcpo remains the only known route for the **rulerless** case, so the residual does
not vanish, it **relocates**: to a distance that is *directed, non-dcpo, and carries no cofinal
`ω`-chain* — a far more exotic object than `ℚ≥0`, now the entire open frontier. This also
closes the boundedness gap left by `escapee_unbounded`: once the image-families are bounded
(excluding the unbounded `D3` escapee), the ruler — not completeness — factors them.

(`ℚ≥0` itself is not built here — a mathlib-free rationals-with-order is disproportionate and
orthogonal to the mechanism. The `Ruler` hypothesis is exactly the Archimedean-ruler property
`ℚ≥0` provably has; the one piece asserted in prose and not formalized is that `ℚ≥0` is not a
dcpo — the standard `√2` gap. `natRuler` witnesses only that `Ruler` is *inhabited* by a
genuine distance codomain: it is **not** the interesting not-dcpo instance. Although `ℕ` fails
strict directed-completeness, every *bounded* image-family in `ℕ` is finite, hence has a sup,
so `factors_of_image_sups` already covers `ℕ` and the ruler adds nothing there — `ℕ`'s
incompleteness lives only in *unbounded* chains, exactly what `bounded` excludes. The
interesting instance needs a bounded family with *no* sup, which `ℕ` lacks and `ℚ≥0` has.) -/

/-- Bounded upward linear search: least `n ∈ [start, start+fuel)` with `p n`, mathlib-free
    (Lean core lacks `Nat.find`, and this file imports nothing). -/
def sfind (p : Nat → Prop) [DecidablePred p] (start : Nat) : Nat → Nat
  | 0        => start
  | fuel + 1 => if p start then start else sfind p (start + 1) fuel

/-- The search result is `≤` any in-range witness — the minimality half. -/
theorem sfind_le (p : Nat → Prop) [DecidablePred p] :
    ∀ (fuel start m : Nat), p m → start ≤ m → m < start + fuel → sfind p start fuel ≤ m
  | 0,        _,     _, _,  hs, _ => hs
  | fuel + 1, start, m, hm, hs, _ => by
      show (if p start then start else sfind p (start + 1) fuel) ≤ m
      by_cases hp : p start
      · rw [if_pos hp]; exact hs
      · rw [if_neg hp]
        have hne : start ≠ m := fun h => hp (h ▸ hm)
        exact sfind_le p fuel (start + 1) m hm (by omega) (by omega)

/-- The search finds a witness whenever one lies in range — the existence half. -/
theorem sfind_p (p : Nat → Prop) [DecidablePred p] :
    ∀ (fuel start : Nat), (∃ m, start ≤ m ∧ m < start + fuel ∧ p m) → p (sfind p start fuel)
  | 0,        _,     ⟨_, hs, hlt, _⟩   => by exact absurd hs (by omega)
  | fuel + 1, start, ⟨m, hs, hlt, hpm⟩ => by
      show p (if p start then start else sfind p (start + 1) fuel)
      by_cases hp : p start
      · rw [if_pos hp]; exact hp
      · rw [if_neg hp]
        have hne : start ≠ m := fun h => hp (h ▸ hpm)
        exact sfind_p p fuel (start + 1) ⟨m, by omega, by omega, hpm⟩

/-- **Least witness, mathlib-free.** From a bare existence proof, a least element — the
    monotone-selection primitive the ruler argument needs, standing in for `Nat.find`. -/
theorem exists_least (p : Nat → Prop) [DecidablePred p] (H : ∃ n, p n) :
    ∃ μ, p μ ∧ ∀ m, p m → μ ≤ m := by
  obtain ⟨w, hw⟩ := H
  refine ⟨sfind p 0 (w + 1), sfind_p p (w + 1) 0 ⟨w, Nat.zero_le _, by omega, hw⟩, ?_⟩
  intro m hm
  rcases Nat.lt_or_ge m (w + 1) with h | h
  · exact sfind_le p (w + 1) 0 m hm (Nat.zero_le _) (by omega)
  · have : sfind p 0 (w + 1) ≤ w := sfind_le p (w + 1) 0 w hw (Nat.zero_le _) (by omega)
    omega

/-- A **cofinal monotone ℕ-ruler** on `(D, le)`: a coarse, countable, unbounded skeleton.
    `ℚ≥0` has one (`k n = n`, cofinal by the Archimedean property) yet is not a dcpo. -/
structure Ruler (D : Type) (le : D → D → Prop) where
  k       : Nat → D
  mono    : ∀ {i j}, i ≤ j → le (k i) (k j)
  cofinal : ∀ b, ∃ n, le b (k n)

/-- **The impossibility theorem.** A cofinal ℕ-ruler defeats every bounded-image escapee:
    if each image-family is bounded, the map factors — through `k (least bounding index)`,
    monotone by leastness, dominating by cofinality. No suprema, no directed-completeness.
    So an escapee over `ℚ≥0` (which has such a ruler) cannot exist — dcpo is one sufficient
    route, this is an incomparable second, and only the *rulerless* case still needs dcpo. -/
noncomputable def ruler_defeats_bounded_escapee {X D : Type} (le : D → D → Prop)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (R : Ruler D le) (dist : X → X → D) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) b) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist := by
  classical
  -- each threshold's image-family is bounded by *some* ruler value (bounded + cofinal)
  have hExists : ∀ t, ∃ n, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) (R.k n) := by
    intro t
    obtain ⟨b, hb⟩ := bounded t
    obtain ⟨n, hbn⟩ := R.cofinal b
    exact ⟨n, fun x y hxy => le_trans (hb x y hxy) hbn⟩
  -- `N t` = least ruler index bounding the family at `t`
  let N : D → Nat := fun t => Classical.choose (exists_least _ (hExists t))
  have hN : ∀ t, (∀ x y, le (dist x y) t → le (dist (f x) (f y)) (R.k (N t))) ∧
      (∀ m, (∀ x y, le (dist x y) t → le (dist (f x) (f y)) (R.k m)) → N t ≤ m) :=
    fun t => Classical.choose_spec (exists_least _ (hExists t))
  refine Bridge.ofModulus (le := le) (dist := dist) le_trans f ⟨fun t => R.k (N t), ?_⟩ ?_
  · -- monotone: a larger down-set is a superset, so its least bounding index is not smaller
    intro a b hab
    exact R.mono ((hN a).2 (N b) (fun x y hxy => (hN b).1 x y (le_trans hxy hab)))
  · -- dominates: the least bounding index bounds the family, at `t = dist x y`
    intro x y
    exact (hN (dist x y)).1 x y (le_refl _)

/-- `ℕ` carries a ruler (`k = id`) — the hypothesis is inhabited by a real distance codomain. -/
def natRuler : Ruler Nat Nat.le where
  k       := id
  mono    := fun h => h
  cofinal := fun b => ⟨b, Nat.le_refl b⟩

/-! ## Countable cofinality closes — and the uncountable residual is genuinely open

The `Ruler` hypothesis asked for a *monotone* cofinal ℕ-chain. Directedness makes the
monotonicity free: any cofinal ℕ-**sequence** `c` — no order on it assumed — becomes a ruler by
running the directed `cub` through it (`cofChain`, `Ruler.ofCofinalSeq`). So the operative
hypothesis is just **countable cofinality**, and `countable_cofinal_factors` needs only a
cofinal sequence — `ℚ≥0` has one (`ℕ ↪ ℚ≥0`), no Archimedean rounding by hand.

**Why this is specific to `ω`, and does not generalize for free.** Monotonizing a cofinal
ℕ-sequence uses only **finite** joins — exactly what directedness supplies (each `cofChain n`
is a finite `cub`-fold). The transfinite analogue is an **open proof, not a formalization
deferral**. To run the same selection along a cofinal `κ`-chain for uncountable `κ`, the limit
step needs *upper bounds of `<κ`-sized prefixes* — i.e. **`κ`-directedness** (every subset of
size `<κ` is bounded). Regular cofinality does **not** give this: a `<κ`-sized subset is
non-cofinal, but *non-cofinal ≠ bounded* in a merely directed order (`ℕ` is directed yet
unbounded). So "regular cofinality ⇒ factors" has a real hole at exactly that step; the
hypothesis the argument actually needs is `κ`-directedness, strictly stronger. (This note
originally went on to call the transfinite selection under `κ`-directedness "plausible —
unchecked, and unformalizable here (transfinite recursion, cardinals)". That was wrong on
both counts, and the next section is the correction: the theorem is *proved* there,
mathlib-free — `prefix_bounded_cofinal_factors`.)

**So the honest residual is the whole uncountable-cofinality realm**, not the smaller "singular
cofinality" — even the regular-uncountable case is open absent `κ`-directedness. It has
**neither a witness nor an impossibility proof**.

Formalized below: `κ = ω` (`cofChain` folds `cub` along ℕ — no ordinals, mathlib-free), which
covers every countably-generated distance, `ℚ≥0` included. -/

/-- Run the directed `cub` through a sequence: the monotone envelope of `c 0, …, c n`. -/
def cofChain {D : Type} {le : D → D → Prop} (dir : Directed D le) (c : Nat → D) : Nat → D
  | 0     => c 0
  | n + 1 => dir.cub (cofChain dir c n) (c (n + 1))

theorem cofChain_le_succ {D : Type} {le : D → D → Prop} (dir : Directed D le) (c : Nat → D) :
    ∀ n, le (cofChain dir c n) (cofChain dir c (n + 1)) :=
  fun _ => dir.le_cub_left _ _

theorem le_cofChain {D : Type} {le : D → D → Prop} (dir : Directed D le)
    (le_refl : ∀ a, le a a) (c : Nat → D) : ∀ n, le (c n) (cofChain dir c n)
  | 0     => le_refl (c 0)
  | _ + 1 => dir.le_cub_right _ _

theorem cofChain_mono {D : Type} {le : D → D → Prop} (dir : Directed D le)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c) (c : Nat → D) :
    ∀ {i j}, i ≤ j → le (cofChain dir c i) (cofChain dir c j) := by
  intro i j h
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (cofChain_le_succ dir c _)

/-- **Directedness monotonizes a cofinal sequence into a ruler.** No order on the sequence is
    assumed — the running `cub` supplies both monotonicity and cofinality. -/
def Ruler.ofCofinalSeq {D : Type} {le : D → D → Prop}
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (dir : Directed D le) (c : Nat → D) (hc : ∀ b, ∃ n, le b (c n)) : Ruler D le where
  k       := cofChain dir c
  mono    := cofChain_mono dir le_refl le_trans c
  cofinal := fun b => by
    obtain ⟨n, hn⟩ := hc b
    exact ⟨n, le_trans hn (le_cofChain dir le_refl c n)⟩

/-- **Countable cofinality suffices — no ruler-monotonicity assumed (the `κ = ω` case).** A
    directed distance with a merely cofinal ℕ-*sequence* factors every bounded-image map (the
    monotonization uses only finite `cub`-folds). So the ruler hypothesis is exactly countable
    cofinality; `ℚ≥0` (cofinal `ℕ`) is covered. The uncountable case does **not** follow — see
    the section note: the transfinite step needs `κ`-directedness, an open hypothesis gap. -/
noncomputable def countable_cofinal_factors {X D : Type} (le : D → D → Prop)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (dir : Directed D le) (c : Nat → D) (hc : ∀ b, ∃ n, le b (c n))
    (dist : X → X → D) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) b) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist :=
  ruler_defeats_bounded_escapee le le_refl le_trans
    (Ruler.ofCofinalSeq le_refl le_trans dir c hc) dist f bounded

/-! ## The transfinite selection, formalized — the residual shrinks to one hypothesis

The section note above claimed the transfinite analogue was "unformalizable here (transfinite
recursion, cardinals)". Both halves of that claim were wrong, and the error was load-bearing
for how open the residual looked. Split the ω-argument into its two halves and each
generalizes, mathlib-free:

- **Selection** (`wruler_defeats_bounded_escapee`): given a *monotone* cofinal chain over any
  well-ordered index (`WellIndex` — an order with a least witness for every inhabited
  predicate), the modulus is `k (least bounding index)`, exactly as at `ω`. The argument is
  per-threshold: it has **no limit steps at all**. What looked transfinite was never
  transfinite; nothing here is specific to `ℕ` except `exists_least`, and `WellIndex.least`
  is that property abstracted.
- **Monotonization** (`WRuler.ofCofinalFamily`): turning a *bare* cofinal `W`-family into a
  monotone chain is where recursion lives — `WellFounded.fix` (Lean core; well-foundedness is
  derived from least witnesses, `WellIndex.wf`) — and where the real hypothesis enters:
  `PrefixBounded`, every family indexed by an initial segment `{v // v ≤ w}` is bounded.
  That is `κ`-directedness stated without cardinals, and *weakened* to segment-indexed
  families — sharper than the classical hypothesis the prose version asked for.

`prefix_bounded_cofinal_factors` composes the halves: **a cofinal family over a well-ordered
index, on a prefix-bounded distance, factors every bounded-image map** — at every cofinality,
the theorem the note above called "only plausible". At `W = ℕ`, `prefixBounded_of_directed`
proves plain directedness already supplies `PrefixBounded` (segments are finite; `cub`-folds
bound them) — the formal content of "κ-directedness is free at ω" — and
`countable_cofinal_factors'` re-derives the countable case end-to-end from the general
theorem.

**What this does and does not close.** The residual is now exactly one hypothesis wide, with
proofs machine-checked on both sides of it: `PrefixBounded` ⇒ factors (any cofinality,
proved); directedness ⇒ `PrefixBounded` at `ω` (proved); at uncountable cofinality
directedness supplies only finite `cub`-folds, which do not bound infinite segments — no
theorem forces `PrefixBounded` there. Whether a directed-only distance of uncountable
cofinality can genuinely defeat every monotone selection — i.e. whether the gap between
`Directed` and `PrefixBounded` is inhabited by an escapee — remains open, with neither
witness nor impossibility proof. But the frontier is no longer "the whole uncountable realm":
it is that single gap. -/

/-- A well-ordered index, mathlib-free: reflexive, transitive, antisymmetric, with a **least
    witness for every inhabited predicate**. (Classically a well-order: least witnesses on
    pair-predicates give totality, and `WellIndex.wf` below derives well-foundedness.) -/
structure WellIndex (W : Type) where
  le          : W → W → Prop
  le_refl     : ∀ a, le a a
  le_trans    : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  least       : ∀ (p : W → Prop), (∃ w, p w) → ∃ μ, p μ ∧ ∀ m, p m → le μ m

/-- The strict order of a `WellIndex`. -/
def WellIndex.lt {W : Type} (WI : WellIndex W) (a b : W) : Prop :=
  WI.le a b ∧ ¬ WI.le b a

/-- Least witnesses make the strict order well-founded — the recursion
    `WRuler.ofCofinalFamily` runs on. (Classical: the least non-accessible element is
    accessible, since leastness puts it below any non-accessible strict predecessor.) -/
theorem WellIndex.wf {W : Type} (WI : WellIndex W) : WellFounded WI.lt := by
  constructor
  intro a
  refine Classical.byContradiction (fun ha => ?_)
  obtain ⟨μ, hμ, hleast⟩ := WI.least (fun w => ¬ Acc WI.lt w) ⟨a, ha⟩
  exact hμ (Acc.intro μ (fun v hv =>
    Classical.byContradiction (fun hv' => hv.2 (hleast v hv'))))

/-- `ℕ` is a `WellIndex` — `exists_least` is exactly the least-witness field. -/
def natWellIndex : WellIndex Nat where
  le          := Nat.le
  le_refl     := Nat.le_refl
  le_trans    := Nat.le_trans
  le_antisymm := Nat.le_antisymm
  least       := fun p hp => @exists_least p (fun n => Classical.propDecidable (p n)) hp

/-- A cofinal monotone chain over a well-ordered index — the transfinite ruler. -/
structure WRuler (W D : Type) (WI : WellIndex W) (le : D → D → Prop) where
  k       : W → D
  mono    : ∀ {i j}, WI.le i j → le (k i) (k j)
  cofinal : ∀ b, ∃ w, le b (k w)

/-- **The selection half is not transfinite.** A monotone cofinal chain over *any* well-ordered
    index defeats every bounded-image escapee, by exactly the `ω`-argument: send `t` to
    `k (least index bounding the image-family at t)` — leastness gives monotonicity, cofinality
    gives domination. Per-threshold; no limit steps, no recursion along the chain. -/
noncomputable def wruler_defeats_bounded_escapee {X W D : Type} (WI : WellIndex W)
    (le : D → D → Prop)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (R : WRuler W D WI le) (dist : X → X → D) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) b) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist := by
  classical
  -- each threshold's image-family is bounded by *some* chain value (bounded + cofinal)
  have hExists : ∀ t, ∃ w, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) (R.k w) := by
    intro t
    obtain ⟨b, hb⟩ := bounded t
    obtain ⟨w, hbw⟩ := R.cofinal b
    exact ⟨w, fun x y hxy => le_trans (hb x y hxy) hbw⟩
  -- `N t` = least chain index bounding the family at `t`
  let N : D → W := fun t => Classical.choose (WI.least _ (hExists t))
  have hN : ∀ t, (∀ x y, le (dist x y) t → le (dist (f x) (f y)) (R.k (N t))) ∧
      (∀ m, (∀ x y, le (dist x y) t → le (dist (f x) (f y)) (R.k m)) → WI.le (N t) m) :=
    fun t => Classical.choose_spec (WI.least _ (hExists t))
  refine Bridge.ofModulus (le := le) (dist := dist) le_trans f ⟨fun t => R.k (N t), ?_⟩ ?_
  · -- monotone: a larger down-set is a superset, so its least bounding index is not smaller
    intro a b hab
    exact R.mono ((hN a).2 (N b) (fun x y hxy => (hN b).1 x y (le_trans hxy hab)))
  · -- dominates: the least bounding index bounds the family, at `t = dist x y`
    intro x y
    exact (hN (dist x y)).1 x y (le_refl _)

/-- **`κ`-directedness, stated without cardinals** — and weakened to what the argument needs:
    every family indexed by an initial segment `{v // v ≤ w}` of the index is bounded.
    Segments are inclusive, hence inhabited; no separate seed element is needed. -/
def PrefixBounded {W D : Type} (WI : WellIndex W) (le : D → D → Prop) : Prop :=
  ∀ (w : W) (g : ∀ v, WI.le v w → D), ∃ b, ∀ v (h : WI.le v w), le (g v h) b

section
open Classical

/-- Monotonize a bare `W`-family: at each `w`, choose (via `PrefixBounded`) a bound of the
    already-monotonized strict predecessors together with `c` on the segment itself.
    `WellFounded.fix` (Lean core) is the transfinite recursion — no ordinals, no cardinals. -/
noncomputable def monotonize {W D : Type} (WI : WellIndex W) {le : D → D → Prop}
    (hpb : PrefixBounded WI le) (c : W → D) : W → D :=
  WI.wf.fix (fun w rec =>
    Classical.choose (hpb w (fun v _ => if h : WI.lt v w then rec v h else c v)))

theorem monotonize_eq {W D : Type} (WI : WellIndex W) {le : D → D → Prop}
    (hpb : PrefixBounded WI le) (c : W → D) (w : W) :
    monotonize WI hpb c w = Classical.choose
      (hpb w (fun v _ => if _h : WI.lt v w then monotonize WI hpb c v else c v)) :=
  WI.wf.fix_eq _ w

/-- The monotonized chain dominates the family it came from (the `v = w` slot of the choice). -/
theorem le_monotonize {W D : Type} (WI : WellIndex W) {le : D → D → Prop}
    (hpb : PrefixBounded WI le) (c : W → D) (w : W) :
    le (c w) (monotonize WI hpb c w) := by
  rw [monotonize_eq]
  have h := Classical.choose_spec
    (hpb w (fun v _ => if _h : WI.lt v w then monotonize WI hpb c v else c v)) w (WI.le_refl w)
  rw [dif_neg (fun hlt : WI.lt w w => hlt.2 (WI.le_refl w))] at h
  exact h

/-- The monotonized chain is monotone across a strict step (the `v < w` slots of the choice). -/
theorem monotonize_lt_mono {W D : Type} (WI : WellIndex W) {le : D → D → Prop}
    (hpb : PrefixBounded WI le) (c : W → D) {v w : W} (hvw : WI.lt v w) :
    le (monotonize WI hpb c v) (monotonize WI hpb c w) := by
  rw [monotonize_eq WI hpb c w]
  have h := Classical.choose_spec
    (hpb w (fun v _ => if _h : WI.lt v w then monotonize WI hpb c v else c v)) v hvw.1
  rw [dif_pos hvw] at h
  exact h

theorem monotonize_mono {W D : Type} (WI : WellIndex W) {le : D → D → Prop}
    (le_refl : ∀ a : D, le a a) (hpb : PrefixBounded WI le) (c : W → D)
    {i j : W} (hij : WI.le i j) :
    le (monotonize WI hpb c i) (monotonize WI hpb c j) := by
  by_cases h : WI.le j i
  · rw [WI.le_antisymm hij h]
    exact le_refl _
  · exact monotonize_lt_mono WI hpb c ⟨hij, h⟩

end

/-- **The monotonization half.** Under `PrefixBounded` — the cardinal-free `κ`-directedness —
    any cofinal family over a well-ordered index monotonizes into a `WRuler`: each value
    bounds all earlier values and its own `c`, so monotonicity and cofinality both hold.
    This is the limit step the `ω`-case did with finite `cub`-folds, now at any cofinality. -/
noncomputable def WRuler.ofCofinalFamily {W D : Type} (WI : WellIndex W) {le : D → D → Prop}
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (hpb : PrefixBounded WI le) (c : W → D) (hc : ∀ b, ∃ w, le b (c w)) :
    WRuler W D WI le where
  k       := monotonize WI hpb c
  mono    := fun hij => monotonize_mono WI le_refl hpb c hij
  cofinal := fun b => by
    obtain ⟨w, hw⟩ := hc b
    exact ⟨w, le_trans hw (le_monotonize WI hpb c w)⟩

/-- **The transfinite theorem the residual called "plausible — unchecked".** A cofinal family
    over any well-ordered index, on a prefix-bounded distance, factors every bounded-image
    map: selection (`wruler_defeats_bounded_escapee`) composed with monotonization
    (`WRuler.ofCofinalFamily`). The open residual is now exactly the hypothesis gap:
    directedness supplies `PrefixBounded` at `ω` (`prefixBounded_of_directed`) and is not
    known to at any uncountable cofinality. -/
noncomputable def prefix_bounded_cofinal_factors {X W D : Type} (WI : WellIndex W)
    (le : D → D → Prop)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (hpb : PrefixBounded WI le) (c : W → D) (hc : ∀ b, ∃ w, le b (c w))
    (dist : X → X → D) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) b) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist :=
  wruler_defeats_bounded_escapee WI le le_refl le_trans
    (WRuler.ofCofinalFamily WI le_refl le_trans hpb c hc) dist f bounded

/-- **Directedness supplies `PrefixBounded` at `ω`** — `ℕ`-segments are finite, and iterated
    `cub` bounds any finite family. This is the formal content of "monotonizing an ℕ-sequence
    needs only finite joins", and it is exactly what does not generalize: at uncountable
    cofinality, segments are infinite and finite `cub`-folds cannot reach them. -/
theorem prefixBounded_of_directed {D : Type} {le : D → D → Prop}
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (dir : Directed D le) : PrefixBounded natWellIndex le := by
  intro w
  induction w with
  | zero =>
      intro g
      refine ⟨g 0 (Nat.le_refl 0), fun v hv => ?_⟩
      have hv0 : v = 0 := Nat.le_zero.mp hv
      subst hv0
      exact le_refl _
  | succ n ih =>
      intro g
      obtain ⟨b, hb⟩ := ih (fun v hv => g v (Nat.le_succ_of_le hv))
      refine ⟨dir.cub b (g (n + 1) (Nat.le_refl _)), fun v hv => ?_⟩
      by_cases h : v = n + 1
      · subst h
        exact dir.le_cub_right _ _
      · have hvle : v ≤ n + 1 := hv
        have hv' : v ≤ n := by omega
        exact le_trans (hb v hv') (dir.le_cub_left _ _)

/-- The countable case, re-derived end-to-end through the transfinite machinery: `ω` is the
    instance `W = ℕ` with `PrefixBounded` supplied by plain directedness. Same statement as
    `countable_cofinal_factors`; the general theorem subsumes it. -/
noncomputable def countable_cofinal_factors' {X D : Type} (le : D → D → Prop)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (dir : Directed D le) (c : Nat → D) (hc : ∀ b, ∃ n, le b (c n))
    (dist : X → X → D) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) b) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist :=
  prefix_bounded_cofinal_factors natWellIndex le le_refl le_trans
    (prefixBounded_of_directed le_refl le_trans dir) c hc dist f bounded

/-! ## Hunting the escapee — the strip narrows from both walls

With the frontier reduced to "does `Directed` without `PrefixBounded` admit an escapee at
uncountable cofinality", the hunt begins with the natural candidates, and each death is
informative:

- **`ω₁ × ℕ`** (directed, *not* σ-directed, uncountable cofinality, no cofinal chain — the
  minimal inhabitant of the gap) **dies**: a bounded family has a coordinatewise least upper
  bound (countable sups in `ω₁`, max in `ℕ`), so `factors_of_image_sups` applies. Failing
  σ-directedness did not matter; the order was conditionally complete.
- **Ideal-of-sets orders** (finite or countable subsets, finitely-generated downsets) die the
  same way: bounded = inside one member, and unions supply lubs.
- **Chain-shaped designs** die twice over: requirements accumulated along a threshold chain
  lie inside one bounded slice (prefix-boundedness is automatic), and chain-shaped
  requirements self-dominate (`φ(tₐ) := a₍ₐ₊₁₎`).
- **Gap encodings pointed the wrong way** die structurally: a dominator's constraints are
  *lower* constraints only (`φ t` ranges over an up-set), so nothing can force `φ` under the
  shrinking side of a Hausdorff gap; top-side elements satisfy every constraint.

Two of the deaths generalize into theorems, formalized below.

**Wall one moves up (`sigma_directed_cofinal_factors`).** σ-directedness — every ℕ-family
bounded, the countable strengthening of `Directed` — supplies `PrefixBounded` along any
cofinal well-ordered family with *countable segments* (an "ω₁-like" index; the segment
enumeration replaces cardinals, as `PrefixBounded` replaced `κ`-directedness). So at
cofinality ω₁, σ-directedness already forces factorization: **an escapee carrying an ω₁-like
cofinal family must fail σ-directedness** — it must contain a countable family with no upper
bound, while every pair still has one.

**Wall two holds (`lists_not_sigma_directed` + `lists_bounded_factors`).** Failing
σ-directedness is *not sufficient*: `List Nat` under membership-inclusion is directed
(append), fails σ-directedness (the singletons `[n]` have no common bound — a list is
finite), yet **every bounded-image map over it factors**: a bounded image-family lives inside
one list, and filtering that list down to the family's actual members is a *least* upper
bound (taken classically), so `factors_of_image_sups` applies. This is the `ω₁ × ℕ` death,
made mathlib-free: the first wall of the strip is not where escapees live.

**The quarry's profile, after this hunt.** An escapee must: (1) fail σ-directedness (else
wall one, given an ω₁-like cofinal family); (2) fail conditional completeness on bounded
image-families *unovershootably* (else `factors_of_image_sups`; and total-order gaps
overshoot — the `ℚ≥0` lesson); (3) exhibit its failure only globally: every finite
subsystem is satisfiable (`directed_finite_factors`), and every principal down-set is
satisfied by a constant (that is the `bounded` hypothesis itself) — so no finite and no
localized witness exists, an Aronszajn-style "all levels nonempty, no branch" phenomenon.
Coherent-sequence and gap machinery are the known ZFC engines for exactly that shape —
and their selection problems are notoriously sensitive to axioms beyond ZFC, so the
escapee's existence may yet be *independent*, not merely open. That is the sharpened state
of the hunt: no capture, two walls proved, and a profile that points at genuine
set-theoretic combinatorics. -/

/-- σ-directedness: every *countable* family is bounded — the ℕ-strengthening of
    `Directed` (which bounds pairs), and exactly what `PrefixBounded` needs when
    segments are countable. -/
def SigmaDirected (D : Type) (le : D → D → Prop) : Prop :=
  ∀ c : Nat → D, ∃ b, ∀ n, le (c n) b

/-- An "ω₁-like" index: every segment `{v // v ≤ w}` is countable (admits an
    ℕ-enumeration). The cardinal-free form of "cofinality at most ω₁". -/
def CountableSegments {W : Type} (WI : WellIndex W) : Prop :=
  ∀ w, ∃ e : Nat → W, ∀ v, WI.le v w → ∃ n, e n = v

open Classical in
/-- σ-directedness supplies `PrefixBounded` over any index with countable segments:
    enumerate the segment, bound the induced ℕ-family. The `ω`-case pattern
    (`prefixBounded_of_directed`: finite segments, finite `cub`-folds) lifted one rung. -/
theorem prefixBounded_of_sigmaDirected {W D : Type} (WI : WellIndex W) {le : D → D → Prop}
    (hσ : SigmaDirected D le) (hcs : CountableSegments WI) : PrefixBounded WI le := by
  intro w g
  obtain ⟨e, he⟩ := hcs w
  obtain ⟨b, hb⟩ := hσ (fun n =>
    if h : WI.le (e n) w then g (e n) h else g w (WI.le_refl w))
  refine ⟨b, fun v hv => ?_⟩
  obtain ⟨n, hn⟩ := he v hv
  subst hn
  have h := hb n
  rw [dif_pos hv] at h
  exact h

/-- **Wall one: σ-directedness closes the ω₁-like case.** A σ-directed distance with a
    cofinal well-ordered family of countable segments factors every bounded-image map.
    Contrapositive, for the hunt: an escapee carrying such a family must contain a
    *countable* unbounded family — directedness intact, σ-directedness broken. -/
noncomputable def sigma_directed_cofinal_factors {X W D : Type} (WI : WellIndex W)
    (le : D → D → Prop)
    (le_refl : ∀ a, le a a) (le_trans : ∀ {a b c}, le a b → le b c → le a c)
    (hσ : SigmaDirected D le) (hcs : CountableSegments WI)
    (c : W → D) (hc : ∀ b, ∃ w, le b (c w))
    (dist : X → X → D) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, le (dist x y) t → le (dist (f x) (f y)) b) :
    Bridge X (Mono D le) D (universalGA le le_trans) dist :=
  prefix_bounded_cofinal_factors WI le le_refl le_trans
    (prefixBounded_of_sigmaDirected WI hσ hcs) c hc dist f bounded

/-! ### Wall two: a mathlib-free directed order that fails σ-directedness and factors anyway -/

/-- Membership-inclusion on finite lists: the mathlib-free stand-in for finite sets of
    naturals. A preorder (not antisymmetric — the interface never asked for that). -/
def leL (l₁ l₂ : List Nat) : Prop := ∀ x, x ∈ l₁ → x ∈ l₂

theorem leL_refl : ∀ l, leL l l := fun _ _ h => h

theorem leL_trans : ∀ {a b c}, leL a b → leL b c → leL a c :=
  fun hab hbc x hx => hbc x (hab x hx)

/-- Directed: append is a common upper bound. -/
def dirL : Directed (List Nat) leL where
  cub          := (· ++ ·)
  le_cub_left  := fun _ _ _x hx => List.mem_append.mpr (Or.inl hx)
  le_cub_right := fun _ _ _x hx => List.mem_append.mpr (Or.inr hx)

/-- Every member of a list is at most its running maximum. -/
theorem mem_le_foldMax : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr Nat.max 0
  | a :: l, x, hx => by
    cases hx with
    | head => exact Nat.le_max_left _ _
    | tail _ h => exact Nat.le_trans (mem_le_foldMax l x h) (Nat.le_max_right _ _)

/-- **`List Nat` is not σ-directed**: the singletons `[n]` have no common upper bound —
    such a bound would contain every natural, and lists are finite. Directedness holds
    (`dirL`), so this order lives strictly inside the strip the hunt is searching. -/
theorem lists_not_sigma_directed : ¬ SigmaDirected (List Nat) leL := by
  intro hσ
  obtain ⟨b, hb⟩ := hσ (fun n => [n])
  have hmem : ∀ n, n ∈ b := fun n => hb n n (List.mem_cons_self ..)
  have := mem_le_foldMax b (b.foldr Nat.max 0 + 1) (hmem _)
  omega

open Classical in
/-- **Wall two: failing σ-directedness is not sufficient for an escapee.** Every
    bounded-image map over `(List Nat, leL)` factors: a bounded image-family lies inside
    one list `b t`, and filtering `b t` to the family's actual members is a *least* upper
    bound of the family — so `factors_of_image_sups` applies. The same death as `ω₁ × ℕ`
    (coordinatewise sups) and every ideal-of-sets order (unions): natural set-shaped
    directed orders are conditionally complete on bounded families, and conditional
    completeness, not σ-directedness, is what an escapee has to break. -/
noncomputable def lists_bounded_factors {X : Type}
    (dist : X → X → List Nat) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, leL (dist x y) t → leL (dist (f x) (f y)) b) :
    Bridge X (Mono (List Nat) leL) (List Nat) (universalGA leL leL_trans) dist := by
  refine factors_of_image_sups leL leL_refl leL_trans dist f
    (fun t => (Classical.choose (bounded t)).filter
      (fun v => decide (∃ x y, leL (dist x y) t ∧ v ∈ dist (f x) (f y))))
    (fun t x y hxy v hv => ?_) (fun t u hu v hv => ?_)
  · -- the filter keeps every actual image member: it is an upper bound
    refine List.mem_filter.mpr ⟨Classical.choose_spec (bounded t) x y hxy v hv, ?_⟩
    exact decide_eq_true ⟨x, y, hxy, hv⟩
  · -- and keeps only image members: it is below any other bound — leastness
    obtain ⟨x, y, hxy, hvmem⟩ := of_decide_eq_true (List.mem_filter.mp hv).2
    exact hu x y hxy v hvmem

/-! ## The coherent-sequence encoding — the hunt reaches set theory

The profile said: fail σ-directedness, break conditional completeness unovershootably, fail
only globally. Coherent sequences are the ZFC engine with exactly that shape, and the
encoding goes through — up to a question this repo cannot decide. For a coherent sequence
`⟨e_α : α < ω₁⟩` (`e_α : α → ω`, `e_α =* e_β↾α` — nontrivial ones exist in ZFC, by
Todorcevic's walks), the **fiber order** `D_coh(e) := Σ_α {s : α → ω ∣ s =* e_α}`, ordered
*pointwise* on the smaller domain, is (on paper — ω₁ is not formalizable here):

- **directed with finite joins** — the pointwise max of two fiber elements stays in the
  fiber, because coherence keeps the deviation finite;
- **not σ-directed** — members spiking to `e_{α*}(ξ_n) + n` at points `ξ_n → α*` defeat
  every bound `(γ, w)`: coherence forces `w(ξ_n) = e_{α*}(ξ_n)` cofinitely;
- **conditionally incomplete in the join sense** — a bounded family whose pointwise sup
  dips below the floor `e_β` infinitely has upper bounds but **no minimal upper bound**:
  every bound can dip at one more coordinate. Not the overshootable total-order gap; the
  `D3`-flavoured missing-join kind, sustained infinitely under directedness.

**The first structure passing every wall.** Whether an escapee lives on it reduces to a
uniformization question: the canonical overshoot `φ(t) := (β_t, max(u_{S(t)}, e_{β_t}))` is
monotone *except at coherence defects* — finite per comparable pair, but fixing them
globally means choosing fiber representatives pointwise-monotonically in the level, and
**level-monotone bounded coherent sequences are trivial** (per-coordinate values stabilize;
coherence turns the stable function into a trivialization — provable, on paper). So over a
*nontrivial* sequence the canonical dominator is genuinely obstructed; whether *some*
non-canonical dominator always exists is exactly a coherent-sequence uniformization
principle — the class of statement that is axiom-sensitive (MA vs ◊), i.e. plausibly
**independent of ZFC**. The design space is pinned by a two-order tension: mod-finite
fibers make the requirement chain self-dominate by coherence; pointwise fibers make raw
`e`-requirements slice-unbounded (`sup_{β≤α} e_β(ξ)` can be infinite); every viable design
lives in the finite-modification freedom between the two.

**What is formalizable is the dip pathology itself** — profile item (2), witnessed below at
countable cofinality: `Fb`, levels `ℕ ∪ {∞}` over a constant-`1` floor with finite patches
(the trivial-coherent-sequence shadow of `D_coh`). It is directed (`dirF`), not σ-directed
(`fb_not_sigma_directed`), and carries a bounded family with **no minimal upper bound**
(`fb_no_minimal_ub`) — strictly worse than `Dm`'s two-incomparable-minimal-ubs — yet still
factors (`fb_factors`): an explicit ladder is a cofinal ℕ-sequence, and
`countable_cofinal_factors` overshoots every dip. So *each* profile item is individually
non-lethal at countable cofinality; the quarry must carry the dip pathology at uncountable
cofinality, where the ruler is gone — and that is `D_coh(e)`, waiting on set theory. -/

/-- Evaluate a finite patch list against the constant-`1` floor (first match wins). -/
def evalP : List (Nat × Nat) → Nat → Nat
  | [],             _ => 1
  | (k, v) :: rest, ξ => if ξ = k then v else evalP rest ξ

theorem evalP_not_key : ∀ (p : List (Nat × Nat)) (ξ : Nat),
    (∀ v, (ξ, v) ∉ p) → evalP p ξ = 1
  | [],             _, _ => rfl
  | (k, v) :: rest, ξ, h => by
    have hne : ξ ≠ k := fun he => h v (he ▸ List.mem_cons_self ..)
    show (if ξ = k then v else evalP rest ξ) = 1
    rw [if_neg hne]
    exact evalP_not_key rest ξ (fun u hu => h u (List.mem_cons_of_mem _ hu))

/-- Every key of a patch list is at most its running key-maximum. -/
def maxKeyP (p : List (Nat × Nat)) : Nat := p.foldr (fun kv acc => Nat.max kv.1 acc) 0

theorem key_le_maxKeyP : ∀ (p : List (Nat × Nat)) (ξ v : Nat), (ξ, v) ∈ p → ξ ≤ maxKeyP p
  | kv :: rest, ξ, v, h => by
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ h => exact Nat.le_trans (key_le_maxKeyP rest ξ v h) (Nat.le_max_right _ _)

/-- Every patch value is at most the running value-maximum-with-1. -/
def maxValP (p : List (Nat × Nat)) : Nat := p.foldr (fun kv acc => Nat.max kv.2 acc) 1

theorem evalP_le_maxValP : ∀ (p : List (Nat × Nat)) (ξ : Nat), evalP p ξ ≤ maxValP p
  | [],             _ => Nat.le_refl 1
  | (k, v) :: rest, ξ => by
    show (if ξ = k then v else evalP rest ξ) ≤ Nat.max v (maxValP rest)
    by_cases h : ξ = k
    · rw [if_pos h]; exact Nat.le_max_left _ _
    · rw [if_neg h]; exact Nat.le_trans (evalP_le_maxValP rest ξ) (Nat.le_max_right _ _)

/-- Levels: `ℕ ∪ {∞}` (`none` = the limit level with full domain). -/
def leLvl : Option Nat → Option Nat → Prop
  | _,      none   => True
  | none,   some _ => False
  | some n, some m => n ≤ m

theorem leLvl_refl : ∀ l, leLvl l l
  | none   => trivial
  | some _ => Nat.le_refl _

theorem leLvl_trans : ∀ {a b c}, leLvl a b → leLvl b c → leLvl a c :=
  fun {a b c} => match a, b, c with
  | _,      _,      none   => fun _ _ => trivial
  | none,   none,   some _ => fun _ h₂ => nomatch h₂
  | none,   some _, some _ => fun h₁ _ => nomatch h₁
  | some _, none,   some _ => fun _ h₂ => nomatch h₂
  | some _, some _, some _ => fun h₁ h₂ => Nat.le_trans h₁ h₂

/-- Domain of a level. -/
def inLvl (ξ : Nat) : Option Nat → Prop
  | none   => True
  | some n => ξ < n

theorem inLvl_mono : ∀ {l l'}, leLvl l l' → ∀ {ξ}, inLvl ξ l → inLvl ξ l' :=
  fun {l l'} h {_ξ} hξ => match l, l', h, hξ with
  | _,      none,   _, _  => trivial
  | none,   some _, h, _  => nomatch h
  | some _, some _, h, hξ => Nat.lt_of_lt_of_le hξ h

/-- The fiber order, mathlib-free: a level and a finite patch of the constant-`1` floor,
    ordered pointwise on the smaller domain — the trivial-coherent-sequence shadow of
    `D_coh(e)`. -/
def Fb := Option Nat × List (Nat × Nat)

def leF (a b : Fb) : Prop :=
  leLvl a.1 b.1 ∧ ∀ ξ, inLvl ξ a.1 → evalP a.2 ξ ≤ evalP b.2 ξ

theorem leF_refl : ∀ a, leF a a := fun a => ⟨leLvl_refl a.1, fun _ _ => Nat.le_refl _⟩

theorem leF_trans : ∀ {a b c}, leF a b → leF b c → leF a c :=
  fun hab hbc => ⟨leLvl_trans hab.1 hbc.1,
    fun ξ hξ => Nat.le_trans (hab.2 ξ hξ) (hbc.2 ξ (inLvl_mono hab.1 hξ))⟩

/-! ### Directed: level-max plus pointwise-max patch merge -/

def cubLvl : Option Nat → Option Nat → Option Nat
  | some n, some m => some (Nat.max n m)
  | _,      _      => none

theorem leLvl_cubLvl_left : ∀ l l', leLvl l (cubLvl l l')
  | none,   none   => trivial
  | none,   some _ => trivial
  | some _, none   => trivial
  | some _, some _ => Nat.le_max_left _ _

theorem leLvl_cubLvl_right : ∀ l l', leLvl l' (cubLvl l l')
  | none,   none   => trivial
  | none,   some _ => trivial
  | some _, none   => trivial
  | some _, some _ => Nat.le_max_right _ _

/-- Merge two patches: at every mentioned key, take the pointwise max of both sides. -/
def mergeP (p q : List (Nat × Nat)) : List (Nat × Nat) :=
  (p ++ q).map (fun kv => (kv.1, Nat.max (evalP p kv.1) (evalP q kv.1)))

theorem evalP_mergeP_of_mem : ∀ (l p q : List (Nat × Nat)) (ξ v : Nat), (ξ, v) ∈ l →
    evalP (l.map (fun kv => (kv.1, Nat.max (evalP p kv.1) (evalP q kv.1)))) ξ
      = Nat.max (evalP p ξ) (evalP q ξ)
  | (k, w) :: rest, p, q, ξ, v, h => by
    show (if ξ = k then Nat.max (evalP p k) (evalP q k) else _) = _
    by_cases hk : ξ = k
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
      cases h with
      | head => exact absurd rfl hk
      | tail _ h => exact evalP_mergeP_of_mem rest p q ξ v h

open Classical in
theorem le_evalP_mergeP_left (p q : List (Nat × Nat)) (ξ : Nat) :
    evalP p ξ ≤ evalP (mergeP p q) ξ := by
  by_cases h : ∃ v, (ξ, v) ∈ p ++ q
  · obtain ⟨v, hv⟩ := h
    rw [mergeP, evalP_mergeP_of_mem (p ++ q) p q ξ v hv]
    exact Nat.le_max_left _ _
  · have hp : ∀ v, (ξ, v) ∉ p := fun v hv => h ⟨v, List.mem_append.mpr (Or.inl hv)⟩
    have hm : ∀ v, (ξ, v) ∉ mergeP p q := by
      intro v hv
      obtain ⟨⟨k, w⟩, hk, he⟩ := List.mem_map.mp hv
      cases he
      exact h ⟨w, hk⟩
    rw [evalP_not_key p ξ hp, evalP_not_key _ ξ hm]
    exact Nat.le_refl 1

open Classical in
theorem le_evalP_mergeP_right (p q : List (Nat × Nat)) (ξ : Nat) :
    evalP q ξ ≤ evalP (mergeP p q) ξ := by
  by_cases h : ∃ v, (ξ, v) ∈ p ++ q
  · obtain ⟨v, hv⟩ := h
    rw [mergeP, evalP_mergeP_of_mem (p ++ q) p q ξ v hv]
    exact Nat.le_max_right _ _
  · have hq : ∀ v, (ξ, v) ∉ q := fun v hv => h ⟨v, List.mem_append.mpr (Or.inr hv)⟩
    have hm : ∀ v, (ξ, v) ∉ mergeP p q := by
      intro v hv
      obtain ⟨⟨k, w⟩, hk, he⟩ := List.mem_map.mp hv
      cases he
      exact h ⟨w, hk⟩
    rw [evalP_not_key q ξ hq, evalP_not_key _ ξ hm]
    exact Nat.le_refl 1

def dirF : Directed Fb leF where
  cub          := fun a b => (cubLvl a.1 b.1, mergeP a.2 b.2)
  le_cub_left  := fun a b =>
    ⟨leLvl_cubLvl_left a.1 b.1, fun ξ _ => le_evalP_mergeP_left a.2 b.2 ξ⟩
  le_cub_right := fun a b =>
    ⟨leLvl_cubLvl_right a.1 b.1, fun ξ _ => le_evalP_mergeP_right a.2 b.2 ξ⟩

/-! ### Not σ-directed: unbounded spikes at coordinate 0 -/

theorem fb_not_sigma_directed : ¬ SigmaDirected Fb leF := by
  intro hσ
  obtain ⟨⟨l, v⟩, hb⟩ := hσ (fun n => (none, [(0, n)]))
  have he : evalP [(0, evalP v 0 + 1)] 0 = evalP v 0 + 1 := by
    show (if 0 = 0 then evalP v 0 + 1 else evalP [] 0) = evalP v 0 + 1
    rw [if_pos rfl]
  have h : evalP [(0, evalP v 0 + 1)] 0 ≤ evalP v 0 :=
    (hb (evalP v 0 + 1)).2 0 trivial
  rw [he] at h
  omega

/-! ### The dip pathology: a bounded family with NO minimal upper bound -/

/-- The patch zeroing the even coordinates below `n`. -/
def zeroEvens : Nat → List (Nat × Nat)
  | 0     => []
  | n + 1 => if n % 2 = 0 then (n, 0) :: zeroEvens n else zeroEvens n

theorem evalP_zeroEvens_le_one : ∀ (n ξ : Nat), evalP (zeroEvens n) ξ ≤ 1
  | 0,     _ => Nat.le_refl 1
  | n + 1, ξ => by
    show evalP (if n % 2 = 0 then (n, 0) :: zeroEvens n else zeroEvens n) ξ ≤ 1
    by_cases h : n % 2 = 0
    · rw [if_pos h]
      show (if ξ = n then 0 else evalP (zeroEvens n) ξ) ≤ 1
      by_cases hξ : ξ = n
      · rw [if_pos hξ]; exact Nat.zero_le 1
      · rw [if_neg hξ]; exact evalP_zeroEvens_le_one n ξ
    · rw [if_neg h]; exact evalP_zeroEvens_le_one n ξ

theorem evalP_zeroEvens_even : ∀ (n ξ : Nat), ξ < n → ξ % 2 = 0 → evalP (zeroEvens n) ξ = 0
  | 0,     _, hlt, _   => by omega
  | n + 1, ξ, hlt, hev => by
    show evalP (if n % 2 = 0 then (n, 0) :: zeroEvens n else zeroEvens n) ξ = 0
    by_cases hξ : ξ = n
    · subst hξ
      rw [if_pos hev]
      show (if ξ = ξ then 0 else evalP (zeroEvens ξ) ξ) = 0
      rw [if_pos rfl]
    · by_cases h : n % 2 = 0
      · rw [if_pos h]
        show (if ξ = n then 0 else evalP (zeroEvens n) ξ) = 0
        rw [if_neg hξ]
        exact evalP_zeroEvens_even n ξ (by omega) hev
      · rw [if_neg h]
        exact evalP_zeroEvens_even n ξ (by omega) hev

/-- The dip family: level `n`, floor `1` zeroed on the evens below `n`. Its pointwise sup
    drops to `0` at every even coordinate — infinitely far below the limit-level floor. -/
def sEv (n : Nat) : Fb := (some n, zeroEvens n)

/-- **The dip pathology, witnessed.** The family `sEv` is bounded, and every upper bound
    strictly exceeds another upper bound — dip at one more even coordinate beyond its
    patches. No minimal upper bound exists, a fortiori no least: strictly worse than the
    `Dm` gap (two incomparable minimal ubs), and the exact conditional-incompleteness the
    quarry's profile item (2) demands. -/
theorem fb_no_minimal_ub :
    (∃ b, ∀ n, leF (sEv n) b) ∧
    (∀ u, (∀ n, leF (sEv n) u) →
      ∃ u', (∀ n, leF (sEv n) u') ∧ leF u' u ∧ ¬ leF u u') := by
  constructor
  · exact ⟨(none, []), fun n => ⟨trivial, fun ξ _ => evalP_zeroEvens_le_one n ξ⟩⟩
  · intro u hu
    obtain ⟨l, v⟩ := u
    -- a fresh even coordinate beyond every patch key
    obtain ⟨ξ₀, hev, hgt⟩ : ∃ w, w % 2 = 0 ∧ maxKeyP v < w :=
      ⟨2 * (maxKeyP v + 1), by omega, by omega⟩
    have hfresh : ∀ w, (ξ₀, w) ∉ v := fun w hw =>
      absurd (key_le_maxKeyP v ξ₀ w hw) (by omega)
    have hv₀ : evalP v ξ₀ = 1 := evalP_not_key v ξ₀ hfresh
    refine ⟨(l, (ξ₀, 0) :: v), ⟨?_, ?_, ?_⟩⟩
    · -- still an upper bound: the family itself is 0 at ξ₀
      intro n
      refine ⟨(hu n).1, fun ξ hξ => ?_⟩
      show evalP (zeroEvens n) ξ ≤ (if ξ = ξ₀ then 0 else evalP v ξ)
      by_cases hξeq : ξ = ξ₀
      · rw [if_pos hξeq]
        have h0 : evalP (zeroEvens n) ξ = 0 :=
          evalP_zeroEvens_even n ξ hξ (by rw [hξeq]; exact hev)
        omega
      · rw [if_neg hξeq]
        exact (hu n).2 ξ hξ
    · -- below the given bound
      refine ⟨leLvl_refl l, fun ξ _ => ?_⟩
      show (if ξ = ξ₀ then 0 else evalP v ξ) ≤ evalP v ξ
      by_cases hξeq : ξ = ξ₀
      · rw [if_pos hξeq]; exact Nat.zero_le _
      · rw [if_neg hξeq]; exact Nat.le_refl _
    · -- strictly: the given bound is 1 at ξ₀, the new one is 0
      intro hle
      have hl : l = none := by
        cases l with
        | none => rfl
        | some m => exact absurd ((hu (m + 1)).1) (Nat.not_succ_le_self m)
      have h := hle.2 ξ₀ (by rw [hl]; exact trivial)
      have h0 : evalP ((ξ₀, 0) :: v) ξ₀ = 0 := by
        show (if ξ₀ = ξ₀ then 0 else evalP v ξ₀) = 0
        rw [if_pos rfl]
      rw [hv₀, h0] at h
      omega

/-! ### And it still factors: the ladder is a cofinal ℕ-sequence -/

/-- The ladder patch: value `k` on `[0, j)`. -/
def ladder (k : Nat) : Nat → List (Nat × Nat)
  | 0     => []
  | j + 1 => (j, k) :: ladder k j

theorem evalP_ladder_lt : ∀ (k j ξ : Nat), ξ < j → evalP (ladder k j) ξ = k
  | _, 0,     _, h => by omega
  | k, j + 1, ξ, h => by
    show (if ξ = j then k else evalP (ladder k j) ξ) = k
    by_cases hξ : ξ = j
    · rw [if_pos hξ]
    · rw [if_neg hξ]
      exact evalP_ladder_lt k j ξ (by omega)

theorem evalP_ladder_ge : ∀ (k j ξ : Nat), j ≤ ξ → evalP (ladder k j) ξ = 1
  | _, 0,     _, _ => rfl
  | k, j + 1, ξ, h => by
    show (if ξ = j then k else evalP (ladder k j) ξ) = 1
    rw [if_neg (by omega)]
    exact evalP_ladder_ge k j ξ (by omega)

/-- The ladders are cofinal: every element is dominated once the rung exceeds its patch
    keys and values. A bare cofinal ℕ-sequence — the countable escape hatch. -/
theorem fb_ladder_cofinal : ∀ a : Fb, ∃ n, leF a (none, ladder n n) := by
  intro a
  obtain ⟨l, p⟩ := a
  refine ⟨Nat.max (maxValP p) (maxKeyP p + 1), ⟨trivial, fun ξ _ => ?_⟩⟩
  by_cases hξ : ξ < Nat.max (maxValP p) (maxKeyP p + 1)
  · rw [evalP_ladder_lt _ _ ξ hξ]
    exact Nat.le_trans (evalP_le_maxValP p ξ) (Nat.le_max_left _ _)
  · rw [evalP_ladder_ge _ _ ξ (by omega)]
    have hkey : ∀ v, (ξ, v) ∉ p := by
      intro v hv
      have h1 := key_le_maxKeyP p ξ v hv
      have h2 : maxKeyP p + 1 ≤ Nat.max (maxValP p) (maxKeyP p + 1) := Nat.le_max_right _ _
      omega
    rw [evalP_not_key p ξ hkey]
    exact Nat.le_refl 1

/-- **Profile item (2) is individually non-lethal.** `Fb` carries the dip pathology (no
    minimal upper bound) and fails σ-directedness, yet every bounded-image map factors —
    the ladder ruler overshoots every dip. The quarry must therefore carry the dips at
    *uncountable* cofinality, where no ruler exists: exactly `D_coh(e)` over a nontrivial
    coherent sequence, and that question leaves this repo for set theory. -/
noncomputable def fb_factors {X : Type} (dist : X → X → Fb) (f : X → X)
    (bounded : ∀ t, ∃ b, ∀ x y, leF (dist x y) t → leF (dist (f x) (f y)) b) :
    Bridge X (Mono Fb leF) Fb (universalGA leF leF_trans) dist :=
  countable_cofinal_factors leF leF_refl leF_trans dirF
    (fun n => (none, ladder n n)) fb_ladder_cofinal dist f bounded

/-! ## The reps theorem, machine-checked in shadow

The set-theoretic hunt (`NOTES-coherent-escapee.md`) runs on one four-step engine: a
level-monotone system of representatives for a coherent sequence forces triviality. Its
proof uses exactly three properties of the index ω₁, all already abstracted in this file:
least witnesses (`WellIndex`), σ-directedness of the index (`SigmaDirected` — where
regularity enters), and countable segments (`CountableSegments`). So the engine itself is
formalizable *in shadow*: over an abstract index carrying those three hypotheses, with
"finite" rendered mathlib-free as "covered by a list".

Honesty about instances, per house style: the intended model (ω₁) is not constructible
here, and `ℕ` — the only concrete `WellIndex` in this file — *fails* `SigmaDirected`
(`nat_not_sigma_directed`). The shadow is therefore paired with its boundary witness:
at index `ℕ` the concentration step provably fails (`omega_concentration_fails`) — the
level-monotone, pairwise-finitely-differing family `χ_{<n}` moves at *every* coordinate.
σ-directedness of the index is load-bearing, not decorative: the theorem below is the
exact reason the set-theoretic argument works at ω₁ and not below it. -/

/-- Mathlib-free finiteness of a predicate: some list covers it. -/
def FiniteP {A : Type} (P : A → Prop) : Prop := ∃ L : List A, ∀ a, P a → a ∈ L

theorem FiniteP.union {A : Type} {P Q : A → Prop} (hP : FiniteP P) (hQ : FiniteP Q) :
    FiniteP (fun a => P a ∨ Q a) := by
  obtain ⟨L, hL⟩ := hP
  obtain ⟨M, hM⟩ := hQ
  refine ⟨L ++ M, fun a h => List.mem_append.mpr ?_⟩
  cases h with
  | inl h => exact Or.inl (hL a h)
  | inr h => exact Or.inr (hM a h)

theorem FiniteP.mono {A : Type} {P Q : A → Prop} (h : ∀ a, P a → Q a) (hQ : FiniteP Q) :
    FiniteP P := by
  obtain ⟨L, hL⟩ := hQ
  exact ⟨L, fun a ha => hL a (h a ha)⟩

/-- From non-finiteness, a fresh witness outside any list (classical). -/
theorem exists_fresh {A : Type} {P : A → Prop} (h : ¬ FiniteP P) (L : List A) :
    ∃ a, P a ∧ ¬ a ∈ L :=
  Classical.byContradiction (fun hno =>
    h ⟨L, fun a ha => Classical.byContradiction (fun hmem => hno ⟨a, ha, hmem⟩)⟩)

/-- Mathlib-free pigeonhole: an injective ℕ-sequence cannot land inside one list. -/
theorem no_injection_into_list {A : Type} :
    ∀ (L : List A) (f : Nat → A), (∀ m n, f m = f n → m = n) → ¬ ∀ n, f n ∈ L
  | [], f, _, hall => absurd (hall 0) (fun h => nomatch h)
  | a :: L, f, hinj, hall => by
    by_cases h : ∃ k, f k = a
    · obtain ⟨k, hk⟩ := h
      refine no_injection_into_list L (fun n => f (if n < k then n else n + 1)) ?_ ?_
      · intro m n hmn
        have h1 := hinj _ _ hmn
        by_cases hm : m < k <;> by_cases hn : n < k
        · rw [if_pos hm, if_pos hn] at h1; exact h1
        · rw [if_pos hm, if_neg hn] at h1; omega
        · rw [if_neg hm, if_pos hn] at h1; omega
        · rw [if_neg hm, if_neg hn] at h1; omega
      · intro n
        have hne : f (if n < k then n else n + 1) ≠ a := by
          intro he
          have := hinj _ k (he.trans hk.symm)
          by_cases hn : n < k
          · rw [if_pos hn] at this; omega
          · rw [if_neg hn] at this; omega
        cases hall (if n < k then n else n + 1) with
        | head => exact absurd rfl hne
        | tail _ hmem => exact hmem
    · refine no_injection_into_list L f hinj (fun n => ?_)
      cases hall n with
      | head => exact absurd ⟨n, rfl⟩ h
      | tail _ hmem => exact hmem

/-- Least witnesses give totality: apply `least` to the pair predicate. -/
theorem WellIndex.total {W : Type} (WI : WellIndex W) (a b : W) :
    WI.le a b ∨ WI.le b a := by
  obtain ⟨μ, hμ, hleast⟩ := WI.least (fun w => w = a ∨ w = b) ⟨a, Or.inl rfl⟩
  cases hμ with
  | inl h => subst h; exact Or.inl (hleast b (Or.inr rfl))
  | inr h => subst h; exact Or.inr (hleast a (Or.inl rfl))

theorem WellIndex.lt_of_lt_of_le {W : Type} (WI : WellIndex W) {u v w : W}
    (h : WI.lt u v) (hle : WI.le v w) : WI.lt u w :=
  ⟨WI.le_trans h.1 hle, fun hwu => h.2 (WI.le_trans hle hwu)⟩

theorem WellIndex.lt_of_le_of_lt {W : Type} (WI : WellIndex W) {u v w : W}
    (hle : WI.le u v) (h : WI.lt v w) : WI.lt u w :=
  ⟨WI.le_trans hle h.1, fun hwu => h.2 (WI.le_trans hwu hle)⟩

/-- A coherent sequence over an abstract index: a `ℕ`-valued row per level, any two
    rows differing at only finitely many common-domain positions. (Rows are total
    functions; only values at `u < w` are meaningful.) -/
structure CoherentSeq (W : Type) (WI : WellIndex W) where
  e   : W → W → Nat
  coh : ∀ v w, FiniteP (fun u => WI.lt u v ∧ WI.lt u w ∧ e v u ≠ e w u)

/-- Triviality: one global row matches every level's row off a finite set. -/
def CoherentSeq.Trivial {W : Type} {WI : WellIndex W} (C : CoherentSeq W WI) : Prop :=
  ∃ E : W → Nat, ∀ w, FiniteP (fun u => WI.lt u w ∧ E u ≠ C.e w u)

/-- A representative system: per-level rows in the fiber (finite deviation from `e`),
    pointwise monotone in the level. -/
structure Reps {W : Type} {WI : WellIndex W} (C : CoherentSeq W WI) where
  ρ     : W → W → Nat
  fiber : ∀ w, FiniteP (fun u => WI.lt u w ∧ ρ w u ≠ C.e w u)
  mono  : ∀ {v w}, WI.le v w → ∀ u, WI.lt u v → ρ v u ≤ ρ w u

section RepsTheorem
open Classical

variable {W : Type} (WI : WellIndex W)

/-- σ-directedness bounds pairs. -/
theorem pair_bound (hσ : SigmaDirected W WI.le) (a b : W) :
    ∃ c, WI.le a c ∧ WI.le b c := by
  obtain ⟨c, hc⟩ := hσ (fun n => if n = 0 then a else b)
  refine ⟨c, ?_, ?_⟩
  · have := hc 0; rw [if_pos rfl] at this; exact this
  · have := hc 1; rw [if_neg (by omega)] at this; exact this

/-- Strictly-above elements exist (unboundedness + totality). -/
theorem exists_gt (hub : ∀ w, ∃ w', ¬ WI.le w' w) (w : W) : ∃ s, WI.lt w s := by
  obtain ⟨s, hs⟩ := hub w
  cases WI.total w s with
  | inl h => exact ⟨s, h, hs⟩
  | inr h => exact absurd h hs

/-- **The reps theorem, in shadow.** Over any index with least witnesses, σ-directedness,
    countable segments, and no top, a coherent sequence admitting a level-monotone
    representative system is trivial. This is the four-step ω₁ engine of the
    set-theoretic notes, machine-checked: (1) coherence transfers to the reps and pins
    pairwise movers finite; (2) σ-directedness concentrates countably many movement
    witnesses at one bound — the step that fails at index ℕ; (3) hence the escape set is
    bounded; (4) bounded escape stabilizes into a trivializing row. -/
theorem reps_implies_trivial
    (hσ : SigmaDirected W WI.le) (hcs : CountableSegments WI)
    (hub : ∀ w, ∃ w', ¬ WI.le w' w) (w₀ : W)
    (C : CoherentSeq W WI) (R : Reps C) : C.Trivial := by
  -- (1) pairwise movers are finite: chain through the two fibers and coherence
  have hmov : ∀ v w, FiniteP (fun u => WI.lt u v ∧ WI.lt u w ∧ R.ρ w u > R.ρ v u) := by
    intro v w
    refine FiniteP.mono (fun u hu => ?_)
      (((R.fiber v).union (C.coh v w)).union (R.fiber w))
    obtain ⟨huv, huw, hgt⟩ := hu
    by_cases h1 : R.ρ v u = C.e v u
    · by_cases h2 : C.e v u = C.e w u
      · by_cases h3 : C.e w u = R.ρ w u
        · omega
        · exact Or.inr ⟨huw, fun he => h3 he.symm⟩
      · exact Or.inl (Or.inr ⟨huv, huw, h2⟩)
    · exact Or.inl (Or.inl ⟨huv, h1⟩)
  -- (2) concentration: the set of coordinates below `v` that ever move is finite
  have hU : ∀ v, FiniteP (fun u => WI.lt u v ∧ ∃ w, WI.le v w ∧ R.ρ w u > R.ρ v u) := by
    intro v
    refine Classical.byContradiction (fun hinf => ?_)
    -- an injective sequence of movers, each with a witness level
    have hfresh : ∀ L : List W, ∃ u,
        (WI.lt u v ∧ ∃ w, WI.le v w ∧ R.ρ w u > R.ρ v u) ∧ ¬ u ∈ L :=
      fun L => exists_fresh hinf L
    let picks : Nat → List W := fun n =>
      Nat.rec [] (fun _ ih => Classical.choose (hfresh ih) :: ih) n
    let u : Nat → W := fun n => Classical.choose (hfresh (picks n))
    have hspec : ∀ n, (WI.lt (u n) v ∧ ∃ w, WI.le v w ∧ R.ρ w (u n) > R.ρ v (u n))
        ∧ ¬ u n ∈ picks n := fun n => Classical.choose_spec (hfresh (picks n))
    have hpicks_succ : ∀ n, picks (n + 1) = u n :: picks n := fun _ => rfl
    have hmem_picks : ∀ m n, m < n → u m ∈ picks n := by
      intro m n h
      induction n with
      | zero => omega
      | succ k ih =>
        rw [hpicks_succ k]
        by_cases hmk : m = k
        · subst hmk; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih (by omega))
    have hinj : ∀ m n, u m = u n → m = n := by
      intro m n he
      by_cases h : m = n
      · exact h
      · exfalso
        cases Nat.lt_or_ge m n with
        | inl hlt =>
          have hx := hmem_picks m n hlt
          rw [he] at hx
          exact (hspec n).2 hx
        | inr hge =>
          have hlt : n < m := by omega
          have hx := hmem_picks n m hlt
          rw [← he] at hx
          exact (hspec m).2 hx
    -- witness levels, concentrated at a σ-bound
    let wit : Nat → W := fun n => Classical.choose (hspec n).1.2
    have hwit : ∀ n, WI.le v (wit n) ∧ R.ρ (wit n) (u n) > R.ρ v (u n) :=
      fun n => Classical.choose_spec (hspec n).1.2
    obtain ⟨b, hb⟩ := hσ wit
    have hvb : WI.le v b := WI.le_trans (hwit 0).1 (hb 0)
    -- every `u n` is a mover of the single pair (v, b)
    obtain ⟨L, hL⟩ := hmov v b
    refine no_injection_into_list L u hinj (fun n => hL (u n) ?_)
    have hub' : WI.lt (u n) b := WellIndex.lt_of_lt_of_le WI (hspec n).1.1 hvb
    have hmono : R.ρ (wit n) (u n) ≤ R.ρ b (u n) :=
      R.mono (hb n) (u n) (WellIndex.lt_of_lt_of_le WI (hspec n).1.1 (hwit n).1)
    exact ⟨(hspec n).1.1, hub', by have := (hwit n).2; omega⟩
  -- (3) the escape set is bounded: otherwise a strictly increasing chain of escapees
  -- gets σ-bounded, and each member moves above the bound — an infinite mover set
  have hT : ∃ wstar, ∀ u, (¬ ∃ B, ∀ w, WI.lt u w → R.ρ w u ≤ B) → WI.le u wstar := by
    refine Classical.byContradiction (fun hno => ?_)
    have hstep : ∀ w : W, ∃ u, (¬ ∃ B, ∀ w', WI.lt u w' → R.ρ w' u ≤ B) ∧ ¬ WI.le u w :=
      fun w => Classical.byContradiction (fun hn =>
        hno ⟨w, fun u hu => Classical.byContradiction (fun hle => hn ⟨u, hu, hle⟩)⟩)
    let t : Nat → W := fun n =>
      Nat.rec (motive := fun _ => W) (Classical.choose (hstep w₀))
        (fun _ prev => Classical.choose (hstep prev)) n
    have hts : ∀ n, (¬ ∃ B, ∀ w', WI.lt (t (n+1)) w' → R.ρ w' (t (n+1)) ≤ B)
        ∧ ¬ WI.le (t (n+1)) (t n) := fun n => Classical.choose_spec (hstep (t n))
    have hesc : ∀ n, ¬ ∃ B, ∀ w', WI.lt (t n) w' → R.ρ w' (t n) ≤ B := by
      intro n
      cases n with
      | zero => exact (Classical.choose_spec (hstep w₀)).1
      | succ k => exact (hts k).1
    have hstep_le : ∀ n, WI.le (t n) (t (n+1)) := by
      intro n
      cases WI.total (t n) (t (n+1)) with
      | inl h => exact h
      | inr h => exact absurd h (hts n).2
    have hchain : ∀ m n, m ≤ n → WI.le (t m) (t n) := by
      intro m n h
      induction n with
      | zero =>
        have hm0 : m = 0 := by omega
        subst hm0
        exact WI.le_refl _
      | succ k ih =>
        by_cases hmk : m = k + 1
        · subst hmk; exact WI.le_refl _
        · exact WI.le_trans (ih (by omega)) (hstep_le k)
    have htinj : ∀ m n, t m = t n → m = n := by
      intro m n he
      by_cases h : m = n
      · exact h
      · exfalso
        cases Nat.lt_or_ge m n with
        | inl hlt =>
          have h1 := hchain (m+1) n (by omega)
          rw [← he] at h1
          exact (hts m).2 h1
        | inr hge =>
          have hlt : n < m := by omega
          have h1 := hchain (n+1) m (by omega)
          rw [he] at h1
          exact (hts n).2 h1
    obtain ⟨b, hb⟩ := hσ t
    obtain ⟨s, hbs⟩ := exists_gt WI hub b
    obtain ⟨L, hL⟩ := hU s
    refine no_injection_into_list L t htinj (fun n => hL (t n) ?_)
    have hlts : WI.lt (t n) s := WellIndex.lt_of_le_of_lt WI (hb n) hbs
    have hmove : ∃ w', WI.lt (t n) w' ∧ R.ρ s (t n) < R.ρ w' (t n) :=
      Classical.byContradiction (fun hn =>
        hesc n ⟨R.ρ s (t n), fun w' hw' => Classical.byContradiction
          (fun hgt => hn ⟨w', hw', by omega⟩)⟩)
    obtain ⟨w', hw'lt, hw'gt⟩ := hmove
    obtain ⟨w'', hw'w'', hsw''⟩ := pair_bound WI hσ w' s
    refine ⟨hlts, w'', hsw'', ?_⟩
    have := R.mono hw'w'' (t n) hw'lt
    omega
  -- (4) bounded escape stabilizes into a trivializing row
  obtain ⟨wstar, hwstar⟩ := hT
  obtain ⟨sstar, hsstar⟩ := exists_gt WI hub wstar
  have hstable : ∀ u, ¬ WI.le u wstar →
      ∃ M, (∃ w, WI.lt u w ∧ R.ρ w u = M) ∧ (∀ w, WI.lt u w → R.ρ w u ≤ M) := by
    intro u hu
    have hbdd : ∃ B, ∀ w, WI.lt u w → R.ρ w u ≤ B :=
      Classical.byContradiction (fun hn => hu (hwstar u hn))
    obtain ⟨M, hM, hMleast⟩ := @exists_least (fun B => ∀ w, WI.lt u w → R.ρ w u ≤ B)
      (fun _ => Classical.propDecidable _) hbdd
    refine ⟨M, ?_, hM⟩
    refine Classical.byContradiction (fun hnot => ?_)
    have hlt' : ∀ w, WI.lt u w → R.ρ w u ≠ M := fun w hw he => hnot ⟨w, hw, he⟩
    obtain ⟨s, hs⟩ := exists_gt WI hub u
    cases Nat.eq_zero_or_pos M with
    | inl h0 =>
      have h1 := hM s hs
      have h2 := hlt' s hs
      omega
    | inr hpos =>
      have hM' : ∀ w, WI.lt u w → R.ρ w u ≤ M - 1 := by
        intro w hw
        have h1 := hM w hw
        have h2 := hlt' w hw
        omega
      have := hMleast (M - 1) hM'
      omega
  -- the trivializing row: the floor at `sstar` below the escape bound, stable values above
  let E : W → Nat := fun u =>
    if h : WI.le u wstar then C.e sstar u else Classical.choose (hstable u h)
  refine ⟨E, fun v => ?_⟩
  -- σ-bound the stabilization stages over the (countable) segment of `v`
  obtain ⟨f, hf⟩ := hcs v
  let g : Nat → W := fun n =>
    if h : ¬ WI.le (f n) wstar then
      Classical.choose (Classical.choose_spec (hstable (f n) h)).1
    else v
  obtain ⟨γ₀, hγ₀⟩ := hσ g
  obtain ⟨γ, hvγ, hγ₀γ⟩ := pair_bound WI hσ v γ₀
  refine FiniteP.mono (fun u hu => ?_)
    (((C.coh sstar v).union (R.fiber γ)).union (C.coh γ v))
  obtain ⟨huv, hne⟩ := hu
  by_cases h : WI.le u wstar
  · -- below the escape bound: `E` is the `sstar` floor; coherence covers the difference
    have hus : WI.lt u sstar := WellIndex.lt_of_le_of_lt WI h hsstar
    have hEu : E u = C.e sstar u := dif_pos h
    exact Or.inl (Or.inl ⟨hus, huv, fun he => hne (hEu ▸ he)⟩)
  · -- above: `E` is the stable value, attained at `γ`; fiber + coherence cover it
    obtain ⟨n, hfn⟩ := hf u huv.1
    subst hfn
    have hEu : E (f n) = Classical.choose (hstable (f n) h) := dif_neg h
    have hgn : g n = Classical.choose (Classical.choose_spec (hstable (f n) h)).1 :=
      dif_pos h
    have hwu := Classical.choose_spec (Classical.choose_spec (hstable (f n) h)).1
    rw [← hgn] at hwu
    have hγlt : WI.lt (f n) γ := WellIndex.lt_of_lt_of_le WI huv hvγ
    have hge : R.ρ (g n) (f n) ≤ R.ρ γ (f n) :=
      R.mono (WI.le_trans (hγ₀ n) hγ₀γ) (f n) hwu.1
    have hbd := (Classical.choose_spec (hstable (f n) h)).2 γ hγlt
    have hργ : R.ρ γ (f n) = Classical.choose (hstable (f n) h) := by
      have h2 := hwu.2
      omega
    by_cases h2 : R.ρ γ (f n) = C.e γ (f n)
    · refine Or.inr ⟨hγlt, huv, fun he => hne ?_⟩
      rw [hEu, ← hργ, h2, he]
    · exact Or.inl (Or.inr ⟨hγlt, h2⟩)

end RepsTheorem

/-! ### The boundary witness: the concentration step fails at index ℕ -/

/-- ℕ is not σ-directed as an index: the identity family is unbounded. -/
theorem nat_not_sigma_directed : ¬ SigmaDirected Nat Nat.le := by
  intro hσ
  obtain ⟨b, hb⟩ := hσ (fun n => n)
  have h : b + 1 ≤ b := hb (b + 1)
  omega

/-- The ω-indexed family `χ_{<n}`: level `n` is the indicator of `[0, n)`. -/
def chiLt (n ξ : Nat) : Nat := if ξ < n then 1 else 0

/-- The family is level-monotone. -/
theorem chiLt_mono {n m : Nat} (h : n ≤ m) (ξ : Nat) : chiLt n ξ ≤ chiLt m ξ := by
  show (if ξ < n then 1 else 0) ≤ (if ξ < m then 1 else 0)
  by_cases hξ : ξ < n
  · rw [if_pos hξ, if_pos (by omega)]
    exact Nat.le_refl 1
  · rw [if_neg hξ]
    exact Nat.zero_le _

/-- The family is pairwise finitely-differing ("coherent" at index ℕ). -/
theorem chiLt_coherent (n m : Nat) : FiniteP (fun ξ => chiLt n ξ ≠ chiLt m ξ) := by
  refine ⟨List.range n ++ List.range m, fun ξ hξ => List.mem_append.mpr ?_⟩
  by_cases h1 : ξ < n
  · exact Or.inl (List.mem_range.mpr h1)
  · by_cases h2 : ξ < m
    · exact Or.inr (List.mem_range.mpr h2)
    · refine absurd ?_ hξ
      show (if ξ < n then 1 else 0) = (if ξ < m then 1 else 0)
      rw [if_neg h1, if_neg h2]

/-- **The concentration step fails at index ℕ.** Every coordinate of the coherent,
    level-monotone family `χ_{<n}` moves: the mover set of level `0` is all of ℕ — not
    finite. At ω₁ this set is finite (`reps_implies_trivial`, step 2) *because* the index
    is σ-directed; ℕ is not (`nat_not_sigma_directed`), and this is the exact boundary.
    The shadow theorem's hypotheses are load-bearing. -/
theorem omega_concentration_fails :
    ¬ FiniteP (fun ξ : Nat => ∃ m, chiLt m ξ > chiLt 0 ξ) := by
  intro hfin
  obtain ⟨L, hL⟩ := hfin
  have hall : ∀ ξ : Nat, ξ ∈ L := by
    intro ξ
    refine hL ξ ⟨ξ + 1, ?_⟩
    show (if ξ < ξ + 1 then 1 else 0) > (if ξ < 0 then 1 else 0)
    rw [if_pos (by omega), if_neg (by omega)]
    omega
  have := mem_le_foldMax L (L.foldr Nat.max 0 + 1) (hall _)
  omega

/-! ## The dip-schedulability game, in shadow: Theorem A and Lemma F machine-checked

`NOTES-coherent-escapee.md` / `PROBLEM-dip-schedulability.md` reduce the transport line's
qualitative residual to a game on a coherent sequence. Two proved pillars of that
development are index-agnostic (no ω₁ regularity, no fiber-order construction beyond the
pointwise data they use) and formalize directly over the same `CoherentSeq` abstraction
the reps theorem runs on:

- **Theorem A** (trivial ⟹ strongly schedulable): a trivialization *is* a schedule — the
  canonical dips route every surviving defect into one finite per-top set.
- **Lemma F** (below-level absorption): below an element's own level the fiber inequality
  `s_x ≤ s_u` transfers through the floors, so those coordinates never leak.

These are the pieces the contested open heart (Question 5) rests on; machine-checking
them makes the proved skeleton unimpeachable while the heart stays open. -/

section DipSchedule
open Classical
variable {W : Type} {WI : WellIndex W}

/-- **Upward defect** `D⁺(a,b)` (for `a ≤ b`): coordinates below `a` where row `a`
    exceeds row `b`. -/
def upDefect (C : CoherentSeq W WI) (a b : W) : W → Prop :=
  fun u => WI.lt u a ∧ C.e a u > C.e b u

/-- The **canonical trivialization dip** at source level `a`: where row `a` deviates from
    the global row `E`. -/
def trivDip (C : CoherentSeq W WI) (E : W → Nat) (a : W) : W → Prop :=
  fun u => WI.lt u a ∧ C.e a u ≠ E u

/-- The schedule leftover at a top `t`: coordinates surviving *some* source `a ≤ t`'s
    canonical dip while still defecting against `t`. (`γ = μ`; the union over sources
    `x ⊑ u` collapses to a quantifier over source levels `a ≤ t`.) -/
def scheduleLeftover (C : CoherentSeq W WI) (E : W → Nat) (t : W) : W → Prop :=
  fun u => ∃ a, WI.le a t ∧ upDefect C a t u ∧ ¬ trivDip C E a u

/-- **Theorem A (leftover containment).** Every coordinate surviving the canonical dips
    at top `t` lies in the single `t`-local set where the global row `E` disagrees with
    row `t`. This is the whole content: the union over sources lands in one finite set. -/
theorem thmA_leftover_subset (C : CoherentSeq W WI) (E : W → Nat) (t u : W)
    (hu : scheduleLeftover C E t u) : WI.lt u t ∧ E u ≠ C.e t u := by
  obtain ⟨a, hat, hdef, hndip⟩ := hu
  obtain ⟨hua, hgt⟩ := hdef
  have heq : C.e a u = E u :=
    Classical.byContradiction (fun hne => hndip ⟨hua, hne⟩)
  refine ⟨⟨WI.le_trans hua.1 hat, fun htu => hua.2 (WI.le_trans hat htu)⟩, ?_⟩
  intro hEt; rw [heq] at hgt; omega

/-- **Theorem A (trivial ⟹ strongly schedulable).** For a trivial coherent sequence, the
    canonical trivialization dips make the schedule leftover finite at every top — the
    schedule condition. -/
theorem thmA_schedulable (C : CoherentSeq W WI) (E : W → Nat)
    (hE : ∀ w, FiniteP (fun u => WI.lt u w ∧ E u ≠ C.e w u)) (t : W) :
    FiniteP (scheduleLeftover C E t) :=
  FiniteP.mono (fun _ hu => thmA_leftover_subset C E t _ hu) (hE t)

/-- **Lemma F (below-level absorption).** Below an element's own level `lx`, if the fiber
    functions satisfy `s_x ≤ s_u` (the order relation `x ⊑ u`) and the floors agree with
    the fiber functions there, then the coordinate carries no upward defect: the below-
    level leftover is contained in the two finite fiber-deviation sets. -/
theorem lemmaF_below_subset (C : CoherentSeq W WI) (sx su : W → Nat) (gx gu lx u : W)
    (hle : sx u ≤ su u) (hu : WI.lt u lx ∧ upDefect C gx gu u) :
    C.e gx u ≠ sx u ∨ C.e gu u ≠ su u := by
  obtain ⟨_, hdef⟩ := hu
  obtain ⟨_, hgt⟩ := hdef
  by_cases h1 : C.e gx u = sx u
  · by_cases h2 : C.e gu u = su u
    · exfalso; rw [h1, h2] at hgt; omega
    · exact Or.inr h2
  · exact Or.inl h1

/-- **Lemma F, finiteness form.** With `s_x ≤ s_u` throughout the below-level region, the
    below-level leftover is finite, being covered by the two fiber-deviation sets (finite
    since fiber functions are `=*` their floors). -/
theorem lemmaF_below_finite (C : CoherentSeq W WI) (sx su : W → Nat) (gx gu lx : W)
    (hle : ∀ u, WI.lt u lx → sx u ≤ su u)
    (hfibx : FiniteP (fun u => C.e gx u ≠ sx u))
    (hfibu : FiniteP (fun u => C.e gu u ≠ su u)) :
    FiniteP (fun u => WI.lt u lx ∧ upDefect C gx gu u) :=
  FiniteP.mono (fun u hu => lemmaF_below_subset C sx su gx gu lx u (hle u hu.1) hu)
    (hfibx.union hfibu)

end DipSchedule

/-! ## The escapee framework, machine-checked: Theorem I (forward) and the top route

`NOTES-coherent-escapee.md` §38 (Theorem I) reduces the transport line's qualitative
residual `Φ(D)` — *every legal constraint system on a directed order `D` has a monotone
dominator* — to a single condition: `D` admits a **monotone dominating retraction** of its
σ-ideal completion. The forward direction (retraction ⟹ Φ) and the unification of the three
sufficient routes (top / bounded-complete / ruler) as instances of one retraction are ZFC
order theory, index-agnostic, and formalize directly. This is the proved core of the
escapee analysis; the converse (Φ ⟹ retraction, §39) is an open uniformization and is *not*
claimed here. -/

section EscapeeTheory

/-- A directed order (the abstract carrier of the escapee question): a preorder. -/
structure DirOrder (D : Type) where
  le       : D → D → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c

/-- A **legal constraint system**: constraint sets `M u` monotone in `u` and bounded. -/
structure LegalSystem {D : Type} (O : DirOrder D) where
  M    : D → D → Prop
  mono : ∀ {u u'}, O.le u u' → ∀ w, M u w → M u' w
  bdd  : ∀ u, ∃ b, ∀ w, M u w → O.le w b

/-- A **monotone dominator** of a legal system. -/
structure Dominator {D : Type} {O : DirOrder D} (L : LegalSystem O) where
  φ    : D → D
  mono : ∀ {u u'}, O.le u u' → O.le (φ u) (φ u')
  dom  : ∀ u w, L.M u w → O.le w (φ u)

/-- **`Φ(D)`**: every legal constraint system admits a monotone dominator. Its negation is
    the transport *escapee*. -/
def Phi {D : Type} (O : DirOrder D) : Prop :=
  ∀ L : LegalSystem O, Nonempty (Dominator L)

/-- A **monotone dominating retraction** (the abstract form of §38's three routes): assigns
    to each bounded constraint set an upper bound, monotonically. Not required to be a
    *least* upper bound — so it covers the top route (`r ≡ ⊤`) and the ruler route, not only
    bounded-completeness (`r = ⊔`). -/
structure DomRetraction {D : Type} (O : DirOrder D) where
  r    : (D → Prop) → D
  ub   : ∀ (S : D → Prop) (b : D), (∀ w, S w → O.le w b) → ∀ w, S w → O.le w (r S)
  mono : ∀ (S T : D → Prop) (b : D), (∀ w, T w → O.le w b) → (∀ w, S w → T w) →
           O.le (r S) (r T)

/-- **Theorem I (forward): a dominating retraction gives `Φ`.** For a legal `L`, the map
    `u ↦ r (M u)` is a monotone dominator — domination from `r`'s upper-bound clause,
    monotonicity from `r`'s monotone clause applied to `M u ⊆ M u'` under `u`'s bound. -/
theorem phi_of_domRetraction {D : Type} {O : DirOrder D} (R : DomRetraction O) : Phi O := by
  intro L
  refine ⟨{ φ := fun u => R.r (L.M u), mono := ?_, dom := ?_ }⟩
  · intro u u' huu'
    obtain ⟨b', hb'⟩ := L.bdd u'
    exact R.mono (L.M u) (L.M u') b' hb' (fun w hw => L.mono huu' w hw)
  · intro u w hw
    obtain ⟨b, hb⟩ := L.bdd u
    exact R.ub (L.M u) b hb w hw

/-- **The top route as a retraction.** A top element is a constant dominating retraction. -/
def domRetraction_of_top {D : Type} (O : DirOrder D) (top : D) (htop : ∀ d, O.le d top) :
    DomRetraction O where
  r    := fun _ => top
  ub   := fun _ _ _ w _ => htop w
  mono := fun _ _ _ _ _ => O.le_refl top

/-- **Top ⟹ `Φ`** (`Dm`'s route: `Dm_factors`), as an instance of Theorem I. -/
theorem phi_of_top {D : Type} (O : DirOrder D) (top : D) (htop : ∀ d, O.le d top) : Phi O :=
  phi_of_domRetraction (domRetraction_of_top O top htop)

/-- **The bounded-complete route as a retraction** (Theorem H): a join operator that is an
    upper bound and monotone on commonly-bounded sets is a dominating retraction. -/
def domRetraction_of_join {D : Type} (O : DirOrder D)
    (join : (D → Prop) → D)
    (join_ub : ∀ (S : D → Prop) (b : D), (∀ w, S w → O.le w b) → ∀ w, S w → O.le w (join S))
    (join_mono : ∀ (S T : D → Prop) (b : D), (∀ w, T w → O.le w b) → (∀ w, S w → T w) →
                   O.le (join S) (join T)) :
    DomRetraction O where
  r    := join
  ub   := join_ub
  mono := join_mono

/-- **Bounded-complete ⟹ `Φ`** (Theorem H; `Fb`/lattice route), as an instance of Theorem I. -/
theorem phi_of_join {D : Type} (O : DirOrder D)
    (join : (D → Prop) → D)
    (join_ub : ∀ (S : D → Prop) (b : D), (∀ w, S w → O.le w b) → ∀ w, S w → O.le w (join S))
    (join_mono : ∀ (S T : D → Prop) (b : D), (∀ w, T w → O.le w b) → (∀ w, S w → T w) →
                   O.le (join S) (join T)) :
    Phi O :=
  phi_of_domRetraction (domRetraction_of_join O join join_ub join_mono)

/-! ### The forcing bridge (PFA side): a generic covering family yields Φ

`NOTES-coherent-escapee.md` §25–§26, §39: the PFA side of the escapee independence goes
through the frozen-dip realization poset `P(Σ)` — its generic filter assembles a monotone
dominator out of finite partial pieces. Proving `P(Σ)` *proper* is the open checkpoint and
is **not** formalized (there is no proof). What is proved and machine-checked here is the
*bridge*: the object a proper poset's generic filter would provide — a covering, coherent,
cross-monotone family of finite partial dominators — yields `Φ`. This isolates the open part
(existence of such a family = properness + forcing axiom) as the single hypothesis and
verifies everything downstream. -/

/-- A **partial dominator**: a domain predicate with values, monotone and dominating on the
    domain (a finite condition of `P(Σ)`, here with an arbitrary domain). -/
structure PartialDom {D : Type} {O : DirOrder D} (L : LegalSystem O) where
  inDom     : D → Prop
  val       : D → D
  mono      : ∀ {u u'}, inDom u → inDom u' → O.le u u' → O.le (val u) (val u')
  dominates : ∀ {u}, inDom u → ∀ w, L.M u w → O.le w (val u)

/-- A **generic covering family** — the object a proper poset's generic filter provides:
    a family of partial dominators covering `D`, with cohering values and monotonicity
    across the whole family (the frozen, coherent selection). Its *existence* is the open
    properness/forcing content; its *sufficiency* is `phi_of_generic`. -/
structure GenericDom {D : Type} {O : DirOrder D} (L : LegalSystem O) where
  ι     : Type
  p     : ι → PartialDom L
  cover : ∀ u, ∃ i, (p i).inDom u
  cross : ∀ i j u u', (p i).inDom u → (p j).inDom u' → O.le u u' →
            O.le ((p i).val u) ((p j).val u')

/-- **The forcing bridge: a generic covering family yields `Φ`.** Choose a covering
    condition per element; its value defines `φ`, monotone by cross-family monotonicity and
    dominating by each condition's domination. (The generic family is what PFA supplies once
    `P(Σ)` is proper — the open step, not this lemma.) -/
theorem phi_of_generic {D : Type} {O : DirOrder D} {L : LegalSystem O}
    (G : GenericDom L) : Nonempty (Dominator L) := by
  classical
  refine ⟨{ φ := fun u => (G.p (G.cover u).choose).val u, mono := ?_, dom := ?_ }⟩
  · intro u u' huu'
    exact G.cross _ _ u u' (G.cover u).choose_spec (G.cover u').choose_spec huu'
  · intro u w hw
    exact (G.p (G.cover u).choose).dominates (G.cover u).choose_spec w hw

/-! ### The properness question, attacked directly: compatibility ⟺ cross-monotonicity

Rather than assume the generic, we analyze compatibility of conditions itself — the content
of ccc/properness. The result below is exact: two conditions have a common extension **iff**
their combined values are cross-monotone (given they agree on the overlap). Domination and
"agreeing on the overlap" amalgamate for free; the *sole* obstruction to compatibility is
cross-monotonicity — i.e. the cross-defect `D⁺(μx, μu)` fitting the frozen data. This turns
"`P(Σ)` ccc" into the single combinatorial statement: *among any `ℵ₁` conditions, two are
cross-monotone.* -/

/-- Two conditions are **compatible** if one condition extends both (value-preservingly). -/
def PartialDom.compat {D : Type} {O : DirOrder D} {L : LegalSystem O} (p q : PartialDom L) :
    Prop :=
  ∃ r : PartialDom L,
    (∀ u, p.inDom u → r.inDom u ∧ r.val u = p.val u) ∧
    (∀ u, q.inDom u → r.inDom u ∧ r.val u = q.val u)

/-- **Amalgamation (the proper-poset core): agreeing + cross-monotone ⟹ compatible.** If
    `p, q` agree on their overlap and their combined values are monotone across the two
    domains (both directions), the pointwise union *is* a common extension — a partial
    dominator. So the *only* barrier to compatibility is cross-monotonicity; everything else
    (domination, overlap-consistency) amalgamates. Machine-checked; the ccc of `P(Σ)` is
    thereby exactly "every `ℵ₁`-family of conditions contains a cross-monotone pair." -/
theorem PartialDom.compat_of_crossMono {D : Type} {O : DirOrder D} {L : LegalSystem O}
    (p q : PartialDom L)
    (agree : ∀ u, p.inDom u → q.inDom u → p.val u = q.val u)
    (cross_pq : ∀ u u', p.inDom u → q.inDom u' → O.le u u' → O.le (p.val u) (q.val u'))
    (cross_qp : ∀ u u', q.inDom u → p.inDom u' → O.le u u' → O.le (q.val u) (p.val u')) :
    p.compat q := by
  classical
  refine ⟨{ inDom := fun u => p.inDom u ∨ q.inDom u
            val   := fun u => if p.inDom u then p.val u else q.val u
            mono  := ?_, dominates := ?_ }, ?_, ?_⟩
  · -- cross-monotonicity of the union, by 4 cases on membership of `u`, `u'`
    intro u u' hu hu' huu'
    by_cases hpu : p.inDom u <;> by_cases hpu' : p.inDom u'
    · simp only [if_pos hpu, if_pos hpu']; exact p.mono hpu hpu' huu'
    · simp only [if_pos hpu, if_neg hpu']
      exact cross_pq u u' hpu (hu'.resolve_left hpu') huu'
    · simp only [if_neg hpu, if_pos hpu']
      exact cross_qp u u' (hu.resolve_left hpu) hpu' huu'
    · simp only [if_neg hpu, if_neg hpu']
      exact q.mono (hu.resolve_left hpu) (hu'.resolve_left hpu') huu'
  · -- domination of the union
    intro u hu w hw
    by_cases hpu : p.inDom u
    · simp only [if_pos hpu]; exact p.dominates hpu w hw
    · simp only [if_neg hpu]; exact q.dominates (hu.resolve_left hpu) w hw
  · -- `r` extends `p`
    intro u hpu; exact ⟨Or.inl hpu, if_pos hpu⟩
  · -- `r` extends `q` (uses `agree` on the overlap)
    intro u hqu
    refine ⟨Or.inr hqu, ?_⟩
    by_cases hpu : p.inDom u
    · simp only [if_pos hpu]; exact agree u hpu hqu
    · simp only [if_neg hpu]

/-! ### The single-element case, machine-checked (ZFC)

The one fragment of the ccc/properness analysis that is a genuine ZFC theorem — the boundary
where ZFC stops. A *single-element condition* is one whose domain is a point `u₀` (value a
bound of `M u₀`). Two such with **incomparable** domains are compatible (`compat_of_crossMono`
with vacuous cross-clauses), so a pairwise-*incompatible* family of single-element conditions
has pairwise-*comparable* domains — a chain. Since a nontrivial coherent sequence's fiber
order has no uncountable chain (`Lemma D` — the one cardinality fact, left in prose), any
uncountable such family is impossible: the single-element poset is ccc. The multi-element
case is where the cross-defects conspire, and that is the axiom-dependent part (§40) — not
formalized, because it is not a ZFC theorem. -/

/-- A **single-element condition** at `u₀`: domain `{u₀}`, value a bound of `M u₀`. -/
noncomputable def singletonDom {D : Type} {O : DirOrder D} (L : LegalSystem O) (u₀ : D) :
    PartialDom L where
  inDom     := fun u => u = u₀
  val       := fun _ => (L.bdd u₀).choose
  mono      := fun _ _ _ => O.le_refl _
  dominates := fun {u} hu w hw => (L.bdd u₀).choose_spec w (hu ▸ hw)

/-- **Incomparable single-element conditions are compatible.** The cross-clauses of
    `compat_of_crossMono` are vacuous (the only possible cross-comparabilities are
    `u₀ ⊑ v₀` / `v₀ ⊑ u₀`, both excluded), and the overlap is empty (`u₀ ≠ v₀`). -/
theorem singletonDom_compat_of_incomp {D : Type} {O : DirOrder D} (L : LegalSystem O)
    (u₀ v₀ : D) (hne : u₀ ≠ v₀) (h1 : ¬ O.le u₀ v₀) (h2 : ¬ O.le v₀ u₀) :
    (singletonDom L u₀).compat (singletonDom L v₀) := by
  apply PartialDom.compat_of_crossMono
  · intro u hpu hqu; exact absurd (hpu.symm.trans hqu) hne
  · intro u u' hpu hqu' hle; subst hpu; subst hqu'; exact absurd hle h1
  · intro u u' hqu hpu' hle; subst hqu; subst hpu'; exact absurd hle h2

/-- **Incompatible single-element conditions have comparable domains.** Contrapositive of
    the above — the ccc core. -/
theorem singletonDom_incompat_comparable {D : Type} {O : DirOrder D} (L : LegalSystem O)
    (u₀ v₀ : D) (hne : u₀ ≠ v₀)
    (hincompat : ¬ (singletonDom L u₀).compat (singletonDom L v₀)) :
    O.le u₀ v₀ ∨ O.le v₀ u₀ :=
  Classical.byContradiction (fun h =>
    hincompat (singletonDom_compat_of_incomp L u₀ v₀ hne
      (fun h1 => h (Or.inl h1)) (fun h2 => h (Or.inr h2))))

/-- **The single-element poset is ccc, in ZFC (the antichain-is-a-chain core).** A family of
    single-element conditions at distinct points that is pairwise incompatible (an antichain)
    has pairwise-comparable domains — a **chain**. Combined with `Lemma D` (a nontrivial
    coherent sequence's fiber order has no uncountable chain — the one cardinality fact, cited
    not formalized), no uncountable such antichain exists: ccc. The multi-element case is
    axiom-dependent (§40) and deliberately absent. -/
theorem singleton_antichain_is_chain {D : Type} {O : DirOrder D} (L : LegalSystem O)
    {I : Type} (u : I → D) (hinj : ∀ i j, u i = u j → i = j)
    (hanti : ∀ i j, i ≠ j → ¬ (singletonDom L (u i)).compat (singletonDom L (u j))) :
    ∀ i j, i ≠ j → O.le (u i) (u j) ∨ O.le (u j) (u i) := by
  intro i j hij
  exact singletonDom_incompat_comparable L (u i) (u j)
    (fun h => hij (hinj i j h)) (hanti i j hij)

end EscapeeTheory

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
