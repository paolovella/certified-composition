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
