/-
  Fixpoint may-alias — brick 30: closing brick 24's one-pass loop rule.

  Brick 24's loop rule is **one-pass**: the body must preserve every entry class
  in a single check, so a loop that legitimately *maintains* an alias across the
  back-edge — e.g. `while (…) copy 1 0` with two pointers live on entry — is
  rejected, because after one body pass `0` and `1` have merged and the entry
  classes `[0]`, `[1]` are gone. A real may-alias analysis **infers a coarsening
  invariant** by iterating the body transfer to a fixed point.

  This brick adds that, reusing brick 24's machine, checker, and soundness:

  * `Coarsens P Q` / `ALInv_coarsen` — merging classes only *weakens* the
    may-alias over-approximation (fewer "different class" pairs), so `ALInv P`
    always implies `ALInv Q` for a coarsening `Q`. This is the semantic heart:
    a coarser invariant is sound whenever the finer one is.
  * `mergeOne` / `ALInv_of_setSub` — set-equality comparison of classes (order-
    insensitive), which a fixed point needs (the checker rebuilds classes in a
    different order each pass).
  * `loopFix` — iterate the body transfer, merging classes until the candidate is
    preserved. Its **partial correctness** is proved (`loopFix_correct`): if it
    returns `Q`, then `Q` coarsens the entry and is preserved. Its **convergence**
    is proved too (`loopFix_terminates`): each merge strictly shrinks the class
    count, so the search reaches its final answer within `|P| + 1` fuel and never
    diverges. What is *not* claimed is *completeness* — that it always terminates
    in success rather than giving up — which depends on the merge heuristic.
  * `coarsen_loop_safe` — the loop is memory-safe from the inferred invariant
    (fuel induction, reusing brick 24's `alsafe` for the body).
  * `alias_maintain_loop_safe` — the witness brick 24 rejected: with `0` and `1`
    live and distinct on entry, `while (…) copy 1 0` is accepted (the fixpoint
    infers `[[0,1]]`) and never errors; `brick24_rejects` shows brick 24's
    one-pass rule returns `none` on the same loop.

  Honest limit carried forward: the merge heuristic is basic (merge the first two
  classes when not yet preserved); a precise join (merge exactly the classes the
  body unified) is a precision follow-on, and the rule is integrated for the loop
  as an analyzed unit.
-/
import ConfTyping.AliasLoop

namespace ConfTyping

/-! ## Set-equality comparison of partitions -/

def subOf (a d : List HLoc) : Bool := a.all (fun z => decide (z ∈ d))
def sameElemsB (a b : List HLoc) : Bool := subOf a b && subOf b a
def clsInB (cls : List HLoc) (Q₁ : Part) : Bool := Q₁.any (fun d => sameElemsB cls d)
/-- Every class of `Q` has the same elements as some class of `Q₁`. -/
def preservedB (Q Q₁ : Part) : Bool := Q.all (fun cls => clsInB cls Q₁)

theorem subOf_iff {a d : List HLoc} : subOf a d = true ↔ ∀ z ∈ a, z ∈ d := by
  simp only [subOf, List.all_eq_true, decide_eq_true_eq]

theorem preservedB_spec {Q Q₁ : Part} (h : preservedB Q Q₁ = true) :
    ∀ cls ∈ Q, ∃ d ∈ Q₁, (∀ z ∈ cls, z ∈ d) ∧ (∀ z ∈ d, z ∈ cls) := by
  intro cls hcls
  have := (List.all_eq_true.mp h) cls hcls
  simp only [clsInB, List.any_eq_true] at this
  obtain ⟨d, hd, hsame⟩ := this
  simp only [sameElemsB, Bool.and_eq_true] at hsame
  exact ⟨d, hd, subOf_iff.mp hsame.1, subOf_iff.mp hsame.2⟩

/-! ## Coarsening preserves the invariant -/

/-- `Q` coarsens `P`: same live set, and every may-alias of `P` is a may-alias of
    `Q` (merging can only add aliases), with `Q` a proper partition. -/
def Coarsens (P Q : Part) : Prop :=
  (∀ z, liveP P z ↔ liveP Q z) ∧
  (∀ x y, sameClassP P x y → sameClassP Q x y) ∧
  disjP Q

/-- **Coarsening is sound.** A coarser may-alias invariant holds whenever the
    finer one does — merging classes only weakens the separation guarantee. -/
theorem ALInv_coarsen {P Q : Part} {s : FLState} (h : Coarsens P Q) (hP : ALInv P s) :
    ALInv Q s := by
  obtain ⟨σ, n, F⟩ := s
  obtain ⟨hlive, hsame, hdjQ⟩ := h
  obtain ⟨hli, hsc, hfr, _⟩ := hP
  refine ⟨fun z hz => hli z ((hlive z).mpr hz), ?_, hfr, hdjQ⟩
  intro x y hx hy hxy
  exact hsame x y (hsc x y ((hlive x).mpr hx) ((hlive y).mpr hy) hxy)

/-! ## Merging two classes -/

def mergeOne (a b : List HLoc) (Q : Part) : Part :=
  (a ++ b) :: Q.filter (fun c => decide (c ≠ a) && decide (c ≠ b))

theorem mem_mergeFilter {c a b : List HLoc} {Q : Part} :
    c ∈ Q.filter (fun c => decide (c ≠ a) && decide (c ≠ b)) ↔ c ∈ Q ∧ c ≠ a ∧ c ≠ b := by
  simp [List.mem_filter, decide_eq_true_eq, Bool.and_eq_true, and_assoc]

theorem liveP_mergeOne {a b : List HLoc} {Q : Part} {z : HLoc}
    (ha : a ∈ Q) (hb : b ∈ Q) : liveP (mergeOne a b Q) z ↔ liveP Q z := by
  constructor
  · rintro ⟨cls, hcls, hz⟩
    rw [mergeOne, List.mem_cons] at hcls
    rcases hcls with rfl | hcls
    · rcases List.mem_append.mp hz with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    · exact ⟨cls, (mem_mergeFilter.mp hcls).1, hz⟩
  · rintro ⟨cls, hcls, hz⟩
    by_cases hca : cls = a
    · exact ⟨a ++ b, by simp [mergeOne], List.mem_append_left b (hca ▸ hz)⟩
    · by_cases hcb : cls = b
      · exact ⟨a ++ b, by simp [mergeOne], List.mem_append_right a (hcb ▸ hz)⟩
      · exact ⟨cls, by rw [mergeOne, List.mem_cons]; exact Or.inr (mem_mergeFilter.mpr ⟨hcls, hca, hcb⟩), hz⟩

theorem sameClassP_mergeOne {a b : List HLoc} {Q : Part} {x y : HLoc}
    (h : sameClassP Q x y) : sameClassP (mergeOne a b Q) x y := by
  obtain ⟨cls, hcls, hxc, hyc⟩ := h
  by_cases hca : cls = a
  · exact ⟨a ++ b, by simp [mergeOne], List.mem_append_left b (hca ▸ hxc), List.mem_append_left b (hca ▸ hyc)⟩
  · by_cases hcb : cls = b
    · exact ⟨a ++ b, by simp [mergeOne], List.mem_append_right a (hcb ▸ hxc), List.mem_append_right a (hcb ▸ hyc)⟩
    · exact ⟨cls, by rw [mergeOne, List.mem_cons]; exact Or.inr (mem_mergeFilter.mpr ⟨hcls, hca, hcb⟩),
        hxc, hyc⟩

theorem disjP_mergeOne {a b : List HLoc} {Q : Part} (hdj : disjP Q)
    (ha : a ∈ Q) (hb : b ∈ Q) : disjP (mergeOne a b Q) := by
  intro z c₁ c₂ h1 h2 hz1 hz2
  rw [mergeOne, List.mem_cons] at h1 h2
  rcases h1 with rfl | h1f
  · rcases h2 with rfl | h2f
    · rfl
    · obtain ⟨h2Q, h2a, h2b⟩ := mem_mergeFilter.mp h2f
      rcases List.mem_append.mp hz1 with h | h
      · exact absurd (hdj z a c₂ ha h2Q h hz2) (fun e => h2a e.symm)
      · exact absurd (hdj z b c₂ hb h2Q h hz2) (fun e => h2b e.symm)
  · rcases h2 with rfl | h2f
    · obtain ⟨h1Q, h1a, h1b⟩ := mem_mergeFilter.mp h1f
      rcases List.mem_append.mp hz2 with h | h
      · exact absurd (hdj z c₁ a h1Q ha hz1 h) h1a
      · exact absurd (hdj z c₁ b h1Q hb hz1 h) h1b
    · exact hdj z c₁ c₂ (mem_mergeFilter.mp h1f).1 (mem_mergeFilter.mp h2f).1 hz1 hz2

/-- `mergeOne` coarsens: it preserves a coarsening of `P`. -/
theorem Coarsens_mergeOne {P Q : Part} {a b : List HLoc}
    (h : Coarsens P Q) (ha : a ∈ Q) (hb : b ∈ Q) : Coarsens P (mergeOne a b Q) := by
  obtain ⟨hlive, hsame, hdj⟩ := h
  refine ⟨fun z => (hlive z).trans (liveP_mergeOne ha hb).symm, ?_, disjP_mergeOne hdj ha hb⟩
  intro x y hxy
  exact sameClassP_mergeOne (hsame x y hxy)

/-! ## Set-preservation transports the invariant -/

/-- If every class of `Q` has the same elements as some class of `Q₁`, and both
    are proper partitions, then `ALInv Q₁` gives `ALInv Q`. This is the order-
    insensitive analogue of `ALInv_of_sub`. -/
theorem ALInv_of_setSub {Q Q₁ : Part} {s : FLState}
    (hpres : preservedB Q Q₁ = true) (hdjQ : disjP Q) (hQ₁ : ALInv Q₁ s) : ALInv Q s := by
  obtain ⟨σ, n, F⟩ := s
  obtain ⟨hli, hsc, hfr, hdjQ₁⟩ := hQ₁
  have key := preservedB_spec hpres
  -- a live var of Q is a live var of Q₁ (through its set-equal Q₁-class)
  have hlift : ∀ z, liveP Q z → liveP Q₁ z := by
    rintro z ⟨cls, hcls, hz⟩
    obtain ⟨d, hd, hsub, _⟩ := key cls hcls
    exact ⟨d, hd, hsub z hz⟩
  refine ⟨fun z hz => hli z (hlift z hz), ?_, hfr, hdjQ⟩
  intro x y hx hy hxy
  obtain ⟨d, hd, hxd, hyd⟩ := hsc x y (hlift x hx) (hlift y hy) hxy
  -- x's Q-class cx is set-equal to a Q₁-class, which disjP Q₁ forces to be d
  obtain ⟨cx, hcxQ, hxcx⟩ := hx
  obtain ⟨dx, hdx, hsubx, hsupx⟩ := key cx hcxQ
  have : dx = d := hdjQ₁ x dx d hdx hd (hsubx x hxcx) hxd
  subst this
  -- y also lands in cx: y ∈ d = dx set-equal cx
  exact ⟨cx, hcxQ, hxcx, hsupx y hyd⟩

/-! ## The fixpoint iterator -/

/-- Pick two classes to merge — the basic heuristic merges the first two. -/
def findMerge : Part → Option (List HLoc × List HLoc)
  | a :: b :: _ => some (a, b)
  | _           => none

theorem findMerge_mem {Q : Part} {a b : List HLoc} (h : findMerge Q = some (a, b)) :
    a ∈ Q ∧ b ∈ Q := by
  cases Q with
  | nil => simp [findMerge] at h
  | cons c cs => cases cs with
    | nil => simp [findMerge] at h
    | cons d ds =>
        simp only [findMerge, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp, by simp⟩

/-- Iterate the body transfer, merging classes until the candidate is preserved.
    Uses brick 24's `alcheck` for the body (nested loops keep the one-pass rule). -/
def loopFix : Nat → Part → ALCmd → Option Part
  | 0,   _, _ => none
  | f+1, Q, c =>
      match alcheck Q c with
      | some Q₁ =>
          if preservedB Q Q₁ then some Q
          else match findMerge Q with
               | some (a, b) => loopFix f (mergeOne a b Q) c
               | none        => none
      | none => none

/-- **Partial correctness of the fixpoint search.** If `loopFix` returns `R` from
    a coarsening `Q` of `P`, then `R` still coarsens `P`, and `R` is preserved by
    the body (`alcheck R c` set-equals `R`). Convergence is not asserted. -/
theorem loopFix_correct {P : Part} {c : ALCmd} :
    ∀ (f : Nat) (Q R : Part), Coarsens P Q → loopFix f Q c = some R →
      Coarsens P R ∧ ∃ R₁, alcheck R c = some R₁ ∧ preservedB R R₁ = true := by
  intro f
  induction f with
  | zero => intro Q R _ h; simp [loopFix] at h
  | succ k ih =>
      intro Q R hCo h
      cases hchk : alcheck Q c with
      | none => simp [loopFix, hchk] at h
      | some Q₁ =>
          simp only [loopFix, hchk] at h
          by_cases hpres : preservedB Q Q₁ = true
          · rw [if_pos hpres, Option.some.injEq] at h; subst h
            exact ⟨hCo, Q₁, hchk, hpres⟩
          · rw [if_neg hpres] at h
            cases hfm : findMerge Q with
            | none => simp [hfm] at h
            | some ab =>
                obtain ⟨a, b⟩ := ab
                simp only [hfm] at h
                obtain ⟨ha, hb⟩ := findMerge_mem hfm
                exact ih (mergeOne a b Q) R (Coarsens_mergeOne hCo ha hb) h

/-! ## Convergence: the search always terminates -/

theorem findMerge_eq {Q : Part} {a b : List HLoc} (h : findMerge Q = some (a, b)) :
    ∃ rest, Q = a :: b :: rest := by
  cases Q with
  | nil => simp [findMerge] at h
  | cons c cs => cases cs with
    | nil => simp [findMerge] at h
    | cons d ds =>
        simp only [findMerge, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ds, rfl⟩

/-- **Each merge step strictly shrinks the partition.** `mergeOne` on the first
    two classes removes both and adds one, so the class count drops — the
    termination measure of the fixpoint iteration. -/
theorem findMerge_mergeOne_length {Q : Part} {a b : List HLoc}
    (h : findMerge Q = some (a, b)) : (mergeOne a b Q).length < Q.length := by
  obtain ⟨rest, rfl⟩ := findMerge_eq h
  have hfil : (a :: b :: rest).filter (fun x => decide (x ≠ a) && decide (x ≠ b))
      = rest.filter (fun x => decide (x ≠ a) && decide (x ≠ b)) := by
    simp [List.filter_cons]
  simp only [mergeOne, hfil, List.length_cons]
  have hle := List.length_filter_le (fun x => decide (x ≠ a) && decide (x ≠ b)) rest
  omega

/-- **Convergence of the fixpoint search.** The outcome of `loopFix` is fixed once
    the fuel reaches the entry class count plus one: every extra step is either a
    class-count-reducing merge (at most `|Q|` of them) or a terminal decision, so
    the search never diverges. Proved by induction on a bound of the class count,
    using the strict `mergeOne` decrease. -/
theorem loopFix_converges (c : ALCmd) :
    ∀ (n : Nat) (Q : Part), Q.length ≤ n →
      ∀ f g, Q.length + 1 ≤ f → Q.length + 1 ≤ g → loopFix f Q c = loopFix g Q c := by
  intro n
  induction n with
  | zero =>
      intro Q hQ f g hf hg
      have hQe : Q = [] := by cases Q with | nil => rfl | cons => simp at hQ
      subst hQe
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      simp only [loopFix]
      cases alcheck [] c with
      | none => rfl
      | some Q₁ => simp [preservedB]
  | succ n ih =>
      intro Q hQ f g hf hg
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      simp only [loopFix]
      cases hchk : alcheck Q c with
      | none => rfl
      | some Q₁ =>
          by_cases hp : preservedB Q Q₁ = true
          · simp [hp]
          · simp only [if_neg hp]
            cases hfm : findMerge Q with
            | none => rfl
            | some ab =>
                obtain ⟨a, b⟩ := ab
                simp only [hfm]
                have hlt : (mergeOne a b Q).length < Q.length := findMerge_mergeOne_length hfm
                exact ih (mergeOne a b Q) (by omega) f' g' (by omega) (by omega)

/-- **The search reaches its final answer within `|Q| + 1` fuel** — more fuel never
    changes the result, so the fixpoint iteration always terminates. -/
theorem loopFix_terminates (Q : Part) (c : ALCmd) {f : Nat} (hf : Q.length + 1 ≤ f) :
    loopFix f Q c = loopFix (Q.length + 1) Q c :=
  loopFix_converges c Q.length Q (Nat.le_refl _) f (Q.length + 1) hf (Nat.le_refl _)

/-! ## The loop is sound from the inferred invariant -/

/-- **A coarsening-invariant loop is memory-safe.** If `Q` is preserved by the
    body and disjoint, then from `ALInv Q` the loop never errors and preserves
    `ALInv Q`. Fuel induction, reusing brick 24's `alsafe` for the body. -/
theorem coarsen_loop_safe {e : HLExpr} {c : ALCmd} {Q Q₁ : Part}
    (hchk : alcheck Q c = some Q₁) (hpres : preservedB Q Q₁ = true) (hdj : disjP Q) :
    ∀ (fuel : Nat) (s : FLState), ALInv Q s →
      alexec fuel (.loop e c) s ≠ .err ∧
        (∀ s', alexec fuel (.loop e c) s = .ok s' → ALInv Q s') := by
  intro fuel
  induction fuel with
  | zero => intro s _; exact ⟨by simp [alexec], by intro s' h; simp [alexec] at h⟩
  | succ k ih =>
      intro s hQs
      obtain ⟨σ, n, F⟩ := s
      have bodyPres : ∀ s₁, alexec k c (σ, n, F) = .ok s₁ → ALInv Q s₁ := fun s₁ hs₁ =>
        ALInv_of_setSub hpres hdj ((alsafe k c Q Q₁ (σ, n, F) hchk hQs).2 s₁ hs₁)
      refine ⟨?_, ?_⟩
      · simp only [alexec]; split
        · exact flbind_ne_err (alsafe k c Q Q₁ (σ, n, F) hchk hQs).1
            (fun s₁ hs₁ => (ih s₁ (bodyPres s₁ hs₁)).1)
        · simp [FLRes.bind]
      · intro s' hs; simp only [alexec] at hs; split at hs
        · obtain ⟨s₁, ho₁, ho₂⟩ := flbind_ok hs
          exact (ih s₁ (bodyPres s₁ ho₁)).2 s' ho₂
        · rw [FLRes.ok.injEq] at hs; subst hs; exact hQs

/-- **Certified safe from a fixpoint-inferred invariant.** If `loopFix` infers a
    coarsening invariant of the entry partition `P`, the loop is memory-safe from
    any state satisfying `ALInv P`. -/
theorem coarsen_loop_of_fix {e : HLExpr} {c : ALCmd} {P Q : Part} {s : FLState} {ff : Nat}
    (fuel : Nat) (hCoP : disjP P) (hfix : loopFix ff P c = some Q) (hPs : ALInv P s) :
    alexec fuel (.loop e c) s ≠ .err := by
  have hCo : Coarsens P P := ⟨fun _ => Iff.rfl, fun _ _ h => h, hCoP⟩
  obtain ⟨hCoQ, Q₁, hchk, hpres⟩ := loopFix_correct ff P Q hCo hfix
  have hQs : ALInv Q s := ALInv_coarsen hCoQ hPs
  exact (coarsen_loop_safe hchk hpres hCoQ.2.2 fuel s hQs).1

/-! ## The witness brick 24 rejected -/

/-- The alias-maintaining loop: `while (…) copy 1 0`. With `0` and `1` live and
    distinct on entry, one body pass merges them, so brick 24's one-pass rule
    fails — but the fixpoint infers the invariant `[[0,1]]` and accepts. -/
def MaintainLoop : ALCmd := .loop (.var 9) (.copy 1 0)

/-- **The fixpoint infers the coarsening invariant** `[[1, 0]]` from the entry
    partition `[[1], [0]]` (two distinct live pointers). -/
theorem maintain_loopFix : loopFix 3 [[1], [0]] (.copy 1 0) = some [[1, 0]] := by decide

/-- **Brick 24's one-pass rule rejects it** — after one pass the entry classes are
    gone. -/
theorem brick24_rejects : alcheck [[1], [0]] MaintainLoop = none := by decide

/-- A concrete entry state: cells `0` and `1` allocated (addresses `0`, `1`), both
    live and in distinct classes. -/
def s0 : FLState := (fun k => if k = 1 then (1 : Int) else 0, 2, [])

/-- `[[1], [0]]` is a proper partition. -/
theorem disjP_10 : disjP [[1], [0]] := by
  intro z c₁ c₂ h1 h2 hz1 hz2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    first | rfl | (rw [List.mem_singleton] at hz1 hz2; exact absurd (hz1.symm.trans hz2) (by decide))

theorem ALInv_s0 : ALInv [[1], [0]] s0 := by
  refine ⟨?_, ?_, ?_, disjP_10⟩
  · intro z hz
    rcases liveP_cons.mp hz with h | h
    · rw [List.mem_singleton] at h; subst h; exact ⟨by simp [s0], by simp [s0], by simp [s0]⟩
    · rcases liveP_cons.mp h with h | h
      · rw [List.mem_singleton] at h; subst h; exact ⟨by simp [s0], by simp [s0], by simp [s0]⟩
      · rcases h with ⟨cls, hcls, _⟩; simp at hcls
  · intro x y hx hy hxy
    rcases liveP_cons.mp hx with hax | hax <;> rcases liveP_cons.mp hy with hay | hay
    · rw [List.mem_singleton] at hax hay; subst hax; subst hay; exact ⟨[1], by simp, by simp, by simp⟩
    · rw [List.mem_singleton] at hax
      rcases liveP_cons.mp hay with h | h
      · rw [List.mem_singleton] at h; subst hax; subst h; simp [s0] at hxy
      · rcases h with ⟨cls, hcls, _⟩; simp at hcls
    · rw [List.mem_singleton] at hay
      rcases liveP_cons.mp hax with h | h
      · rw [List.mem_singleton] at h; subst hay; subst h; simp [s0] at hxy
      · rcases h with ⟨cls, hcls, _⟩; simp at hcls
    · rcases liveP_cons.mp hax with h | h
      · rw [List.mem_singleton] at h; subst h
        rcases liveP_cons.mp hay with h' | h'
        · rw [List.mem_singleton] at h'; subst h'; exact ⟨[0], by simp, by simp, by simp⟩
        · rcases h' with ⟨cls, hcls, _⟩; simp at hcls
      · rcases h with ⟨cls, hcls, _⟩; simp at hcls
  · intro a ha; simp [s0] at ha

/-- **It is memory-safe** — the alias-maintaining loop brick 24 rejected runs
    without error at any fuel, certified by the fixpoint-inferred invariant. -/
theorem alias_maintain_loop_safe (fuel : Nat) :
    alexec fuel MaintainLoop s0 ≠ .err :=
  coarsen_loop_of_fix (e := .var 9) fuel disjP_10 maintain_loopFix ALInv_s0

end ConfTyping
