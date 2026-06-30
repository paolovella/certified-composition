/-
  The joint-generation module (framework doc §4, §8, Def. 5).

  Mathlib-free, all over `J_NI`. Proves per-channel ⟺ joint for the separable
  case, and — the point — *localizes* where it fails: completeness needs only
  the backward direction (A3, holds for every J); per-channel generation needs
  the forward direction, which IS separability. `J_ε` lacks exactly that one
  implication.
-/
import ConfTyping.Obs

namespace ConfTyping

/-! ## Target 1 — the join, with the seed pinned -/

/-- The "observe nothing" seed: a constant observation, trivially `J_NI`.
    Constancy is load-bearing — it makes the nil base case of
    `perchannel_to_joint` hold (LHS vacuous ⇒ RHS must be a true `J_NI`). -/
def seedObs : Obs := fun _ => .int 0

theorem seed_JNI (c : Cmd) (P : Partition) : J_NI c seedObs P :=
  fun _ _ _ => rfl

/-- `𝒜̂ = ⟨o⟩_{o∈𝒜}`. `joint [] = seedObs`, `joint (o::os) = tup o (joint os)`.
    `joint [o] = tup o seedObs` — observationally inert, never bites. -/
def joint (𝒜 : List Obs) : Obs := List.foldr tup seedObs 𝒜

/-- Singleton generation (framework §4): one obligation, on the join.
    Contrast `Gen 𝒜 = 𝒜`; the two coincide for `J_NI` exactly via
    `separability_equiv`, and diverge for `J_ε`. -/
def GenJoint (𝒜 : List Obs) : List Obs := [joint 𝒜]

/-! ## Target 2 — completeness relative to 𝒪 (Thm. 2) -/

/-- Discharging the single joint obligation covers every channel the adversary
    can derive (any post-processing). Uses **only A3**, so it holds for every
    A3-respecting `J` — `J_ε` included. This is *why* generation is joint. -/
theorem completeness_rel_O (c : Cmd) (𝒜 : List Obs) (P : Partition)
    (hjoint : J_NI c (joint 𝒜) P) :
    ∀ f : Val → Val, J_NI c (post f (joint 𝒜)) P :=
  fun f => JNI_postproc f c (joint 𝒜) P hjoint

/-! ## Target 3 — separability-equivalence, split into its two implications -/

def fstV : Val → Val | .pair x _ => x | v => v
def sndV : Val → Val | .pair _ y => y | v => v

theorem joint_cons_fst (a : Obs) (as : List Obs) :
    post fstV (joint (a :: as)) = a := by
  funext out; simp [joint, tup, post, fstV]

theorem joint_cons_snd (a : Obs) (as : List Obs) :
    post sndV (joint (a :: as)) = joint as := by
  funext out; simp [joint, tup, post, sndV]

/-- **BACKWARD:** joint bound ⇒ every per-channel bound. Each channel is a
    projection = post-processing of the join, so this is pure A3. Holds for
    `J_ε` too (data-processing inequality, same projections). -/
theorem joint_to_perchannel (c : Cmd) (P : Partition) :
    ∀ 𝒜, J_NI c (joint 𝒜) P → ∀ o ∈ 𝒜, J_NI c o P := by
  intro 𝒜; induction 𝒜 with
  | nil => intro _ o ho; simp at ho
  | cons a as ih =>
      intro hj o ho
      have ha    : J_NI c a P          := joint_cons_fst a as ▸ JNI_postproc fstV c _ P hj
      have htail : J_NI c (joint as) P := joint_cons_snd a as ▸ JNI_postproc sndV c _ P hj
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact ha
      · exact ih htail o ho'

/-- **FORWARD:** per-channel bounds ⇒ joint bound. Uses `JNI_separable` at each
    cons. *This* is the direction that legitimizes per-channel generation, and
    *this* is exactly what `J_ε` lacks — there is no `Jε_separable`. -/
theorem perchannel_to_joint (c : Cmd) (P : Partition) :
    ∀ 𝒜, (∀ o ∈ 𝒜, J_NI c o P) → J_NI c (joint 𝒜) P := by
  intro 𝒜; induction 𝒜 with
  | nil => intro _; exact seed_JNI c P
  | cons a as ih =>
      intro h
      exact JNI_separable c a (joint as) P (h a (by simp))
              (ih (fun o ho => h o (List.mem_cons_of_mem a ho)))

/-- The equivalence: for `J_NI`, per-channel generation and joint generation
    discharge the same obligations. -/
theorem separability_equiv (c : Cmd) (𝒜 : List Obs) (P : Partition) :
    (∀ o ∈ 𝒜, J_NI c o P) ↔ J_NI c (joint 𝒜) P :=
  ⟨perchannel_to_joint c P 𝒜, joint_to_perchannel c P 𝒜⟩

/-! ## Closing Thm. 2 — the factoring bridge (Prop. 1)

`completeness_rel_O` is the *engine* — "every post-processing of the join is
`J_NI`". Thm. 2 proper quantifies over every channel the adversary can
*derive*. The bridge is Prop. 1: every such channel factors through the join.
`joint_cons_fst/snd` already are "head/tail is a projection of the join"; this
packages them as the general inclusion. -/

/-- A channel is adversary-derivable from 𝒜 iff it factors through the join. -/
def Derivable (𝒜 : List Obs) (o : Obs) : Prop := ∃ f : Val → Val, o = post f (joint 𝒜)

/-- **Prop. 1.** Every primitive channel of 𝒜 factors through the join. -/
theorem mem_is_postproc (o : Obs) :
    ∀ 𝒜, o ∈ 𝒜 → Derivable 𝒜 o := by
  intro 𝒜; induction 𝒜 with
  | nil => intro h; simp at h
  | cons a as ih =>
      intro ho
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact ⟨fstV, (joint_cons_fst o as).symm⟩
      · obtain ⟨f, hf⟩ := ih ho'
        exact ⟨f ∘ sndV, by rw [hf, ← joint_cons_snd a as]; rfl⟩

/-- **Theorem 2 (completeness rel 𝒪), honest form.** Discharging the single
    joint obligation kills every adversary-*derivable* channel — primitives
    and all their post-processings, the quantifier now closed over real
    channels rather than over-shot to all functions. -/
theorem completeness_thm2 (c : Cmd) (𝒜 : List Obs) (P : Partition)
    (hjoint : J_NI c (joint 𝒜) P) :
    ∀ o, Derivable 𝒜 o → J_NI c o P := by
  rintro o ⟨f, rfl⟩
  exact completeness_rel_O c 𝒜 P hjoint f

/-- Per-channel coverage now flows *through* the honest Thm. 2 (primitives are
    derivable), exhibiting `joint_to_perchannel` as its special case. -/
theorem perchannel_covered (c : Cmd) (𝒜 : List Obs) (P : Partition)
    (hjoint : J_NI c (joint 𝒜) P) : ∀ o ∈ 𝒜, J_NI c o P :=
  fun o ho => completeness_thm2 c 𝒜 P hjoint o (mem_is_postproc o 𝒜 ho)

end ConfTyping
