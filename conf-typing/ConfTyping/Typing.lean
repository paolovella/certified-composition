/-
  Layer 4: strata, evidence typing, the rejection, conformance, soundness
  (§§6–9), plus the §7.5 worked rejection and §7.3/7.4 policy/residual.

  Key structural commitment (checklist item 6 / Thm. 4): the discharge
  judgment for J(o,H) has *only* the Closure and Policy constructors. There
  is deliberately no constructor discharging J from attestation evidence —
  its absence IS "no coercion across strata".
-/
import ConfTyping.Pleak

namespace ConfTyping

/-! ## §6 Strata and evidence kinds -/

inductive Stratum where
  | closure | policy | conformance
deriving DecidableEq, Repr

inductive EvKind where
  | proof   -- Ev_proof  : an in-model derivation        (Σ_sem)
  | policy  -- Ev_policy : a release declaration         (Σ_sem)
  | attest  -- Ev_attest : a witness `deploy ≅ A`        (Σ_code)
deriving DecidableEq, Repr

/-- The evidence kind admissible at each stratum (§6 table). -/
def evidenceFor : Stratum → EvKind
  | .closure     => .proof
  | .policy      => .policy
  | .conformance => .attest

/-! ## §6 The discharge judgment  `𝒜 ⊢ J(o,H) ◁ S [E]`

Indexed by the (fixed) `J`. The obligation's content is `J c o P`; the
constructors carry the real evidence, so soundness has content. There is
no `conformance` constructor and no constructor consuming `Ev_attest`:
that absence is Theorem 4. -/

/-- A policy: the declared releases, as a relation `o φ` ("`φ` is declared
    for channel `o`"). A relation, not a function, so we need no `DecidableEq`
    on observations. -/
abbrev Policy := Obs → Release → Prop

/-- The empty policy declares nothing — the Closure-only regime. -/
def noPolicy : Policy := fun _ _ => False

inductive Discharge (J : JTy) (c : Cmd) (P : Partition)
    (𝒜 : List Obs) (Pi : Policy) : Obs → Stratum → Prop where
  | clo (o : Obs) (hmem : o ∈ 𝒜) (h : J c o P) :
      Discharge J c P 𝒜 Pi o .closure
  | pol (o : Obs) (hmem : o ∈ 𝒜) (φ : Release)
        (hdecl  : Pi o φ)                        -- the normative act (declaration)
        (hbound : ReleasesAtMost c o P φ) :       -- the PROOF obligation
      Discharge J c P 𝒜 Pi o .policy

/-! ## §8 Lemma 3 — the rejection is J-invariant

For *every* J, no obligation is dischargeable at the Conformance stratum.
The proof inspects the constructors; `J` never appears in it, so the
rejection is identical whether `J := J_NI` or `J := J_ε`. -/

theorem reject_Jinvariant (J : JTy) (c : Cmd) (P : Partition)
    (𝒜 : List Obs) (Pi : Policy) (o : Obs) :
    ¬ Discharge J c P 𝒜 Pi o .conformance := by
  intro h; cases h

/-! ## §6 The conformance relation and the transport gate (§6.1, §9) -/

/-- `deploy ≅ A` : 𝒪-observational equivalence. -/
def Conform (𝒪 : List Obs) (deploy A : Cmd) : Prop :=
  ∀ o ∈ 𝒪, ∀ σ, obs o deploy σ = obs o A σ

/-- Bit-identity ⟹ ≅. In this model (Sem-Det ∧ Sem-Closed) hold because
    `eval` is a pure total function, so identical artifacts conform. -/
theorem conform_refl (𝒪 : List Obs) (c : Cmd) : Conform 𝒪 c c :=
  fun _ _ _ => rfl

/-- The conformance gate transports a Closure result proven about the
    artifact `A` onto the running `deploy`. (§6.1: attestation relocates a
    J-claim; it never *establishes* one.) -/
theorem transport_JNI (𝒪 : List Obs) (deploy A : Cmd) (o : Obs) (P : Partition)
    (hmem : o ∈ 𝒪) (hconf : Conform 𝒪 deploy A) (hA : J_NI A o P) :
    J_NI deploy o P := by
  intro σ σ' hle
  rw [hconf o hmem σ, hconf o hmem σ', hA σ σ' hle]

/-- The gate transports the *Policy* half too: a proven release bound on the
    artifact `A` carries to `deploy`. Clean because `φ : Store → Val` is a
    function of the store, not the program — `hφ : φ σ = φ σ'` crosses the
    gate untouched; only the `obs` endpoints are rewritten. -/
theorem transport_releases (𝒪 : List Obs) (deploy A : Cmd) (o : Obs)
    (P : Partition) (φ : Release)
    (hmem : o ∈ 𝒪) (hconf : Conform 𝒪 deploy A)
    (hA : ReleasesAtMost A o P φ) : ReleasesAtMost deploy o P φ := by
  intro σ σ' hle hφ
  rw [hconf o hmem σ, hconf o hmem σ']
  exact hA σ σ' hle hφ

/-- **Theorem 4, sharpened (§6.1).** A *valid* attestation can coexist with
    a *false* obligation, so attestation cannot be evidence for J: deploy = A
    = P_leak conforms trivially, yet `J_NI(result,H)` is false. The two
    propositions are independent — disjoint signatures made visible. -/
theorem attest_is_not_J_evidence :
    Conform (OO Phigh) Pleak Pleak ∧ ¬ J_NI Pleak (resultO Phigh) Phigh :=
  ⟨conform_refl _ _, result_not_closable⟩

/-! ## §9 Boolean soundness -/

/-- `c` is confidential against 𝒜 (rel. 𝒪, under J, declassification Pi):
    each channel either leaks nothing, or leaks at most a *declared and
    proven* bound. The policy branch now carries the bound — no free pass. -/
def Confidential (J : JTy) (c : Cmd) (P : Partition) (𝒜 : List Obs) (Pi : Policy) : Prop :=
  ∀ o ∈ 𝒜, J c o P ∨ ∃ φ, Pi o φ ∧ ReleasesAtMost c o P φ

/-- If every generated obligation is well-typed-discharged (each `o ∈ 𝒜` at
    Closure with a real J-proof, or at Policy with a declared+bounded `φ`),
    then `c` is confidential with declassification exactly Pi. -/
theorem soundness (J : JTy) (c : Cmd) (P : Partition) (𝒜 : List Obs) (Pi : Policy)
    (htyped : ∀ o ∈ 𝒜, ∃ S, Discharge J c P 𝒜 Pi o S) :
    Confidential J c P 𝒜 Pi := by
  intro o ho
  obtain ⟨S, hd⟩ := htyped o ho
  cases hd with
  | clo _ h               => exact Or.inl h
  | pol _ φ hdecl hbound  => exact Or.inr ⟨φ, hdecl, hbound⟩

/-- **The conformance gate, full strength (§9).** Confidentiality proven about
    the artifact `A` — *both* the Closure channels and the Policy channels with
    their bounds — transports to the running `deploy`. Conformance is a global
    gate over the whole `Confidential` claim, never a discharge of any one
    obligation. -/
theorem confidential_transport (deploy A : Cmd) (P : Partition)
    (𝒜 : List Obs) (Pi : Policy)
    (hsub : 𝒜 ⊆ OO P) (hconf : Conform (OO P) deploy A)
    (hartifact : Confidential J_NI A P 𝒜 Pi) :
    Confidential J_NI deploy P 𝒜 Pi := by
  intro o ho
  rcases hartifact o ho with hJ | ⟨φ, hdecl, hbound⟩
  · exact Or.inl (transport_JNI (OO P) deploy A o P (hsub ho) hconf hJ)
  · exact Or.inr ⟨φ, hdecl, transport_releases (OO P) deploy A o P φ (hsub ho) hconf hbound⟩

/-- The old closure-only corollary, now revealed as the `Pi = noPolicy`
    special case of `confidential_transport`. -/
theorem soundness_deploy (deploy A : Cmd) (P : Partition) (𝒜 : List Obs)
    (hsub : 𝒜 ⊆ OO P)
    (hconf : Conform (OO P) deploy A)
    (hartifact : Confidential J_NI A P 𝒜 noPolicy) :
    ∀ o ∈ 𝒜, J_NI deploy o P := by
  intro o ho
  rcases confidential_transport deploy A P 𝒜 noPolicy hsub hconf hartifact o ho
    with hJ | ⟨φ, hdecl, _⟩
  · exact hJ
  · exact absurd hdecl (by simp [noPolicy])

/-! ## §7 The worked instance, end to end -/

/-- The P_leak policy: `result` is declared to release exactly the bit
    `φ_bit`, and nothing else is declared. A relation — no `DecidableEq` on
    observations needed. -/
def PiLeak : Policy := fun o φ => o = resultO Phigh ∧ φ = φ_bit

/-- §7.2 + §7.3: under `A_local` (no branch channel), P_leak is fully typed —
    `wall` at Closure, `result` at Policy with the *proven bound* `φ_bit`. -/
theorem pleak_typed_local :
    ∀ o ∈ A_local Phigh,
      ∃ S, Discharge J_NI Pleak Phigh (A_local Phigh) PiLeak o S := by
  intro o ho
  simp only [A_local, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact ⟨.policy, .pol _ (by simp [A_local]) φ_bit ⟨rfl, rfl⟩ result_releases_at_most_bit⟩
  · exact ⟨.closure, .clo _ (by simp [A_local]) wall_closure⟩

/-- Hence P_leak is confidential against the local adversary, declassifying
    exactly the bit `(b ≠ 0)` on `result` — a substantive guarantee now,
    not a fiat. -/
theorem pleak_confidential_local :
    Confidential J_NI Pleak Phigh (A_local Phigh) PiLeak :=
  soundness _ _ _ _ _ pleak_typed_local

theorem A_local_sub_OO : A_local Phigh ⊆ OO Phigh := by
  intro o ho
  simp only [A_local, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> simp [OO, List.mem_cons]

/-- **End to end across the gate.** The *running* P_leak (any `deploy` that
    conforms — here bit-identity via `conform_refl`) is confidential against
    the local adversary, leaking at most the bit `(b ≠ 0)` on `result`. This
    is the deploy-level guarantee the gate exists to deliver. -/
theorem pleak_confidential_deploy :
    Confidential J_NI Pleak Phigh (A_local Phigh) PiLeak :=
  confidential_transport Pleak Pleak Phigh (A_local Phigh) PiLeak
    A_local_sub_OO (conform_refl _ _) pleak_confidential_local

/-- §7.4 The residual. Under the physical adversary, with only `result`
    declared, `branch` is dischargeable at *no* stratum: it is not High-
    invariant (so not Closure) and not declared (so not Policy). -/
theorem branch_residual :
    ¬ ∃ S, Discharge J_NI Pleak Phigh (A_physical Phigh) PiLeak branchO S := by
  rintro ⟨S, hd⟩
  cases hd with
  | clo _ h  => exact branch_not_closable h
  | pol _ φ hdecl _ =>
      -- declaration forces branchO = resultO Phigh, but they differ
      have hbr : branchO = resultO Phigh := hdecl.1
      have := congrFun hbr ((fun _ => 0), 0, [])
      simp [branchO, resultO] at this

/-- §7.5 The rejection. Offering attestation for the *legitimately closable*
    `J(wall,H)` is ill-typed — an instance of the J-invariant Lemma 3. -/
theorem wall_rejection :
    ¬ Discharge J_NI Pleak Phigh (A_physical Phigh) PiLeak wall .conformance :=
  reject_Jinvariant _ _ _ _ _ _

end ConfTyping
