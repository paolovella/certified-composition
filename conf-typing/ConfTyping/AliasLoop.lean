/-
  May-alias under loops — brick 24: the aliasing/free/loop intersection.

  Two disciplines never met. Brick 19 (`AliasSafe`) made `free` sound in the
  presence of pointer **copying** by tracking each pointer's *exact* address —
  precise only because straight-line allocation addresses are static. Brick 23
  (`FreeLoop`) made `free` sound under **loops**, but only via linearity, which
  *forbids copying* — its own header names the gap: "aliasing-under-loops needs
  may-alias." This brick closes it: a language with `copy` **and** `free`
  **and** unbounded loops, kept memory-safe by a *may-alias* analysis.

  Under loops the exact addresses of brick 19 are gone, so the checker abstracts
  the heap by a **partition of the live pointer variables into may-alias
  classes** — a `List (List Var)`, no addresses, no allocation counter (a
  counter would never be a loop fixed point). The soundness invariant is the
  may-alias over-approximation: *variables in different classes hold different
  addresses* (equivalently, equal address ⟹ same class). Then:

  * `alloc x` starts a fresh singleton class (a fresh cell aliases nothing);
  * `copy x y` puts `x` into `y`'s class (`x` may-aliases `y`);
  * `free x` drops `x`'s **whole class** — killing every alias at once, sound
    because any actual alias of `x` is in `x`'s class;
  * `access x` requires `x` to be in some class.

  The loop rule is one-pass, like brick 20/23: the body must **preserve every
  entry class** (a decidable fixed point), so a body may create aliases
  internally but must free them before the back-edge.

  * `alsafe` — soundness by fuel induction with the four-clause invariant; a
    checked program never hits a use-after-free / double-free / wild access, at
    any fuel;
  * `alias_free_loop_safe` — the witness brick 23 could not state: a loop that
    **allocates, copies (aliases), uses the alias, and frees** is accepted and
    never errors — copying under loops, made safe;
  * `alias_uaf_loop_rejected` — freeing then accessing through the alias is a
    use-after-free, rejected; `doublefree_aliasloop_rejected` — an invariant-
    pointer free is a cross-iteration double-free, rejected by the fixed point.
-/
import ConfTyping.FreeLoop

namespace ConfTyping

/-! ## The machine: a heap with copy and free, under loops -/

/-- Commands: allocate a fresh cell, **copy a pointer** (aliasing), access, free,
    sequence, loop. (`data`/`ite` are routine and omitted to keep the may-alias
    core in focus.) -/
inductive ALCmd where
  | alloc  : HLoc → ALCmd
  | copy   : HLoc → HLoc → ALCmd
  | access : HLoc → ALCmd
  | free   : HLoc → ALCmd
  | seq    : ALCmd → ALCmd → ALCmd
  | loop   : HLExpr → ALCmd → ALCmd

def alexec : Nat → ALCmd → FLState → FLRes
  | 0,   _,          _         => .to
  | _+1, .alloc x,   (σ, n, F) => .ok (flUpd σ x (n : Int), n + 1, F)
  | _+1, .copy x y,  (σ, n, F) => .ok (flUpd σ x (σ y), n, F)
  | _+1, .access x,  (σ, n, F) => if fLive (σ x) n F then .ok (σ, n, F) else .err
  | _+1, .free x,    (σ, n, F) => if fLive (σ x) n F then .ok (σ, n, σ x :: F) else .err
  | k+1, .seq c₁ c₂, s         => (alexec k c₁ s).bind (alexec k c₂)
  | k+1, .loop e c,  (σ, n, F) =>
      if hlval e σ ≠ 0 then (alexec k c (σ, n, F)).bind (alexec k (.loop e c))
      else .ok (σ, n, F)

/-! ## The may-alias partition and its checker -/

abbrev Part := List (List HLoc)

/-- `x` is a live pointer: it belongs to some class. -/
def liveP (P : Part) (z : HLoc) : Prop := ∃ cls ∈ P, z ∈ cls
/-- `x` and `y` are in a common class (may-alias). -/
def sameClassP (P : Part) (x y : HLoc) : Prop := ∃ cls ∈ P, x ∈ cls ∧ y ∈ cls
/-- Classes are separated: a shared member forces list equality. -/
def disjP (P : Part) : Prop :=
  ∀ z cls₁ cls₂, cls₁ ∈ P → cls₂ ∈ P → z ∈ cls₁ → z ∈ cls₂ → cls₁ = cls₂

/-- Remove `x` from every class. -/
def purge (x : HLoc) (P : Part) : Part := P.map (fun cls => cls.filter (fun z => decide (z ≠ x)))

/-- The partition after `copy x y`: purge `x`, then add it to `y`'s class. -/
def copyImg (x y : HLoc) (P : Part) : Part :=
  (purge x P).map (fun cls => if y ∈ cls then x :: cls else cls)

def alcheck : Part → ALCmd → Option Part
  | P, .alloc x   => some ([x] :: purge x P)
  | P, .copy x y  => some (copyImg x y P)
  | P, .access x  => if P.any (fun cls => decide (x ∈ cls)) then some P else none
  | P, .free x    =>
      if P.any (fun cls => decide (x ∈ cls)) then some (P.filter (fun cls => decide (x ∉ cls))) else none
  | P, .seq c₁ c₂ => (alcheck P c₁).bind (fun P₁ => alcheck P₁ c₂)
  | P, .loop _ c  =>
      match alcheck P c with
      | some P₁ => if P.all (fun cls => decide (cls ∈ P₁)) then some P else none
      | none    => none

/-! ## Membership lemmas -/

theorem mem_filter_ne {z x : HLoc} {cls : List HLoc} :
    z ∈ cls.filter (fun w => decide (w ≠ x)) ↔ z ∈ cls ∧ z ≠ x := by
  simp [List.mem_filter]

theorem liveP_purge {P : Part} {x z : HLoc} :
    liveP (purge x P) z ↔ z ≠ x ∧ liveP P z := by
  constructor
  · rintro ⟨cls, hcls, hz⟩
    simp only [purge, List.mem_map] at hcls
    obtain ⟨cls0, hcls0, rfl⟩ := hcls
    rw [mem_filter_ne] at hz
    exact ⟨hz.2, cls0, hcls0, hz.1⟩
  · rintro ⟨hzx, cls, hcls, hz⟩
    exact ⟨cls.filter (fun w => decide (w ≠ x)), by simp [purge, List.mem_map]; exact ⟨cls, hcls, rfl⟩,
      mem_filter_ne.mpr ⟨hz, hzx⟩⟩

theorem liveP_cons {c : List HLoc} {P : Part} {z : HLoc} :
    liveP (c :: P) z ↔ z ∈ c ∨ liveP P z := by
  simp only [liveP, List.mem_cons]
  constructor
  · rintro ⟨cls, (rfl | hcls), hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨cls, hcls, hz⟩
  · rintro (hz | ⟨cls, hcls, hz⟩)
    · exact ⟨c, Or.inl rfl, hz⟩
    · exact ⟨cls, Or.inr hcls, hz⟩

theorem liveP_any {P : Part} {x : HLoc} :
    (P.any (fun cls => decide (x ∈ cls)) = true) ↔ liveP P x := by
  simp only [List.any_eq_true, decide_eq_true_eq]; rfl

/-! ## Disjointness is preserved -/

theorem disjP_purge {P : Part} {x : HLoc} (h : disjP P) : disjP (purge x P) := by
  intro z cls₁ cls₂ h1 h2 hz1 hz2
  simp only [purge, List.mem_map] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  rw [mem_filter_ne] at hz1 hz2
  have : a = b := h z a b ha hb hz1.1 hz2.1
  rw [this]

theorem disjP_filter {P : Part} {p : List HLoc → Bool} (h : disjP P) :
    disjP (P.filter p) := by
  intro z cls₁ cls₂ h1 h2 hz1 hz2
  rw [List.mem_filter] at h1 h2
  exact h z cls₁ cls₂ h1.1 h2.1 hz1 hz2

/-! ## The soundness invariant -/

def ALInv (P : Part) : FLState → Prop
  | (σ, n, F) =>
      (∀ z, liveP P z → 0 ≤ σ z ∧ σ z < (n : Int) ∧ σ z ∉ F) ∧
      (∀ x y, liveP P x → liveP P y → σ x = σ y → sameClassP P x y) ∧
      (∀ a ∈ F, a < (n : Int)) ∧
      disjP P

/-- Weaken the invariant along class inclusion: if every class of `P` is a class
    of `Q` and `Q` is disjoint, then `ALInv Q` gives `ALInv P`. -/
theorem ALInv_of_sub {P Q : Part} {s : FLState}
    (hsub : ∀ cls ∈ P, cls ∈ Q) (hQ : ALInv Q s) : ALInv P s := by
  obtain ⟨σ, n, F⟩ := s
  obtain ⟨hli, hsc, hfr, hdj⟩ := hQ
  have hlift : ∀ z, liveP P z → liveP Q z := by
    rintro z ⟨cls, hcls, hz⟩; exact ⟨cls, hsub cls hcls, hz⟩
  refine ⟨fun z hz => hli z (hlift z hz), ?_, hfr, ?_⟩
  · intro x y hx hy hxy
    obtain ⟨cls, hclsQ, hxc, hyc⟩ := hsc x y (hlift x hx) (hlift y hy) hxy
    -- x lies in a P-class; disjointness in Q identifies it with cls
    obtain ⟨cx, hcxP, hxcx⟩ := hx
    have hcxcls : cx = cls := hdj x cx cls (hsub cx hcxP) hclsQ hxcx hxc
    subst hcxcls
    exact ⟨cx, hcxP, hxcx, hyc⟩
  · intro z cls₁ cls₂ h1 h2 hz1 hz2
    exact hdj z cls₁ cls₂ (hsub cls₁ h1) (hsub cls₂ h2) hz1 hz2

/-! ## Soundness -/

/-- **Memory safety with aliasing and free, under loops, by construction.** A
    checked program never hits a use-after-free, double-free, or wild access (at
    any fuel), and the may-alias invariant is preserved. -/
theorem alsafe :
    ∀ (fuel : Nat) (c : ALCmd) (P P' : Part) (s : FLState),
      alcheck P c = some P' → ALInv P s →
      alexec fuel c s ≠ .err ∧ (∀ s', alexec fuel c s = .ok s' → ALInv P' s') := by
  intro fuel
  induction fuel with
  | zero => intro c P P' s _ _; exact ⟨by simp [alexec], by intro s' h; simp [alexec] at h⟩
  | succ k ih =>
    intro c P P' s hchk hinv
    obtain ⟨σ, n, F⟩ := s
    obtain ⟨hli, hsc, hfr, hdj⟩ := hinv
    cases c with
    | alloc x =>
        simp only [alcheck, Option.some.injEq] at hchk; subst hchk
        refine ⟨by simp [alexec], ?_⟩
        intro s' hs; simp only [alexec, FLRes.ok.injEq] at hs; subst hs
        have hnF : (n : Int) ∉ F := fun hmem => absurd (hfr (n : Int) hmem) (by omega)
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro z hz
          rw [liveP_cons] at hz
          rcases hz with hz | hz
          · rw [List.mem_singleton] at hz; rw [hz]
            have hu : flUpd σ x (n : Int) x = (n : Int) := by simp [flUpd]
            rw [hu]; exact ⟨by omega, by omega, hnF⟩
          · rw [liveP_purge] at hz
            have hzx : z ≠ x := hz.1
            obtain ⟨hlz1, hlz2, hlz3⟩ := hli z hz.2
            have hu : flUpd σ x (n : Int) z = σ z := by simp [flUpd, hzx]
            rw [hu]; exact ⟨hlz1, by omega, hlz3⟩
        · intro a b ha hb hab
          rw [liveP_cons] at ha hb
          have key : ∀ w, (w ∈ [x] ∨ liveP (purge x P) w) →
              (w = x ∧ flUpd σ x (n : Int) w = (n : Int)) ∨
              (w ≠ x ∧ liveP P w ∧ flUpd σ x (n : Int) w = σ w ∧ σ w < (n : Int)) := by
            intro w hw
            rcases hw with hw | hw
            · rw [List.mem_singleton] at hw; subst hw
              exact Or.inl ⟨rfl, by simp [flUpd]⟩
            · rw [liveP_purge] at hw
              have hwx := hw.1
              exact Or.inr ⟨hwx, hw.2, by simp [flUpd, hwx], (hli w hw.2).2.1⟩
          rcases key a ha with ⟨hae1, hae⟩ | ⟨hax, halive, hae, halt⟩
          · rcases key b hb with ⟨hbe1, hbe⟩ | ⟨hbx, hblive, hbe, hblt⟩
            · exact ⟨[x], by simp, by rw [hae1]; simp, by rw [hbe1]; simp⟩
            · rw [hae, hbe] at hab; omega
          · rcases key b hb with ⟨hbe1, hbe⟩ | ⟨hbx, hblive, hbe, hblt⟩
            · rw [hae, hbe] at hab; omega
            · rw [hae, hbe] at hab
              obtain ⟨cls, hcls, hac, hbc⟩ := hsc a b halive hblive hab
              refine ⟨cls.filter (fun z => decide (z ≠ x)), ?_, ?_, ?_⟩
              · simp only [List.mem_cons, purge, List.mem_map]
                exact Or.inr ⟨cls, hcls, rfl⟩
              · exact mem_filter_ne.mpr ⟨hac, hax⟩
              · exact mem_filter_ne.mpr ⟨hbc, hbx⟩
        · intro a ha; have := hfr a ha; omega
        · intro z cls₁ cls₂ h1 h2 hz1 hz2
          rw [List.mem_cons] at h1 h2
          have hx_not : ∀ c, c ∈ purge x P → x ∉ c := by
            intro c hc hxc
            simp only [purge, List.mem_map] at hc
            obtain ⟨c0, _, rfl⟩ := hc
            exact (mem_filter_ne.mp hxc).2 rfl
          rcases h1 with rfl | h1p
          · rcases h2 with rfl | h2p
            · rfl
            · rw [List.mem_singleton] at hz1; subst hz1
              exact absurd hz2 (hx_not cls₂ h2p)
          · rcases h2 with rfl | h2p
            · rw [List.mem_singleton] at hz2; subst hz2
              exact absurd hz1 (hx_not cls₁ h1p)
            · exact disjP_purge hdj z cls₁ cls₂ h1p h2p hz1 hz2
    | copy x y =>
        simp only [alcheck, Option.some.injEq] at hchk; subst hchk
        refine ⟨by simp [alexec], ?_⟩
        intro s' hs; simp only [alexec, FLRes.ok.injEq] at hs; subst hs
        -- membership in the mapped partition
        have memQ : ∀ z, liveP (copyImg x y P) z ↔
            (z = x ∧ liveP (purge x P) y) ∨ liveP (purge x P) z := by
          intro z
          simp only [copyImg, liveP, List.mem_map]
          constructor
          · rintro ⟨cls, ⟨cls0, hcls0, rfl⟩, hz⟩
            by_cases hy : y ∈ cls0
            · simp only [if_pos hy, List.mem_cons] at hz
              rcases hz with rfl | hz
              · exact Or.inl ⟨rfl, cls0, hcls0, hy⟩
              · exact Or.inr ⟨cls0, hcls0, hz⟩
            · simp only [if_neg hy] at hz
              exact Or.inr ⟨cls0, hcls0, hz⟩
          · rintro (⟨rfl, cls0, hcls0, hy⟩ | ⟨cls0, hcls0, hz⟩)
            · exact ⟨_, ⟨cls0, hcls0, rfl⟩, by simp [hy]⟩
            · by_cases hy : y ∈ cls0
              · exact ⟨_, ⟨cls0, hcls0, rfl⟩, by simp [if_pos hy, hz]⟩
              · exact ⟨_, ⟨cls0, hcls0, rfl⟩, by simp [if_neg hy, hz]⟩
        -- helper: address bounds for live-in-purge vars
        have hpb : ∀ z, liveP (purge x P) z → 0 ≤ σ z ∧ σ z < (n : Int) ∧ σ z ∉ F := by
          intro z hz; exact hli z ((liveP_purge.mp hz).2)
        -- x ∉ any purge class
        have hxnp : ∀ c ∈ purge x P, x ∉ c := by
          intro c hc; simp only [purge, List.mem_map] at hc; obtain ⟨c0, _, rfl⟩ := hc
          intro hxc; exact (mem_filter_ne.mp hxc).2 rfl
        -- representative φ: a live-Q var z has a purge-live rep w with σ' z = σ w, and z
        -- lands in the mapped image of any purge-class containing w
        have rep : ∀ z, liveP (copyImg x y P) z → ∃ w, liveP (purge x P) w ∧ flUpd σ x (σ y) z = σ w ∧
            (∀ cls, w ∈ cls → z ∈ (if y ∈ cls then x :: cls else cls)) := by
          intro z hz
          rw [memQ] at hz
          rcases hz with ⟨rfl, hylive⟩ | hz
          · refine ⟨y, hylive, by simp [flUpd], ?_⟩
            intro cls hy; rw [if_pos hy]; simp
          · have hzx : z ≠ x := (liveP_purge.mp hz).1
            refine ⟨z, hz, by simp [flUpd, hzx], ?_⟩
            intro cls hzc
            by_cases hy : y ∈ cls
            · rw [if_pos hy]; exact List.mem_cons_of_mem x hzc
            · rw [if_neg hy]; exact hzc
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro z hz
          rw [memQ] at hz
          rcases hz with ⟨rfl, hylive⟩ | hz
          · simp only [flUpd, if_pos rfl]; exact hpb y hylive
          · have hzx : z ≠ x := (liveP_purge.mp hz).1
            simp only [flUpd, if_neg hzx]; exact hpb z hz
        · intro a b ha hb hab
          obtain ⟨wa, hwa, hva, hga⟩ := rep a ha
          obtain ⟨wb, hwb, hvb, hgb⟩ := rep b hb
          rw [hva, hvb] at hab
          have hscP : sameClassP P wa wb :=
            hsc wa wb ((liveP_purge.mp hwa).2) ((liveP_purge.mp hwb).2) hab
          obtain ⟨cls0, hcls0, hwac, hwbc⟩ := hscP
          -- the shared class, purged, lives in purge x P
          have hclsP : cls0.filter (fun z => decide (z ≠ x)) ∈ purge x P := by
            simp only [purge, List.mem_map]; exact ⟨cls0, hcls0, rfl⟩
          have hwacP : wa ∈ cls0.filter (fun z => decide (z ≠ x)) :=
            mem_filter_ne.mpr ⟨hwac, (liveP_purge.mp hwa).1⟩
          have hwbcP : wb ∈ cls0.filter (fun z => decide (z ≠ x)) :=
            mem_filter_ne.mpr ⟨hwbc, (liveP_purge.mp hwb).1⟩
          refine ⟨_, ?_, hga _ hwacP, hgb _ hwbcP⟩
          simp only [copyImg, List.mem_map]
          exact ⟨cls0.filter (fun z => decide (z ≠ x)), hclsP, rfl⟩
        · intro a ha; have := hfr a ha; omega
        · intro z cls₁' cls₂' h1 h2 hz1 hz2
          simp only [copyImg, List.mem_map] at h1 h2
          obtain ⟨cls₁, hcls₁, rfl⟩ := h1
          obtain ⟨cls₂, hcls₂, rfl⟩ := h2
          by_cases hzx : z = x
          · subst hzx
            have hy1 : y ∈ cls₁ := by
              by_cases hy : y ∈ cls₁
              · exact hy
              · rw [if_neg hy] at hz1; exact absurd hz1 (hxnp cls₁ hcls₁)
            have hy2 : y ∈ cls₂ := by
              by_cases hy : y ∈ cls₂
              · exact hy
              · rw [if_neg hy] at hz2; exact absurd hz2 (hxnp cls₂ hcls₂)
            rw [disjP_purge hdj y cls₁ cls₂ hcls₁ hcls₂ hy1 hy2]
          · have hz1' : z ∈ cls₁ := by
              by_cases hy : y ∈ cls₁
              · rw [if_pos hy, List.mem_cons] at hz1; exact hz1.resolve_left hzx
              · rw [if_neg hy] at hz1; exact hz1
            have hz2' : z ∈ cls₂ := by
              by_cases hy : y ∈ cls₂
              · rw [if_pos hy, List.mem_cons] at hz2; exact hz2.resolve_left hzx
              · rw [if_neg hy] at hz2; exact hz2
            rw [disjP_purge hdj z cls₁ cls₂ hcls₁ hcls₂ hz1' hz2']
    | access x =>
        simp only [alcheck] at hchk
        by_cases hxP : (P.any (fun cls => decide (x ∈ cls)) = true)
        · rw [if_pos hxP, Option.some.injEq] at hchk; subst hchk
          have hlive : liveP P x := liveP_any.mp hxP
          obtain ⟨cls, hcls, hxc⟩ := hlive
          have hlv := hli x ⟨cls, hcls, hxc⟩
          have hfl : fLive (σ x) n F = true := fLive_true hlv.1 hlv.2.1 hlv.2.2
          refine ⟨by simp [alexec, hfl], ?_⟩
          intro s' hs; simp only [alexec, hfl, if_true, FLRes.ok.injEq] at hs; subst hs
          exact ⟨hli, hsc, hfr, hdj⟩
        · rw [if_neg hxP] at hchk; simp at hchk
    | free x =>
        simp only [alcheck] at hchk
        by_cases hxP : (P.any (fun cls => decide (x ∈ cls)) = true)
        · rw [if_pos hxP, Option.some.injEq] at hchk; subst hchk
          have hlive : liveP P x := liveP_any.mp hxP
          obtain ⟨clsx, hclsx, hxcx⟩ := hlive
          have hlv := hli x ⟨clsx, hclsx, hxcx⟩
          have hfl : fLive (σ x) n F = true := fLive_true hlv.1 hlv.2.1 hlv.2.2
          refine ⟨by simp [alexec, hfl], ?_⟩
          intro s' hs; simp only [alexec, hfl, if_true, FLRes.ok.injEq] at hs; subst hs
          have hsubF : ∀ z, liveP (P.filter (fun cls => decide (x ∉ cls))) z → liveP P z := by
            rintro z ⟨cls, hcls, hz⟩; rw [List.mem_filter] at hcls; exact ⟨cls, hcls.1, hz⟩
          refine ⟨?_, ?_, ?_, disjP_filter hdj⟩
          · intro z hz
            have hzL : liveP P z := hsubF z hz
            obtain ⟨cls, hcls, hzc⟩ := hz
            rw [List.mem_filter] at hcls
            have hxnc : x ∉ cls := by have := hcls.2; simpa using of_decide_eq_true this
            have hlvz := hli z hzL
            refine ⟨hlvz.1, hlvz.2.1, ?_⟩
            intro hmem
            rcases List.mem_cons.mp hmem with h | h
            · -- σ z = σ x ⟹ z, x same class ⟹ x ∈ cls, contradiction
              have hsame := hsc z x hzL ⟨clsx, hclsx, hxcx⟩ h
              obtain ⟨cc, hcc, hzcc, hxcc⟩ := hsame
              have : cls = cc := hdj z cls cc hcls.1 hcc hzc hzcc
              rw [this] at hxnc; exact hxnc hxcc
            · exact hlvz.2.2 h
          · intro a b ha hb hab
            have hsame := hsc a b (hsubF a ha) (hsubF b hb) hab
            obtain ⟨cc, hcc, hacc, hbcc⟩ := hsame
            obtain ⟨ca, hca, hac⟩ := ha
            rw [List.mem_filter] at hca
            have hxnca : x ∉ ca := by have := hca.2; simpa using of_decide_eq_true this
            have hcaeq : ca = cc := hdj a ca cc hca.1 hcc hac hacc
            refine ⟨cc, ?_, hacc, hbcc⟩
            rw [List.mem_filter]
            refine ⟨hcc, ?_⟩
            rw [← hcaeq]; simpa using hxnca
          · intro a ha
            rcases List.mem_cons.mp ha with h | h
            · rw [h]; exact hlv.2.1
            · exact hfr a h
        · rw [if_neg hxP] at hchk; simp at hchk
    | seq c₁ c₂ =>
        simp only [alcheck, Option.bind_eq_bind] at hchk
        cases hP₁ : alcheck P c₁ with
        | none => rw [hP₁] at hchk; simp at hchk
        | some P₁ =>
            rw [hP₁, Option.bind_some] at hchk
            obtain ⟨e₁, o₁⟩ := ih c₁ P P₁ (σ, n, F) hP₁ ⟨hli, hsc, hfr, hdj⟩
            refine ⟨flbind_ne_err e₁ (fun s₁ hs₁ => (ih c₂ P₁ P' s₁ hchk (o₁ s₁ hs₁)).1), ?_⟩
            intro s' hs
            obtain ⟨s₁, ho₁, ho₂⟩ := flbind_ok hs
            exact (ih c₂ P₁ P' s₁ hchk (o₁ s₁ ho₁)).2 s' ho₂
    | loop e c =>
        cases hP₁ : alcheck P c with
        | none => simp [alcheck, hP₁] at hchk
        | some P₁ =>
            simp only [alcheck, hP₁] at hchk
            by_cases hsub : (P.all (fun cls => decide (cls ∈ P₁)) = true)
            · rw [if_pos hsub, Option.some.injEq] at hchk; subst hchk
              have hsubcls : ∀ cls ∈ P, cls ∈ P₁ := by
                intro cls hcls
                have := (List.all_eq_true.mp hsub) cls hcls
                simpa using of_decide_eq_true this
              have hloopchk : alcheck P (.loop e c) = some P := by
                simp only [alcheck, hP₁, hsub, if_true]
              have bodyStep : ∀ s₁, alexec k c (σ, n, F) = .ok s₁ → ALInv P s₁ := by
                intro s₁ hs₁
                exact ALInv_of_sub hsubcls ((ih c P P₁ (σ, n, F) hP₁ ⟨hli, hsc, hfr, hdj⟩).2 s₁ hs₁)
              refine ⟨?_, ?_⟩
              · simp only [alexec]; split
                · refine flbind_ne_err (ih c P P₁ (σ, n, F) hP₁ ⟨hli, hsc, hfr, hdj⟩).1 ?_
                  intro s₁ hs₁
                  exact (ih (.loop e c) P P s₁ hloopchk (bodyStep s₁ hs₁)).1
                · simp [FLRes.bind]
              · intro s' hs; simp only [alexec] at hs; split at hs
                · obtain ⟨s₁, ho₁, ho₂⟩ := flbind_ok hs
                  exact (ih (.loop e c) P P s₁ hloopchk (bodyStep s₁ ho₁)).2 s' ho₂
                · rw [FLRes.ok.injEq] at hs; subst hs; exact ⟨hli, hsc, hfr, hdj⟩
            · rw [if_neg hsub] at hchk; simp at hchk

/-- **Certified may-alias-safe under loops by `decide`.** -/
theorem alsafe_of_check {c : ALCmd} {P' : Part} (fuel : Nat) (σ₀ : HLoc → Int)
    (h : alcheck [] c = some P') : alexec fuel c (σ₀, 0, []) ≠ .err := by
  have hinv : ALInv [] (σ₀, 0, []) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro z ⟨cls, hcls, _⟩; cases hcls
    · rintro x y ⟨cls, hcls, _⟩; cases hcls
    · intro a ha; cases ha
    · intro z cls₁ cls₂ h1 _ _ _; cases h1
  exact (alsafe fuel c [] P' (σ₀, 0, []) h hinv).1

/-! ## Witnesses -/

/-- The witness brick 23 could not state: a loop that **allocates** a fresh cell,
    **copies** the pointer (aliasing), **uses the alias**, and **frees** — all
    under an unbounded loop. Linearity forbade the copy; the may-alias partition
    accepts it, and it is safe. -/
def AliasFreeLoop : ALCmd :=
  .loop (.var 9) (.seq (.alloc 0) (.seq (.copy 1 0) (.seq (.access 1) (.free 0))))

theorem aliasfree_checks : (alcheck [] AliasFreeLoop).isSome = true := by decide

theorem alias_free_loop_safe (fuel : Nat) (σ₀ : HLoc → Int) :
    alexec fuel AliasFreeLoop (σ₀, 0, []) ≠ .err := by
  obtain ⟨P', h⟩ := Option.isSome_iff_exists.mp aliasfree_checks
  exact alsafe_of_check fuel σ₀ h

/-- Use-after-free through an alias, inside a loop: allocate, copy, **free**, then
    access the alias. It errors and is rejected — the free killed the whole class,
    so the alias `1` is no longer live. -/
def AliasUAFLoop : ALCmd :=
  .loop (.var 9) (.seq (.alloc 0) (.seq (.copy 1 0) (.seq (.free 0) (.access 1))))

theorem alias_uaf_loop_rejected : alcheck [] AliasUAFLoop = none := by decide

/-- Double-free across iterations: with `0` in the loop invariant, freeing it each
    iteration double-frees. The fixed-point rule rejects it — `free` drops `0`'s
    class, so the body cannot preserve the invariant. -/
def DoubleFreeLoopA : ALCmd := .loop (.var 9) (.free 0)

theorem doublefree_aliasloop_rejected : alcheck [[0]] DoubleFreeLoopA = none := by decide

end ConfTyping
