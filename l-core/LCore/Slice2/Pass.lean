/-
  VS-2 step 6: the obligations over loops, by induction over frames at every fuel.

  `behind`: the machine at fuel `m` is never ahead of the source at fuel `m`. `det_run`: two machines, in different environments, whose source runs show the same at fuel `m`, show the same at fuel `m`.
  `ahead`: what the source finishes, the machine finishes. Nothing here is about a certificate. A jump belongs to no source step, so it is charged to the step that made it pending.
-/
import LCore.Slice2.Chunk

namespace LCore.Slice2.Lower

open Slice (W64 Expr Store upd eval retEv cap tick tick_ext Ext sec0 inp)
open Slice.Rv
open Slice.Slots (SExpr evalS updS encBytes wordAt)
open Slice.Lower (Good fetchI fetchI_parts fetchI_code fetchI_bound At Micro tickM fuelB playApp playApp_append Exec Exec.nil Exec.trans Exec.step Exec.stepAt
  addImm_val slotAddr Inv mE genE sE okE genE_length genE_good genE_exec mE_length wordsMax exitF entry_exec exit_exec code_length Inv.mono_mem play_view get_zero
  play_ev play_cost play_fin play_out)
open Slots (SCmd SProg SFrame pushS runS slotLang arrBase runS_ext)

/-! ## The source, one step at a time -/

/-- What a command's step leaks in the source. -/
def lkOf (c : SCmd) (t : Slice.Slots.Slots) : List Lk :=
  match c with
  | .ite e _ _ | .loop e _ => if (evalS e t).val ≠ 0 then [.branch true] else [.branch false]
  | .load _ e | .store e _ => [addrLk (idx (evalS e t))]
  | _ => []

/-- The source's frames after a command. -/
def nextS (c : SCmd) (q : List Nat) (ks : List SFrame) (t : Slice.Slots.Slots) : List SFrame :=
  match c with
  | .ite e a b => if (evalS e t).val ≠ 0 then pushS a (q ++ [0]) ks else pushS b (q ++ [1]) ks
  | .loop e b => if (evalS e t).val ≠ 0 then pushS b (q ++ [0]) ((.loop e b, q) :: ks) else ks
  | _ => ks

theorem src_step (ret : SExpr) {c : SCmd} (hc : ∀ a b, c ≠ .seq a b) (n : Nat) (q : List Nat) (ks : List SFrame) (t : Slice.Slots.Slots) :
    runS ret (n + 1) ((c, q) :: ks) t = tick (lkOf c t) q (runS ret n (nextS c q ks t) (nextT c t)) := by
  cases c with
  | seq a b => exact absurd rfl (hc a b)
  | skip | set _ _ | load _ _ | store _ _ => rfl
  | ite e a b =>
    by_cases hg : (evalS e t).val ≠ 0
    · simp [runS, lkOf, nextS, nextT, hg]
    · simp [runS, lkOf, nextS, nextT, hg]
  | loop e b =>
    by_cases hg : (evalS e t).val ≠ 0
    · simp [runS, lkOf, nextS, nextT, hg]
    · simp [runS, lkOf, nextS, nextT, hg]

/-- Source frames and target frames: the same commands, with the target's jumps in between. -/
inductive Corr : List SFrame → List TF → Prop where
  | nil : Corr [] []
  | cmd {ks : List SFrame} {k : List TF} {c : SCmd} {q : List Nat} {pc : Nat} : Corr ks k → Corr ((c, q) :: ks) (.cmd c pc :: k)
  | jmp {ks : List SFrame} {k : List TF} {p r : Nat} : Corr ks k → Corr ks (.jmp p r :: k)

theorem Corr.push : ∀ (c : SCmd) (q : List Nat) (pc : Nat) {ks : List SFrame} {k : List TF}, Corr ks k → Corr (pushS c q ks) (pushT c pc k)
  | .seq a b, q, pc, _, _, h => Corr.push a _ _ (Corr.push b _ _ h)
  | .skip, _, _, _, _, h | .set _ _, _, _, _, _, h | .ite _ _ _, _, _, _, _, h | .loop _ _, _, _, _, _, h
  | .load _ _, _, _, _, _, h | .store _ _, _, _, _, _, h => Corr.cmd h

theorem Corr.next {ks : List SFrame} {k : List TF} (h : Corr ks k) (c : SCmd) (q : List Nat) (pc : Nat) (t : Slice.Slots.Slots) :
    Corr (nextS c q ks t) (nextK c pc k t) := by
  cases c with
  | ite e a b =>
    simp only [nextS, nextK]
    split
    · exact Corr.push _ _ _ (Corr.jmp h)
    · exact Corr.push _ _ _ h
  | loop e b =>
    simp only [nextS, nextK]
    split
    · exact Corr.push _ _ _ (Corr.jmp (Corr.cmd h))
    · exact h
  | _ => exact h

/-! ## Played lists -/

theorem play_short {c : List Micro} {F : Nat → Beh} : ∀ {m : Nat}, m < c.length →
    (playApp c F m).out = .fuel ∧ (playApp c F m).ev = [] ∧ (playApp c F m).cost ≤ m := by
  induction c with
  | nil => intro m h; simp at h
  | cons x c ih =>
    intro m h
    cases m with
    | zero => exact ⟨rfl, rfl, Nat.le_refl _⟩
    | succ n =>
      obtain ⟨h1, h2, h3⟩ := ih (m := n) (by simpa using h)
      refine ⟨h1, h2, ?_⟩
      show 1 + (playApp c F n).cost ≤ n + 1
      omega

theorem play_long {c : List Micro} {F : Nat → Beh} (a : Nat) :
    (playApp c F (c.length + a)).out = (F a).out ∧ (playApp c F (c.length + a)).ev = (F a).ev ∧
      (playApp c F (c.length + a)).cost = c.length + (F a).cost := by
  induction c with
  | nil => simp [playApp]
  | cons x c ih =>
    have e : (x :: c).length + a = (c.length + a) + 1 := by simp; omega
    rw [e]
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h1, h2, ?_⟩
    show 1 + (playApp c F (c.length + a)).cost = _
    simp only [List.length_cons]
    omega

theorem tick_view {x : Micro} {r r' : Beh} {f : Observer} (h : r.view f = r'.view f) : (tickM x r).view f = (tickM x r').view f := by
  have he := congrArg Beh.ev h
  have hl := congrArg Beh.lk h
  have hc := congrArg Beh.cost h
  have ho := congrArg Beh.out h
  simp only [Beh.view] at he hl hc ho
  simp only [tickM, Beh.view, he, hl, hc, ho]

/-- Two played lists show the same, if what follows them does, at the fuel left. -/
theorem play_congr {f : Observer} {F G : Nat → Beh} : ∀ (c : List Micro) (m : Nat), (∀ a, a + c.length ≤ m → (F a).view f = (G a).view f) →
    (playApp c F m).view f = (playApp c G m).view f
  | [], m, h => h m (by simp)
  | _ :: _, 0, _ => rfl
  | x :: c, n + 1, h => tick_view (play_congr c n (fun a ha => h a (by simp; omega)))

/-! ## Sizes -/

/-- **What one source step can cost on the machine**: the command's own chunk, plus the jump it may push. Not the whole command: a loop's step
    runs its guard and a branch, and its body is charged to the body's own steps (BOUND-01 step 5a). -/
def stepC : SCmd → Nat
  | .skip => 1
  | .set _ e => sE e + 1
  | .seq _ _ => 0
  | .ite e _ _ | .loop e _ => sE e + 2
  | .load _ e => sE e + 7
  | .store e v => sE e + 5 + sE v + 1

/-- The largest `stepC` over every frame a command can push, its branches and loop body included. -/
def stepMax : SCmd → Nat
  | .seq a b => max (stepMax a) (stepMax b)
  | .ite e a b => max (sE e + 2) (max (stepMax a) (stepMax b))
  | .loop e b => max (sE e + 2) (stepMax b)
  -- Every other constructor is listed, not caught by `| c => _`: a match with overlapping patterns compiles through `propext`, and this
  -- definition is axiom-free without it (the manifest gate caught it, PR #21).
  | .skip => stepC .skip
  | .set n e => stepC (.set n e)
  | .load x e => stepC (.load x e)
  | .store e v => stepC (.store e v)

theorem stepC_le : ∀ (c : SCmd), stepC c ≤ stepMax c
  | .seq _ _ => Nat.zero_le _
  | .ite _ _ _ | .loop _ _ => Nat.le_max_left _ _
  | .skip | .set _ _ | .load _ _ | .store _ _ => Nat.le_refl _

def FS (L : Nat) : List TF → Prop
  | [] => True
  | .cmd c _ :: k => stepMax c ≤ L ∧ FS L k
  | .jmp _ _ :: k => FS L k

def jc : List TF → Nat
  | [] => 0
  | .cmd _ _ :: k => jc k
  | .jmp _ _ :: k => 1 + jc k

theorem push_fs {L : Nat} : ∀ (c : SCmd) (pc : Nat) (k : List TF), stepMax c ≤ L → FS L k → FS L (pushT c pc k)
  | .seq a b, pc, k, h, hk => by
    simp only [stepMax] at h
    exact push_fs a _ _ (by omega) (push_fs b _ _ (by omega) hk)
  | .skip, _, _, h, hk | .set _ _, _, _, h, hk | .ite _ _ _, _, _, h, hk | .loop _ _, _, _, h, hk
  | .load _ _, _, _, h, hk | .store _ _, _, _, h, hk => ⟨h, hk⟩

theorem jc_push : ∀ (c : SCmd) (pc : Nat) (k : List TF), jc (pushT c pc k) = jc k
  | .seq a b, pc, k => by simp only [pushT, jc_push a, jc_push b]
  | .skip, _, _ | .set _ _, _, _ | .ite _ _ _, _, _ | .loop _ _, _, _ | .load _ _, _, _ | .store _ _, _, _ => rfl

theorem next_fs {L : Nat} {c : SCmd} {pc : Nat} {k : List TF} (t : Slice.Slots.Slots) (hc : stepMax c ≤ L) (hk : FS L k) : FS L (nextK c pc k t) := by
  cases c with
  | ite e a b =>
    simp only [stepMax] at hc
    simp only [nextK]
    split
    · exact push_fs _ _ _ (by omega) hk
    · exact push_fs _ _ _ (by omega) hk
  | loop e b =>
    have hc0 := hc
    simp only [stepMax] at hc
    simp only [nextK]
    split
    · exact push_fs _ _ _ (by omega) ⟨hc0, hk⟩
    · exact hk
  | _ => exact hk

theorem mIdx_length (e : SExpr) (pc : Nat) : (mIdx e pc).length = sE e + 5 := by
  simp [mIdx, mE_length]

theorem chunk_length {c : SCmd} (pc : Nat) (k : List TF) (t : Slice.Slots.Slots) (hs : ∀ a b, c ≠ .seq a b) :
    0 < (chunkC c pc t).length ∧ (chunkC c pc t).length + jc (nextK c pc k t) ≤ stepC c + jc k := by
  cases c with
  | seq a b => exact absurd rfl (hs a b)
  | skip => simp [chunkC, nextK, stepC]
  | set n e => simp [chunkC, nextK, stepC, mE_length]
  | ite e a b =>
    simp only [chunkC, nextK, stepC, List.length_append, mE_length, List.length_cons, List.length_nil]
    constructor
    · omega
    · split
      · rw [jc_push]; simp only [jc]; omega
      · rw [jc_push]; omega
  | loop e b =>
    simp only [chunkC, nextK, stepC, List.length_append, mE_length, List.length_cons, List.length_nil]
    constructor
    · omega
    · split
      · rw [jc_push]; simp only [jc]; omega
      · omega
  | load x e => simp [chunkC, nextK, stepC, mIdx_length]
  | store e v => simp [chunkC, nextK, stepC, mIdx_length, mE_length]; omega

/-! ## The end of a run -/

def tailM (ret : SExpr) (r : Nat) : List Micro :=
  mE ret r ++ [(r + 4 * sE ret, []), (r + 4 * sE ret + 4, [])]

/-- The result's code is at `r`. -/
structure Tail (C : List Byte) (ret : SExpr) (r : Nat) : Prop where
  ok : okE ret 0 = true
  res : At C r (genE ret 0)
  x0 : fetchI C (r + 4 * sE ret) = some (.add 10 8 0)
  x1 : fetchI C (r + 4 * sE ret + 4) = some (.addi 17 0 (Int.ofNat 93))
  x2 : fetchI C (r + 4 * sE ret + 8) = some .ecall

/-- **The end of a run**, from the slots alone. -/
theorem tail_exec {C : List Byte} {en : Env} {ret : SExpr} {r : Nat} (ht : Tail C ret r) {m : Mach} {t : Slice.Slots.Slots}
    (hp : m.pc = r) (hinv : Inv m t) (n : Nat) :
    Slice.Rv.run C en n m = playApp (tailM ret r) (exitF (evalS ret t) (r + 4 * sE ret + 8)) n := by
  obtain ⟨m₃, e₃, p₃, _, v₃, _⟩ := genE_exec (en := en) ret 0 m t ht.ok hinv (by rw [hp]; exact ht.res)
  rw [hp] at e₃ p₃
  obtain ⟨m₅, e₅, hexit⟩ := exit_exec (e := en) p₃ ht.x0 ht.x1 ht.x2
  have hval : m₃.get 8 = evalS ret t := v₃
  rw [hval] at hexit
  have hE : Exec C en (tailM ret r) m m₅ := e₃.trans e₅
  rw [hE n]
  have : (fun k => Slice.Rv.run C en k m₅) = exitF (evalS ret t) (r + 4 * sE ret + 8) := funext hexit
  rw [this]

theorem src_done (ret : SExpr) (n : Nat) (t : Slice.Slots.Slots) :
    (runS ret n [] t).out = .done ∧ (runS ret n [] t).ev = [Slice.retEv (evalS ret t)] := by
  cases n <;> exact ⟨rfl, rfl⟩

/-! ## The machine is never ahead of the source -/

/-- **`behind`**: at the same fuel, the machine's events are a prefix of the source's, its cost is bounded, and what it finishes the source has finished, alike. -/
theorem behind {C : List Byte} {en : Env} {ret : SExpr} {r : Nat} (hC : C.length ≤ 3000) (ht : Tail C ret r) (L : Nat) :
    ∀ (m : Nat) (k : List TF) (ks : List SFrame) (t : Slice.Slots.Slots) (M : Mach), Corr ks k → FS L k → FOk C k → Chain M.pc k r → Inv M t →
      (Slice.Rv.run C en m M).ev <+: (runS ret m ks t).ev ∧
      (Slice.Rv.run C en m M).cost ≤ L * (runS ret m ks t).cost + jc k + ((tailM ret r).length + 1) ∧
      ((Slice.Rv.run C en m M).out ≠ .fuel → (Slice.Rv.run C en m M).out = (runS ret m ks t).out ∧ (Slice.Rv.run C en m M).ev = (runS ret m ks t).ev) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro k ks t M hc hs hf hch hinv
  cases hc with
  | nil =>
    have hp : M.pc = r := hch
    rw [tail_exec (en := en) ht hp hinv m]
    obtain ⟨hd, he⟩ := src_done ret m t
    refine ⟨?_, ?_, ?_⟩
    · rw [he]
      rcases play_ev (evalS ret t) (r + 4 * sE ret + 8) (tailM ret r) m with h | h <;> rw [h]
      · exact List.nil_prefix
      · exact List.prefix_refl _
    · have := play_cost (evalS ret t) (r + 4 * sE ret + 8) (tailM ret r) m
      omega
    · intro ho
      obtain ⟨h1, h2⟩ := play_out _ _ _ _ ho
      exact ⟨by rw [h1, hd], by rw [h2, he]⟩
  | @jmp ks k p q hc' =>
    obtain ⟨⟨i, hfe, ha⟩, hf'⟩ := hf
    obtain ⟨hp, hch'⟩ := hch
    subst hp
    obtain ⟨m', e', p', i'⟩ := exec_jmp (en := en) hfe ha hinv
    have hS : FS L k := hs
    rw [e' m]
    cases m with
    | zero => exact ⟨List.nil_prefix, Nat.zero_le _, fun h => absurd rfl h⟩
    | succ a =>
      obtain ⟨h1, h2, h3⟩ := ih a (by omega) k ks t m' hc' hS hf' (by rw [p']; exact hch') i'
      have hx := runS_ext ret a (a + 1) ks t (by omega)
      have hm := Nat.mul_le_mul_left L hx.2.2.2
      refine ⟨List.IsPrefix.trans h1 hx.2.1, ?_, ?_⟩
      · show 1 + (Slice.Rv.run C en a m').cost ≤ _
        simp only [jc]
        omega
      · intro ho
        obtain ⟨o1, o2⟩ := h3 ho
        have hnf : (runS ret a ks t).out ≠ .fuel := by rw [← o1]; exact ho
        have he := hx.1 hnf
        exact ⟨by rw [← he]; exact o1, by rw [← he]; exact o2⟩
  | @cmd ks k c q pc hc' =>
    have hns := hf.1
    obtain ⟨m', e', hf', hch', i'⟩ := chunk_exec (en := en) hC hf hch hinv
    have hlen := chunk_length (c := c) pc k t hns
    have hS' : FS L (nextK c pc k t) := next_fs t hs.1 hs.2
    have hsc : stepC c ≤ L := Nat.le_trans (stepC_le c) hs.1
    have hjc : jc (.cmd c pc :: k) = jc k := rfl
    rw [e' m]
    by_cases hm : m < (chunkC c pc t).length
    · obtain ⟨o1, o2, o3⟩ := play_short (F := fun j => Slice.Rv.run C en j m') hm
      refine ⟨by rw [o2]; exact List.nil_prefix, ?_, fun h => absurd o1 h⟩
      cases m with
      | zero => omega
      | succ n =>
        rw [src_step ret hns n q ks t]
        show _ ≤ L * (1 + _) + _ + _
        rw [Nat.mul_add, Nat.mul_one]
        omega
    · obtain ⟨a, rfl⟩ : ∃ a, m = (chunkC c pc t).length + a := ⟨m - (chunkC c pc t).length, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, (chunkC c pc t).length + a = n + 1 := ⟨(chunkC c pc t).length + a - 1, by omega⟩
      have hle : a ≤ n := by omega
      obtain ⟨h1, h2, h3⟩ := ih a (by omega) _ _ _ m' (hc'.next c q pc t) hS' hf' hch' i'
      have hx := runS_ext ret a n (nextS c q ks t) (nextT c t) hle
      have hm2 := Nat.mul_le_mul_left L hx.2.2.2
      obtain ⟨o1, o2, o3⟩ := play_long (c := chunkC c pc t) (F := fun j => Slice.Rv.run C en j m') a
      rw [o1, o2, o3, hn, src_step ret hns n q ks t]
      refine ⟨List.IsPrefix.trans h1 hx.2.1, ?_, ?_⟩
      · show _ ≤ L * (1 + _) + _ + _
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · intro ho
        obtain ⟨u1, u2⟩ := h3 ho
        have hnf : (runS ret a (nextS c q ks t) (nextT c t)).out ≠ .fuel := by rw [← u1]; exact ho
        have he := hx.1 hnf
        exact ⟨by show _ = (runS ret n _ _).out; rw [← he]; exact u1, by show _ = (runS ret n _ _).ev; rw [← he]; exact u2⟩

/-! ## What the source finishes, the machine finishes -/

theorem jc_next {c : SCmd} (pc : Nat) (k : List TF) (t : Slice.Slots.Slots) : jc (nextK c pc k t) ≤ jc k + 1 := by
  cases c with
  | ite e a b =>
    simp only [nextK]
    split
    · rw [jc_push]; simp only [jc]; omega
    · rw [jc_push]; omega
  | loop e b =>
    simp only [nextK]
    split
    · rw [jc_push]; simp only [jc]; omega
    · omega
  | _ => simp [nextK]

/-- **`ahead`.** Induction on fuel and pending jumps together: a jump spends none of the source's fuel. -/
theorem ahead {C : List Byte} {en : Env} {ret : SExpr} {r : Nat} (hC : C.length ≤ 3000) (ht : Tail C ret r) :
    ∀ (w n : Nat) (k : List TF) (ks : List SFrame) (t : Slice.Slots.Slots) (M : Mach), 2 * n + jc k ≤ w → Corr ks k → FOk C k → Chain M.pc k r → Inv M t →
      (runS ret n ks t).out ≠ .fuel →
      ∃ m, (Slice.Rv.run C en m M).out = (runS ret n ks t).out ∧ (Slice.Rv.run C en m M).ev = (runS ret n ks t).ev := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
  intro n k ks t M hw hc hf hch hinv hout
  cases hc with
  | nil =>
    have hp : M.pc = r := hch
    obtain ⟨hd, he⟩ := src_done ret n t
    obtain ⟨h1, h2⟩ := play_fin (evalS ret t) (r + 4 * sE ret + 8) (tailM ret r) _ (Nat.lt_succ_self _)
    refine ⟨(tailM ret r).length + 1, ?_, ?_⟩
    · rw [tail_exec (en := en) ht hp hinv, h1, hd]
    · rw [tail_exec (en := en) ht hp hinv, h2, he]
  | @jmp ks k p q hc' =>
    obtain ⟨⟨i, hfe, ha⟩, hf'⟩ := hf
    obtain ⟨hp, hch'⟩ := hch
    subst hp
    obtain ⟨m', e', p', i'⟩ := exec_jmp (en := en) hfe ha hinv
    simp only [jc] at hw
    obtain ⟨a, h1, h2⟩ := ih (2 * n + jc k) (by omega) n k ks t m' (Nat.le_refl _) hc' hf' (by rw [p']; exact hch') i' hout
    obtain ⟨o1, o2, _⟩ := play_long (c := [(M.pc, [])]) (F := fun j => Slice.Rv.run C en j m') a
    refine ⟨[(M.pc, ([] : List Lk))].length + a, ?_, ?_⟩
    · rw [e', o1, h1]
    · rw [e', o2, h2]
  | @cmd ks k c q pc hc' =>
    have hns := hf.1
    obtain ⟨m', e', hf', hch', i'⟩ := chunk_exec (en := en) hC hf hch hinv
    cases n with
    | zero => exact absurd rfl hout
    | succ n =>
      have hj := jc_next (c := c) pc k t
      simp only [jc] at hw
      rw [src_step ret hns n q ks t] at hout ⊢
      obtain ⟨a, h1, h2⟩ := ih (2 * n + jc (nextK c pc k t)) (by omega) n _ _ _ m' (Nat.le_refl _) (hc'.next c q pc t) hf' hch' i' hout
      obtain ⟨o1, o2, _⟩ := play_long (c := chunkC c pc t) (F := fun j => Slice.Rv.run C en j m') a
      refine ⟨(chunkC c pc t).length + a, ?_, ?_⟩
      · rw [e', o1, h1]; rfl
      · rw [e', o2, h2]; rfl

/-! ## Two machines -/

theorem view_tick {f : Observer} {l : List Lk} {q : List Nat} {r r' : Beh} (h : r.view f = r'.view f) :
    (tick l q r).view f = (tick l q r').view f := by
  have he := congrArg Beh.ev h
  have hl := congrArg Beh.lk h
  have hc := congrArg Beh.cost h
  have ho := congrArg Beh.out h
  simp only [Beh.view] at he hl hc ho
  simp only [tick, Beh.view, he, hl, hc, ho]

/-- One source step off the front of two equal views. -/
theorem view_peel {f : Observer} {l l' : List Lk} {q q' : List Nat} {r r' : Beh} (h : (tick l q r).view f = (tick l' q' r').view f)
    (hl : l.length = l'.length) : l = l' ∧ r.view f = r'.view f := by
  have he := congrArg Beh.ev h
  have hk := congrArg Beh.lk h
  have hc := congrArg Beh.cost h
  have ho := congrArg Beh.out h
  simp only [Beh.view, tick] at he hk hc ho
  obtain ⟨h1, h2⟩ := List.append_inj (List.cons.inj hk).2 hl
  have hc' : r.cost = r'.cost := by omega
  refine ⟨h1, ?_⟩
  simp only [Beh.view, he, h2, hc', ho]

theorem lkOf_length (c : SCmd) (t t' : Slice.Slots.Slots) : (lkOf c t).length = (lkOf c t').length := by
  cases c <;> simp only [lkOf] <;> (try split) <;> (try split) <;> rfl

theorem guard_same {a b : Nat}
    (h : (if a ≠ 0 then [Lk.branch true] else [Lk.branch false]) = (if b ≠ 0 then [Lk.branch true] else [Lk.branch false])) :
    a ≠ 0 ↔ b ≠ 0 := by
  by_cases h1 : a ≠ 0 <;> by_cases h2 : b ≠ 0 <;> simp_all

/-- **What the source shows fixes what comes next**: the chunk and the frames on both sides. -/
theorem same_step {c : SCmd} {t t' : Slice.Slots.Slots} (h : lkOf c t = lkOf c t') (pc : Nat) (k : List TF) (q : List Nat) (ks : List SFrame) :
    chunkC c pc t = chunkC c pc t' ∧ nextK c pc k t = nextK c pc k t' ∧ nextS c q ks t = nextS c q ks t' := by
  cases c with
  | skip | set _ _ | seq _ _ => exact ⟨rfl, rfl, rfl⟩
  | ite e a b =>
    have hg := guard_same h
    refine ⟨rfl, ?_, ?_⟩
    · simp only [nextK, hg]
    · simp only [nextS, hg]
  | loop e b =>
    have hg := guard_same h
    refine ⟨rfl, ?_, ?_⟩
    · simp only [nextK, hg]
    · simp only [nextS, hg]
  | load x e =>
    simp only [lkOf, addrLk, List.cons.injEq, Lk.addr.injEq, Int.ofNat.injEq, and_true] at h
    exact ⟨by simp only [chunkC, h], rfl, rfl⟩
  | store e v =>
    simp only [lkOf, addrLk, List.cons.injEq, Lk.addr.injEq, Int.ofNat.injEq, and_true] at h
    exact ⟨by simp only [chunkC, h], rfl, rfl⟩

theorem next_noSeq {c : SCmd} {q : List Nat} {ks : List SFrame} (t : Slice.Slots.Slots) (h : Slots.NoSeqS ((c, q) :: ks)) : Slots.NoSeqS (nextS c q ks t) := by
  have ht : Slots.NoSeqS ks := fun x hx => h x (List.mem_cons_of_mem _ hx)
  cases c with
  | ite e a b =>
    simp only [nextS]
    split
    · exact Slots.pushS_noSeq _ _ _ ht
    · exact Slots.pushS_noSeq _ _ _ ht
  | loop e b =>
    simp only [nextS]
    split
    · exact Slots.pushS_noSeq _ _ _ h
    · exact ht
  | _ => exact ht

theorem src_nil (ret : SExpr) (n n' : Nat) (t : Slice.Slots.Slots) : runS ret n [] t = runS ret n' [] t := by
  cases n <;> cases n' <;> rfl

/-- **Equal views at some fuel are equal at any lower fuel**: each step's leak is at the front of the list. -/
theorem view_mono (ret : SExpr) (f : Observer) : ∀ (m n : Nat) (ks : List SFrame) (t t' : Slice.Slots.Slots), n ≤ m → Slots.NoSeqS ks →
    (runS ret m ks t).view f = (runS ret m ks t').view f → (runS ret n ks t).view f = (runS ret n ks t').view f := by
  intro m
  induction m with
  | zero =>
    intro n ks t t' hn _ h
    obtain rfl : n = 0 := by omega
    exact h
  | succ m ih =>
    intro n ks t t' hn hs h
    cases ks with
    | nil => rw [src_nil ret n (m + 1) t, src_nil ret n (m + 1) t']; exact h
    | cons x ks =>
      obtain ⟨c, q⟩ := x
      cases n with
      | zero => rfl
      | succ n =>
        have hns : ∀ a b, c ≠ .seq a b := hs _ List.mem_cons_self
        rw [src_step ret hns m q ks t, src_step ret hns m q ks t'] at h
        rw [src_step ret hns n q ks t, src_step ret hns n q ks t']
        obtain ⟨hl, hr⟩ := view_peel h (lkOf_length c t t')
        obtain ⟨_, _, ss⟩ := same_step hl 0 [] q ks
        rw [← ss] at hr ⊢
        rw [← hl]
        exact view_tick (ih n _ _ _ (by omega) (next_noSeq t hs) hr)

/-- **`det`.** Two machines, in different environments, on what may be different inputs. If the source's two runs show the same at fuel `m`, the machines' do at fuel `m`. -/
theorem det_run {C : List Byte} {en en' : Env} {ret : SExpr} {r : Nat} (hC : C.length ≤ 3000) (ht : Tail C ret r) (f : Observer) :
    ∀ (m : Nat) (k : List TF) (ks : List SFrame) (t t' : Slice.Slots.Slots) (M M' : Mach), Corr ks k → Slots.NoSeqS ks → FOk C k →
      Chain M.pc k r → Chain M'.pc k r → Inv M t → Inv M' t' →
      (runS ret m ks t).view f = (runS ret m ks t').view f →
      (Slice.Rv.run C en m M).view f = (Slice.Rv.run C en' m M').view f := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro k ks t t' M M' hc hn hf hch hch' hinv hinv' hv
  cases hc with
  | nil =>
    rw [tail_exec (en := en) ht hch hinv, tail_exec (en := en') ht hch' hinv']
    have he := congrArg Beh.ev hv
    simp only [Beh.view] at he
    rw [(src_done ret m t).2, (src_done ret m t').2] at he
    exact play_view f _ he _ m
  | @jmp ks k p q hc' =>
    obtain ⟨⟨i, hfe, ha⟩, hf'⟩ := hf
    obtain ⟨hp, h1⟩ := hch
    obtain ⟨hp', h2⟩ := hch'
    obtain ⟨m1, e1, p1, i1⟩ := exec_jmp (m := M) (q := q) (en := en) (by rw [← hp]; exact hfe) (by rw [← hp]; exact ha) hinv
    obtain ⟨m2, e2, p2, i2⟩ := exec_jmp (m := M') (q := q) (en := en') (by rw [← hp']; exact hfe) (by rw [← hp']; exact ha) hinv'
    rw [e1 m, e2 m, ← hp, ← hp']
    apply play_congr
    intro a ha'
    simp only [List.length_cons, List.length_nil] at ha'
    exact ih a (by omega) k ks t t' m1 m2 hc' hn hf' (by rw [p1]; exact h1) (by rw [p2]; exact h2) i1 i2
      (view_mono ret f m a ks t t' (by omega) hn hv)
  | @cmd ks k c q pc hc' =>
    have hns := hf.1
    obtain ⟨m1, e1, f1, c1, i1⟩ := chunk_exec (en := en) hC hf hch hinv
    obtain ⟨m2, e2, f2, c2, i2⟩ := chunk_exec (en := en') hC hf hch' hinv'
    have hlen := (chunk_length (c := c) pc k t hns).1
    cases m with
    | zero => rfl
    | succ n =>
      rw [src_step ret hns n q ks t, src_step ret hns n q ks t'] at hv
      obtain ⟨hl, hr⟩ := view_peel hv (lkOf_length c t t')
      obtain ⟨sc, sk, ss⟩ := same_step hl pc k q ks
      rw [← sk] at f2 c2
      rw [← ss] at hr
      rw [e1 (n + 1), e2 (n + 1), ← sc]
      apply play_congr
      intro a ha
      exact ih a (by omega) _ _ _ _ m1 m2 (hc'.next c q pc t) (next_noSeq t hn) f1 c1 c2 i1 i2
        (view_mono ret f n a _ _ _ (by omega) (next_noSeq t hn) hr)

/-- Unfinished source runs have shown no event. -/
theorem fuel_ev (ret : SExpr) : ∀ (n : Nat) (ks : List SFrame) (t : Slice.Slots.Slots), Slots.NoSeqS ks → (runS ret n ks t).out = .fuel → (runS ret n ks t).ev = [] := by
  intro n
  induction n with
  | zero =>
    intro ks t _ h
    cases ks with
    | nil => simp [runS] at h
    | cons _ _ => rfl
  | succ n ih =>
    intro ks t hs h
    cases ks with
    | nil => simp [runS] at h
    | cons x ks =>
      obtain ⟨c, q⟩ := x
      have hns : ∀ a b, c ≠ .seq a b := hs _ List.mem_cons_self
      rw [src_step ret hns n q ks t] at h ⊢
      exact ih _ _ (next_noSeq t hs) h

/-! ## The program -/

def genP (p : SProg) : List Insn :=
  [.lui 7 0x20] ++ genC p.body ++ genE p.ret 0 ++ [.add 10 8 0, .addi 17 0 (Int.ofNat 93), .ecall]

def okP (p : SProg) : Bool :=
  okC p.body && okE p.ret 0 && decide (4 * (genP p).length ≤ 3000)

def startPc : Nat := codeBase + 4
def retPc (p : SProg) : Nat := startPc + 4 * sC p.body
def codeLen (p : SProg) : Nat := (genP p).length
/-- The per-step charge: the largest step any frame of the body can take (BOUND-01 step 5a; it was `codeLen`). -/
def stepL (p : SProg) : Nat := stepMax p.body
/-- The constant: the entry stub, the result's code and the exit. -/
def tailC (p : SProg) : Nat := sE p.ret + 4
def k0 (p : SProg) : List TF := pushT p.body startPc []
def ks0 (p : SProg) : List SFrame := pushS p.body [] []

theorem genP_length (p : SProg) : (genP p).length = 1 + sC p.body + sE p.ret + 3 := by
  simp only [genP, List.length_append, genC_length, genE_length, List.length_cons, List.length_nil]

theorem genP_good {p : SProg} (hb : okC p.body = true) (hr : okE p.ret 0 = true) : ∀ i ∈ genP p, Good i := by
  intro i hi
  simp only [genP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((hi | hi) | hi) | (hi | hi | hi)
  · subst hi; exact Slice.Lower.good_lui (by omega) (by omega)
  · exact genC_good _ hb i hi
  · exact genE_good _ _ hr i hi
  · subst hi; exact Slice.Lower.good_add (by omega) (by omega) (by omega)
  · subst hi; exact Slice.Lower.good_addi (by omega) (by omega) (by omega)
  · subst hi; exact Slice.Lower.good_ecall

structure Laid (C : List Byte) (p : SProg) : Prop where
  size : C.length ≤ 3000
  lui : fetchI C codeBase = some (.lui 7 0x20)
  body : At C startPc (genC p.body)
  tail : Tail C p.ret (retPc p)

theorem laid {p : SProg} (hok : okP p = true) : Laid (code (genP p)) p := by
  simp only [okP, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hb, hr⟩, hlen⟩ := hok
  have hat : At (code (genP p)) codeBase (genP p) := fun j hj => fetchI_code (genP_good hb hr) hj
  simp only [genP] at hat
  have atP := hat.left.left
  have atB := atP.right
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one] at atB
  have atR := hat.left.right
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, genC_length] at atR
  have atX := hat.right
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, genC_length, genE_length] at atX
  have e1 : retPc p = codeBase + 4 * (1 + sC p.body) := by simp only [retPc, startPc]; omega
  have e2 : retPc p + 4 * sE p.ret = codeBase + 4 * (1 + sC p.body + sE p.ret) := by rw [e1]; omega
  refine ⟨by rw [code_length]; exact hlen, atP.left.head, atB, hr, by rw [e1]; exact atR, ?_, ?_, ?_⟩
  · rw [e2]; exact atX 0 (by simp)
  · rw [e2]; exact atX 1 (by simp)
  · rw [e2]; exact atX 2 (by simp)

theorem k0_fok {C : List Byte} {p : SProg} (hl : Laid C p) (hb : okC p.body = true) : FOk C (k0 p) :=
  push_fok _ _ _ hb hl.body trivial

theorem okP_body {p : SProg} (hok : okP p = true) : okC p.body = true := by
  simp only [okP, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1.1

theorem k0_corr (p : SProg) : Corr (ks0 p) (k0 p) := Corr.push _ _ _ Corr.nil

theorem ks0_noSeq (p : SProg) : Slots.NoSeqS (ks0 p) := Slots.pushS_noSeq _ _ _ (fun _ h => by simp at h)

theorem k0_fs (p : SProg) : FS (stepL p) (k0 p) := push_fs _ _ _ (Nat.le_refl _) trivial

theorem k0_jc (p : SProg) : jc (k0 p) = 0 := by
  simp [k0, jc_push, jc]

/-- The entry stub, then the frames. -/
theorem entry {p : SProg} (hl : Laid (code (genP p)) p) (d : Nat → Byte) (e : Env) :
    ∃ m₁, (∀ a, Slice.Rv.run (code (genP p)) e (a + 1) (init (code (genP p)) d e) = tickM (codeBase, []) (Slice.Rv.run (code (genP p)) e a m₁)) ∧
      Chain m₁.pc (k0 p) (retPc p) ∧ Inv m₁ (wordAt d) := by
  obtain ⟨m₁, e₁, p₁, i₁⟩ := entry_exec (d := d) (e := e) hl.size hl.lui
  refine ⟨m₁, fun a => e₁ (a + 1), ?_, i₁⟩
  rw [p₁]
  exact push_chain _ _ _ _ rfl

/-- `behind`, from the first byte. -/
theorem behind_top {p : SProg} (hok : okP p = true) (m : Nat) (d : Nat → Byte) (e : Env) :
    (Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).ev <+: (runS p.ret m (ks0 p) (wordAt d)).ev ∧
    (Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).cost ≤ stepL p * (runS p.ret m (ks0 p) (wordAt d)).cost + tailC p ∧
    ((Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).out ≠ .fuel →
      (Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).out = (runS p.ret m (ks0 p) (wordAt d)).out ∧
      (Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).ev = (runS p.ret m (ks0 p) (wordAt d)).ev) := by
  have hl := laid hok
  cases m with
  | zero => exact ⟨List.nil_prefix, by show 0 ≤ _; omega, fun h => absurd rfl h⟩
  | succ a =>
    obtain ⟨m₁, e₁, c₁, i₁⟩ := entry (d := d) (e := e) hl
    obtain ⟨h1, h2, h3⟩ := behind (en := e) hl.size hl.tail (stepL p) a (k0 p) (ks0 p) (wordAt d) m₁ (k0_corr p) (k0_fs p) (k0_fok hl (okP_body hok)) c₁ i₁
    have hx := runS_ext p.ret a (a + 1) (ks0 p) (wordAt d) (by omega)
    have hm := Nat.mul_le_mul_left (stepL p) hx.2.2.2
    have hj := k0_jc p
    have hL : tailC p = sE p.ret + 4 := rfl
    have ht : (tailM p.ret (retPc p)).length = sE p.ret + 2 := by simp [tailM, mE_length]
    rw [e₁ a]
    refine ⟨List.IsPrefix.trans h1 hx.2.1, ?_, ?_⟩
    · show 1 + (Slice.Rv.run _ e a m₁).cost ≤ _
      omega
    · intro ho
      obtain ⟨o1, o2⟩ := h3 ho
      have hnf : (runS p.ret a (ks0 p) (wordAt d)).out ≠ .fuel := by rw [← o1]; exact ho
      have he := hx.1 hnf
      exact ⟨by rw [← he]; exact o1, by rw [← he]; exact o2⟩

/-- `ahead`, from the first byte. -/
theorem ahead_top {p : SProg} (hok : okP p = true) (n : Nat) (d : Nat → Byte) (e : Env) (hf : (runS p.ret n (ks0 p) (wordAt d)).out ≠ .fuel) :
    ∃ m, (Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).out = (runS p.ret n (ks0 p) (wordAt d)).out ∧
      (Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).ev = (runS p.ret n (ks0 p) (wordAt d)).ev := by
  have hl := laid hok
  obtain ⟨m₁, e₁, c₁, i₁⟩ := entry (d := d) (e := e) hl
  obtain ⟨a, h1, h2⟩ := ahead (en := e) hl.size hl.tail _ n (k0 p) (ks0 p) (wordAt d) m₁ (Nat.le_refl _) (k0_corr p) (k0_fok hl (okP_body hok)) c₁ i₁ hf
  exact ⟨a + 1, by rw [e₁ a]; exact h1, by rw [e₁ a]; exact h2⟩

/-- `det`, from the first byte. -/
theorem det_top {p : SProg} (hok : okP p = true) (f : Observer) (m : Nat) (d d' : Nat → Byte) (e e' : Env)
    (hv : (runS p.ret m (ks0 p) (wordAt d)).view f = (runS p.ret m (ks0 p) (wordAt d')).view f) :
    (Slice.Rv.run (code (genP p)) e m (init (code (genP p)) d e)).view f = (Slice.Rv.run (code (genP p)) e' m (init (code (genP p)) d' e')).view f := by
  have hl := laid hok
  cases m with
  | zero => rfl
  | succ a =>
    obtain ⟨m₁, e₁, c₁, i₁⟩ := entry (d := d) (e := e) hl
    obtain ⟨m₂, e₂, c₂, i₂⟩ := entry (d := d') (e := e') hl
    rw [e₁ a, e₂ a]
    exact tick_view (det_run hl.size hl.tail f a (k0 p) (ks0 p) (wordAt d) (wordAt d') m₁ m₂ (k0_corr p) (ks0_noSeq p) (k0_fok hl (okP_body hok)) c₁ c₂ i₁ i₂
      (view_mono p.ret f (a + 1) a _ _ _ (by omega) (ks0_noSeq p) hv))

/-- **The environment cannot show**, at any fuel, to any observer, whether or not the run ever finishes. -/
theorem compiled_ignores_env {p : SProg} (hok : okP p = true) (f : Observer) (n : Nat) (d : Nat → Byte) (e e' : Env) :
    (Slice.Rv.run (code (genP p)) e n (init (code (genP p)) d e)).view f = (Slice.Rv.run (code (genP p)) e' n (init (code (genP p)) d e')).view f :=
  det_top hok f n d d e e' rfl

/-! ## The pass -/

/-- `t.fuel m = m`. The first slice's constant could not hold a run that never ends. -/
def xf (p : SProg) : Xform where
  lk l := l
  cost c := stepL p * c + tailC p
  fuel m := m
  costMono a b h := by
    have := Nat.mul_le_mul_left (stepL p) h
    omega

def compR (p : SProg) : Except String (List Byte × Xform) :=
  if okP p then .ok (code (genP p), xf p) else .error "the program does not fit the slice's instructions"

theorem compR_ok {p : SProg} {p' : List Byte} {t : Xform} (h : compR p = .ok (p', t)) :
    okP p = true ∧ p' = code (genP p) ∧ t = xf p := by
  simp only [compR] at h
  split at h
  · rename_i hk
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨hk, h.1.symm, h.2.symm⟩
  · cases h

/-- **Slots to machine bytes, over loops.** One step becomes many, the machine has an environment, and a run may never finish. -/
def rvPass (P : Nat → Bool) : PassCert (slotLang Env P) (rvLang P) where
  comp := compR
  enc i := i
  enc_adm _ h := h
  cover u hu := ⟨u, hu, rfl⟩
  low_cover u u' hu hu' hl := ⟨u, u', hu, hu', hl, rfl, rfl⟩
  ev_sim p p' t h m i _ := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    exact (behind_top hok m i.1 i.2).1
  cost_sim p p' t h m i _ := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    exact (behind_top hok m i.1 i.2).2.1
  det p p' t h f m i i' _ _ he := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    exact det_top hok f m i.1 i'.1 i.2 i'.2 he
  progress p p' t h n i _ hf := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    exact ahead_top hok n i.1 i.2 hf
  catch_up p p' t h n i _ := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    by_cases hf : (runS p.ret n (ks0 p) (wordAt i.1)).out = .fuel
    · refine ⟨0, ?_⟩
      show (runS p.ret n (ks0 p) (wordAt i.1)).ev <+: _
      rw [fuel_ev p.ret n _ _ (ks0_noSeq p) hf]
      exact List.nil_prefix
    · obtain ⟨m, _, h2⟩ := ahead_top hok n i.1 i.2 hf
      refine ⟨m, ?_⟩
      show (runS p.ret n (ks0 p) (wordAt i.1)).ev <+: (Slice.Rv.run _ i.2 m (init _ i.1 i.2)).ev
      rw [h2]
      exact List.prefix_refl _
  reflect p p' t h m i _ hf := by
    obtain ⟨hok, rfl, rfl⟩ := compR_ok h
    obtain ⟨h1, h2⟩ := (behind_top hok m i.1 i.2).2.2 hf
    exact ⟨m, h1.symm, h2.symm⟩

/-- **Source to machine bytes**: two certified passes, chained. -/
def pipeline (P : Nat → Bool) : PassCert (sliceLang Env P) (rvLang P) :=
  (Slots.slotPass Env P).seq (rvPass P)

/-- **What the checker accepts, compiled, carries `rel` on the machine**, by the kernel's transfer alone, whether or not it ever finishes. -/
theorem slice_carries {P : Nat → Bool} {p : Prog} {C : List Byte} {t : Xform}
    (hc : sliceCheck P p = true) (hcomp : (pipeline P).comp p = .ok (C, t)) : Cert.rel (rvLang P) C :=
  (pipeline P).rel_transfer hcomp (sliceCheck_rel hc)

end LCore.Slice2.Lower
