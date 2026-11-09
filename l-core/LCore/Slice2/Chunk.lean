/-
  VS-2 step 6, the frame layer. **`chunk_exec` is the lemma the design rests on**: from a good state, a frame's `chunk` takes the machine to the next good state. A chunk is computed from
  the frame and the slots alone, so the machine's environment and its other registers cannot appear in it.

  A jump at the end of a loop body or a branch's first arm belongs to no source step, so it is a frame of its own.
-/
import LCore.Slice2.Lower

namespace LCore.Slice2.Lower

open Slice (W64 Expr Store upd eval retEv cap tick tick_ext Ext sec0 inp)
open Slice.Rv
open Slice.Slots (SExpr evalS updS encBytes wordAt)
open Slice.Lower (Good fetchI fetchI_parts fetchI_code fetchI_bound At Micro tickM fuelB playApp playApp_append Exec Exec.nil Exec.trans Exec.step Exec.stepAt
  addImm_val slotAddr Inv mE genE sE okE genE_length genE_good mE_length wordsMax exitF entry_exec exit_exec code_length Inv.mono_mem play_view get_zero)
open Slots (SCmd SProg SFrame pushS runS slotLang arrBase)

/-- A target frame: a command at a PC, or a jump. -/
inductive TF where
  | cmd (c : SCmd) (pc : Nat)
  | jmp (p q : Nat)

def pushT : SCmd → Nat → List TF → List TF
  | .seq a b, pc, k => pushT a pc (pushT b (pc + 4 * sC a) k)
  | c, pc, k => .cmd c pc :: k

/-- **What a frame shows**: a function of the frame and, for an array access, its masked index. -/
def chunkC (c : SCmd) (pc : Nat) (t : Slice.Slots.Slots) : List Micro :=
  match c with
  | .skip => [(pc, [])]
  | .set n e => mE e pc ++ [(pc + 4 * sE e, [.addr (Int.ofNat (slotAddr n))])]
  | .seq _ _ => []
  | .ite e _ _ | .loop e _ => mE e pc ++ [(pc + 4 * sE e, [])]
  | .load x e =>
    mIdx e pc ++ [(pc + 4 * (sE e + 5), [.addr (Int.ofNat (arrAddr (idx (evalS e t))))]),
      (pc + 4 * (sE e + 5) + 4, [.addr (Int.ofNat (slotAddr x))])]
  | .loadB x ws e =>
    mE e pc ++ [(pc + 4 * sE e, []), (pc + 4 * sE e + 4, []),
      (pc + 4 * sE e + 8, [.addr (Int.ofNat (dataBase + 8 * ws.headD 0 + Slots.bidxS ws (evalS e t)))]),
      (pc + 4 * sE e + 12, [.addr (Int.ofNat (slotAddr x))])]
  | .store e v =>
    mIdx e pc ++ mE v (pc + 4 * (sE e + 5)) ++
      [(pc + 4 * (sE e + 5) + 4 * sE v, [.addr (Int.ofNat (arrAddr (idx (evalS e t))))])]
  | .storeB ws e v =>
    mE e pc ++ [(pc + 4 * sE e, []), (pc + 4 * sE e + 4, [])] ++ mE v (pc + 4 * sE e + 8) ++
      [(pc + 4 * sE e + 8 + 4 * sE v, [.addr (Int.ofNat (dataBase + 8 * ws.headD 0 + Slots.bidxS ws (evalS e t)))])]
  | .emitB ws =>
    [(pc, []), (pc + 4, []), (pc + 8, []), (pc + 12, []),
      (pc + 16, (List.range (8 * ws.length)).map fun i => .addr (Int.ofNat (dataBase + 8 * ws.headD 0 + i)))]

/-- **What a frame emits**, at its last micro-step: the output's bytes for `emitB` (RC-02), and nothing for every other command. -/
def evC (c : SCmd) (t : Slice.Slots.Slots) : List Ev :=
  match c with
  | .emitB ws => [.emit "out" (Slots.outBytesS t ws)]
  | _ => []

def chunk : TF → Slice.Slots.Slots → List Micro
  | .jmp p _, _ => [(p, [])]
  | .cmd c pc, t => chunkC c pc t

/-- The slots after a command. -/
def nextT (c : SCmd) (t : Slice.Slots.Slots) : Slice.Slots.Slots :=
  match c with
  | .set n e => updS t n (evalS e t)
  | .load x e => updS t x (t (arrBase + idx (evalS e t)))
  | .loadB x ws e => updS t x (Slots.byteAtS t ws (Slots.bidxS ws (evalS e t)))
  | .store e v => updS t (arrBase + idx (evalS e t)) (evalS v t)
  | .storeB ws e v => Slots.storeAtS t ws (Slots.bidxS ws (evalS e t)) (evalS v t)
  | _ => t

/-- The frames after a command. -/
def nextK (c : SCmd) (pc : Nat) (k : List TF) (t : Slice.Slots.Slots) : List TF :=
  match c with
  | .ite e a b =>
    if (evalS e t).val ≠ 0 then
      pushT a (pc + 4 * (sE e + 1)) (.jmp (pc + 4 * (sE e + 1 + sC a)) (pc + 4 * (sE e + 1 + sC a + 1 + sC b)) :: k)
    else pushT b (pc + 4 * (sE e + 1 + sC a + 1)) k
  | .loop e b =>
    if (evalS e t).val ≠ 0 then
      pushT b (pc + 4 * (sE e + 1)) (.jmp (pc + 4 * (sE e + 1 + sC b)) pc :: .cmd (.loop e b) pc :: k)
    else k
  | _ => k

/-- The frames' code is where they say. -/
def FOk (C : List Byte) : List TF → Prop
  | [] => True
  | .cmd c pc :: k => (∀ a b, c ≠ .seq a b) ∧ okC c = true ∧ At C pc (genC c) ∧ FOk C k
  | .jmp p q :: k => (∃ i, fetchI C p = some (.beq 0 0 i) ∧ addImm (W64.ofNat p) i = q) ∧ FOk C k

/-- The frames run in order, ending at `f`. -/
def Chain : Nat → List TF → Nat → Prop
  | pc, [], f => pc = f
  | pc, .cmd c q :: k, f => q = pc ∧ Chain (pc + 4 * sC c) k f
  | pc, .jmp p q :: k, f => p = pc ∧ Chain q k f

theorem push_fok {C : List Byte} : ∀ (c : SCmd) (pc : Nat) (k : List TF), okC c = true →
    At C pc (genC c) → FOk C k → FOk C (pushT c pc k)
  | .seq a b, pc, k, hc, hat, hk => by
    simp only [okC, Bool.and_eq_true] at hc
    simp only [genC] at hat
    have hr := Slice.Lower.At.right hat
    rw [genC_length] at hr
    exact push_fok a pc _ hc.1 (Slice.Lower.At.left hat) (push_fok b _ k hc.2 hr hk)
  | .skip, _, _, hc, hat, hk | .set _ _, _, _, hc, hat, hk | .ite _ _ _, _, _, hc, hat, hk
  | .loop _ _, _, _, hc, hat, hk | .load _ _, _, _, hc, hat, hk | .loadB _ _ _, _, _, hc, hat, hk
  | .store _ _, _, _, hc, hat, hk | .storeB _ _ _, _, _, hc, hat, hk | .emitB _, _, _, hc, hat, hk =>
    ⟨(by intro a b h; cases h), hc, hat, hk⟩

theorem push_chain : ∀ (c : SCmd) (pc : Nat) (k : List TF) (f : Nat), Chain (pc + 4 * sC c) k f →
    Chain pc (pushT c pc k) f
  | .seq a b, pc, k, f, h => by
    apply push_chain a pc
    apply push_chain b
    have : pc + 4 * sC a + 4 * sC b = pc + 4 * sC (.seq a b) := by simp only [sC]; omega
    rw [this]; exact h
  | .skip, _, _, _, h | .set _ _, _, _, _, h | .ite _ _ _, _, _, _, h | .loop _ _, _, _, _, h
  | .load _ _, _, _, _, h | .loadB _ _ _, _, _, _, h | .store _ _, _, _, _, h | .storeB _ _ _, _, _, _, h
  | .emitB _, _, _, _, h => ⟨rfl, h⟩

/-- A jump, forward or back. -/
theorem exec_jmp {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {i : Int} {q : Nat}
    (hf : fetchI C m.pc = some (.beq 0 0 i)) (ha : addImm (W64.ofNat m.pc) i = q) (hinv : Inv m t) :
    ∃ m', Exec C en [(m.pc, [])] m m' ∧ m'.pc = q ∧ Inv m' t := by
  have hs := step_beq (en := en) hf
  refine ⟨_, Exec.step hs, ?_, Inv.mono_mem hinv rfl rfl⟩
  show (if m.get 0 = m.get 0 then addImm (W64.ofNat m.pc) i else m.pc + 4) = q
  rw [if_pos rfl, ha]

/-- `if`: the guard, then into an arm, with the first arm's jump pending. -/
theorem exec_ite {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {e : SExpr} {a b : SCmd} {k : List TF} {f : Nat}
    (hC : C.length ≤ 3000) (hoc : okC (.ite e a b) = true) (hat : At C m.pc (genC (.ite e a b))) (hok : FOk C k)
    (hch : Chain (m.pc + 4 * sC (.ite e a b)) k f) (hinv : Inv m t) :
    ∃ m', Exec C en (chunkC (.ite e a b) m.pc t) m m' ∧ FOk C (nextK (.ite e a b) m.pc k t) ∧
      Chain m'.pc (nextK (.ite e a b) m.pc k t) f ∧ Inv m' (nextT (.ite e a b) t) := by
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
  obtain ⟨⟨⟨⟨ho1, ho2⟩, ho3⟩, ho4⟩, ho5⟩ := hoc
  simp only [genC] at hat
  have atG := Slice.Lower.At.left (Slice.Lower.At.left (Slice.Lower.At.left hat))
  have atA := Slice.Lower.At.right (Slice.Lower.At.left (Slice.Lower.At.left hat))
  simp only [List.length_append, genE_length, List.length_cons, List.length_nil, Nat.zero_add] at atA
  have atJ := (Slice.Lower.At.right (Slice.Lower.At.left hat)).head
  simp only [List.length_append, genE_length, genC_length, List.length_cons, List.length_nil, Nat.zero_add] at atJ
  have atB := Slice.Lower.At.right hat
  simp only [List.length_append, genE_length, genC_length, List.length_cons, List.length_nil, Nat.zero_add] at atB
  obtain ⟨m', e', hi', hp'⟩ := exec_guard (en := en) (t := t) (off := 4 * (sC a + 2)) hC (by omega) ho1
    (show Inv m t from hinv) atG
  simp only [sC] at hch
  have hbd := fetchI_bound atJ
  have hcb : codeBase = 0x100b0 := rfl
  have hv : (W64.ofNat (m.pc + 4 * (sE e + 1 + sC a))).val = m.pc + 4 * (sE e + 1 + sC a) := ofNat_val (by omega)
  refine ⟨m', e', ?_, ?_, hi'⟩
  · simp only [nextK]
    split
    · refine push_fok a _ _ ho2 atA ⟨⟨_, atJ, ?_⟩, hok⟩
      rw [addImm_val _ _ (by rw [hv]; omega), hv]; omega
    · exact push_fok b _ _ ho3 atB hok
  · simp only [nextK]
    split
    · rename_i hg
      rw [hp', if_pos hg]
      exact push_chain a _ _ _ ⟨by omega, hch⟩
    · rename_i hg
      rw [hp', if_neg hg]
      rw [show m.pc + 4 * sE e + 4 * (sC a + 2) = m.pc + 4 * (sE e + 1 + sC a + 1) by omega]
      exact push_chain b _ _ _ (by
        rw [show m.pc + 4 * (sE e + 1 + sC a + 1) + 4 * sC b = m.pc + 4 * (sE e + 1 + sC a + 1 + sC b) by omega]
        exact hch)

/-- `while`: the guard, then the body with the jump back and the loop pending, or past it. -/
theorem exec_loop {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {e : SExpr} {b : SCmd} {k : List TF} {f : Nat}
    (hC : C.length ≤ 3000) (hoc : okC (.loop e b) = true) (hat : At C m.pc (genC (.loop e b))) (hok : FOk C k)
    (hch : Chain (m.pc + 4 * sC (.loop e b)) k f) (hinv : Inv m t) :
    ∃ m', Exec C en (chunkC (.loop e b) m.pc t) m m' ∧ FOk C (nextK (.loop e b) m.pc k t) ∧
      Chain m'.pc (nextK (.loop e b) m.pc k t) f ∧ Inv m' (nextT (.loop e b) t) := by
  have hoc0 := hoc
  have hat0 := hat
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
  obtain ⟨⟨⟨ho1, ho2⟩, ho3⟩, ho4⟩ := hoc
  simp only [genC] at hat
  have atG := Slice.Lower.At.left (Slice.Lower.At.left hat)
  have atB := Slice.Lower.At.right (Slice.Lower.At.left hat)
  simp only [List.length_append, genE_length, List.length_cons, List.length_nil, Nat.zero_add] at atB
  have atJ := (Slice.Lower.At.right hat).head
  simp only [List.length_append, genE_length, genC_length, List.length_cons, List.length_nil, Nat.zero_add] at atJ
  obtain ⟨m', e', hi', hp'⟩ := exec_guard (en := en) (t := t) (off := 4 * (sC b + 2)) hC (by omega) ho1
    (show Inv m t from hinv) atG
  have hch0 := hch
  simp only [sC] at hch
  have hbd := fetchI_bound atJ
  have hcb : codeBase = 0x100b0 := rfl
  have hv : (W64.ofNat (m.pc + 4 * (sE e + 1 + sC b))).val = m.pc + 4 * (sE e + 1 + sC b) := ofNat_val (by omega)
  refine ⟨m', e', ?_, ?_, hi'⟩
  · simp only [nextK]
    split
    · refine push_fok b _ _ ho2 atB ⟨⟨_, atJ, ?_⟩, (by intro x y h; cases h), hoc0, hat0, hok⟩
      have hs : 0 < sE e + 1 + sC b := by omega
      rw [addImm_back _ _ (by omega) (by rw [hv]; omega), hv]; omega
    · exact hok
  · simp only [nextK]
    split
    · rename_i hg
      rw [hp', if_pos hg]
      refine push_chain b _ _ _ ⟨by omega, rfl, ?_⟩
      exact hch0
    · rename_i hg
      rw [hp', if_neg hg]
      rw [show m.pc + 4 * sE e + 4 * (sC b + 2) = m.pc + 4 * (sE e + 1 + sC b + 1) by omega]
      exact hch

/-- **One frame, on the machine**, whatever its environment. -/
theorem chunk_exec {C : List Byte} {en : Env} {m : Mach} {t : Slice.Slots.Slots} {c : SCmd} {pc : Nat} {k : List TF} {f : Nat}
    (hC : C.length ≤ 3000) (hok : FOk C (.cmd c pc :: k)) (hch : Chain m.pc (.cmd c pc :: k) f) (hinv : Inv m t) :
    ∃ m', ExecE C en (chunkC c pc t) (evC c t) m m' ∧ FOk C (nextK c pc k t) ∧ Chain m'.pc (nextK c pc k t) f ∧ Inv m' (nextT c t) := by
  obtain ⟨hns, hoc, hat, hok'⟩ := hok
  obtain ⟨hp, hch'⟩ := hch
  subst hp
  cases c with
  | skip =>
    have hs := step_addi (en := en) hat.head
    refine ⟨_, ExecE.ofExec (Exec.step hs), hok', hch', Inv.mono_mem hinv (by simp [Mach.get, Mach.set]) rfl⟩
  | set n e =>
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
    obtain ⟨m', e', p', i'⟩ := exec_set (en := en) hoc.1 hoc.2 hinv hat
    exact ⟨m', ExecE.ofExec e', hok', by rw [p']; exact hch', i'⟩
  | seq a b => exact absurd rfl (hns a b)
  | ite e a b =>
    obtain ⟨m', e', r'⟩ := exec_ite hC hoc hat hok' hch' hinv (en := en)
    exact ⟨m', ExecE.ofExec e', r'⟩
  | loop e b =>
    obtain ⟨m', e', r'⟩ := exec_loop hC hoc hat hok' hch' hinv (en := en)
    exact ⟨m', ExecE.ofExec e', r'⟩
  | load x e =>
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
    obtain ⟨m', e', p', i'⟩ := exec_load (en := en) hoc.1 hoc.2 hinv hat
    exact ⟨m', ExecE.ofExec e', hok', by rw [p']; exact hch', i'⟩
  | loadB x ws e =>
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
    obtain ⟨⟨⟨⟨hx, he⟩, hws⟩, hm⟩, hb⟩ := hoc
    generalize hB : ws.headD 0 = b at hws hb ⊢
    generalize hL : ws.length = len at hws hm hb
    subst hws
    obtain ⟨m', e', p', i'⟩ := exec_loadB (en := en) hx he hm hb hinv hat
    have hhead : (List.range' b len).headD 0 = b := hB
    simp only [chunkC, nextT, hhead]
    exact ⟨m', ExecE.ofExec e', hok', by rw [p']; exact hch', i'⟩
  | store e v =>
    simp only [okC, Bool.and_eq_true] at hoc
    obtain ⟨m', e', p', i'⟩ := exec_store (en := en) hoc.1 hoc.2 hinv hat
    exact ⟨m', ExecE.ofExec e', hok', by rw [p']; exact hch', i'⟩

  | storeB ws e v =>
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
    obtain ⟨⟨⟨⟨he, hv⟩, hws⟩, hm⟩, hb⟩ := hoc
    generalize hB : ws.headD 0 = b at hws hb ⊢
    generalize hL : ws.length = len at hws hm hb
    subst hws
    obtain ⟨m', e', p', i'⟩ := exec_storeB (en := en) he hv hm hb hinv hat
    have hhead : (List.range' b len).headD 0 = b := hB
    simp only [chunkC, nextT, evC, hhead]
    refine ⟨m', ExecE.ofExec e', hok', by rw [p']; exact hch', i'⟩
  | emitB ws =>
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hoc
    obtain ⟨⟨⟨hws, hl0⟩, hl⟩, hb⟩ := hoc
    generalize hB : ws.headD 0 = b at hws hb ⊢
    generalize hL : ws.length = len at hws hl0 hl hb ⊢
    subst hws
    obtain ⟨m', e', p', i'⟩ := exec_emitB (en := en) hl0 hl hb hinv hat
    have hl' : (List.range' b len).length = len := List.length_range'
    have hhead : (List.range' b len).headD 0 = b := hB
    simp only [chunkC, nextT, evC, hhead, hl']
    refine ⟨m', e', hok', ?_, i'⟩
    simp only [nextK]
    rw [p']
    exact hch'

end LCore.Slice2.Lower
