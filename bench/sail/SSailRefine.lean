import LeanRV64D
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

/-! S-SAIL (backlog/S-SAIL.md): ADDI and BEQ, as executed by the generated Sail RISC-V model
    (opencompl/sail-riscv-lean 51c635c460 with bench/sail/apply-435.sh), for every register pair
    and immediate. Not built by CI. Checked in the scratch copy with `lake env lean`; the receipts
    are `ssail-*`. The 32-way case lemmas were generated, one per register, because the model's
    register file is 31 separately named registers. -/

set_option linter.unusedSimpArgs false
namespace SSail

abbrev St := SequentialState RegisterType trivialChoiceSource

/-- The x-register file as Sail stores it: `x0` reads 0, `xN` is the `Register.xN` entry. -/
def xget (σ : St) : Nat → Option (BitVec 64)
  | 0 => some 0
  | 1 => σ.regs.get? Register.x1
  | 2 => σ.regs.get? Register.x2
  | 3 => σ.regs.get? Register.x3
  | 4 => σ.regs.get? Register.x4
  | 5 => σ.regs.get? Register.x5
  | 6 => σ.regs.get? Register.x6
  | 7 => σ.regs.get? Register.x7
  | 8 => σ.regs.get? Register.x8
  | 9 => σ.regs.get? Register.x9
  | 10 => σ.regs.get? Register.x10
  | 11 => σ.regs.get? Register.x11
  | 12 => σ.regs.get? Register.x12
  | 13 => σ.regs.get? Register.x13
  | 14 => σ.regs.get? Register.x14
  | 15 => σ.regs.get? Register.x15
  | 16 => σ.regs.get? Register.x16
  | 17 => σ.regs.get? Register.x17
  | 18 => σ.regs.get? Register.x18
  | 19 => σ.regs.get? Register.x19
  | 20 => σ.regs.get? Register.x20
  | 21 => σ.regs.get? Register.x21
  | 22 => σ.regs.get? Register.x22
  | 23 => σ.regs.get? Register.x23
  | 24 => σ.regs.get? Register.x24
  | 25 => σ.regs.get? Register.x25
  | 26 => σ.regs.get? Register.x26
  | 27 => σ.regs.get? Register.x27
  | 28 => σ.regs.get? Register.x28
  | 29 => σ.regs.get? Register.x29
  | 30 => σ.regs.get? Register.x30
  | _ => σ.regs.get? Register.x31

/-- Writing `xN`; writes to `x0` are dropped. -/
def xset (σ : St) (n : Nat) (v : BitVec 64) : St :=
  match n with
  | 0 => σ
  | 1 => { σ with regs := σ.regs.insert Register.x1 v }
  | 2 => { σ with regs := σ.regs.insert Register.x2 v }
  | 3 => { σ with regs := σ.regs.insert Register.x3 v }
  | 4 => { σ with regs := σ.regs.insert Register.x4 v }
  | 5 => { σ with regs := σ.regs.insert Register.x5 v }
  | 6 => { σ with regs := σ.regs.insert Register.x6 v }
  | 7 => { σ with regs := σ.regs.insert Register.x7 v }
  | 8 => { σ with regs := σ.regs.insert Register.x8 v }
  | 9 => { σ with regs := σ.regs.insert Register.x9 v }
  | 10 => { σ with regs := σ.regs.insert Register.x10 v }
  | 11 => { σ with regs := σ.regs.insert Register.x11 v }
  | 12 => { σ with regs := σ.regs.insert Register.x12 v }
  | 13 => { σ with regs := σ.regs.insert Register.x13 v }
  | 14 => { σ with regs := σ.regs.insert Register.x14 v }
  | 15 => { σ with regs := σ.regs.insert Register.x15 v }
  | 16 => { σ with regs := σ.regs.insert Register.x16 v }
  | 17 => { σ with regs := σ.regs.insert Register.x17 v }
  | 18 => { σ with regs := σ.regs.insert Register.x18 v }
  | 19 => { σ with regs := σ.regs.insert Register.x19 v }
  | 20 => { σ with regs := σ.regs.insert Register.x20 v }
  | 21 => { σ with regs := σ.regs.insert Register.x21 v }
  | 22 => { σ with regs := σ.regs.insert Register.x22 v }
  | 23 => { σ with regs := σ.regs.insert Register.x23 v }
  | 24 => { σ with regs := σ.regs.insert Register.x24 v }
  | 25 => { σ with regs := σ.regs.insert Register.x25 v }
  | 26 => { σ with regs := σ.regs.insert Register.x26 v }
  | 27 => { σ with regs := σ.regs.insert Register.x27 v }
  | 28 => { σ with regs := σ.regs.insert Register.x28 v }
  | 29 => { σ with regs := σ.regs.insert Register.x29 v }
  | 30 => { σ with regs := σ.regs.insert Register.x30 v }
  | _ => { σ with regs := σ.regs.insert Register.x31 v }

theorem lt32 (n : Nat) (h : n < 32) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 := by omega

set_option maxHeartbeats 0 in
/-- Read after write, for every pair of the 32 registers. -/
theorem xget_xset (σ : St) (n m : Nat) (hn : n < 32) (hm : m < 32) (v : BitVec 64) :
    xget (xset σ m v) n = if n = m ∧ m ≠ 0 then some v else xget σ n := by
  rcases lt32 n hn with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
  rcases lt32 m hm with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
  simp [xget, xset, Std.ExtDHashMap.get?_insert]

attribute [local simp] EStateM.run PreSail.readReg PreSail.writeReg BitVec.toNatInt regval_from_reg
  regval_into_reg bind EStateM.bind get getThe MonadStateOf.get EStateM.get modify modifyGet
  MonadStateOf.modifyGet EStateM.modifyGet Functor.map EStateM.map pure EStateM.pure

theorem rX_run_0 (σ : St) : (rX (.Regno 0)).run σ = match xget σ 0 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp [rX, xget, zero_reg, zeros, regval_from_reg, EStateM.run, pure, EStateM.pure, bind, EStateM.bind]

theorem rX_run_1 (σ : St) : (rX (.Regno 1)).run σ = match xget σ 1 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x1 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_2 (σ : St) : (rX (.Regno 2)).run σ = match xget σ 2 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x2 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_3 (σ : St) : (rX (.Regno 3)).run σ = match xget σ 3 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x3 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_4 (σ : St) : (rX (.Regno 4)).run σ = match xget σ 4 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x4 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_5 (σ : St) : (rX (.Regno 5)).run σ = match xget σ 5 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x5 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_6 (σ : St) : (rX (.Regno 6)).run σ = match xget σ 6 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x6 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_7 (σ : St) : (rX (.Regno 7)).run σ = match xget σ 7 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x7 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_8 (σ : St) : (rX (.Regno 8)).run σ = match xget σ 8 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x8 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_9 (σ : St) : (rX (.Regno 9)).run σ = match xget σ 9 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x9 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_10 (σ : St) : (rX (.Regno 10)).run σ = match xget σ 10 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x10 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_11 (σ : St) : (rX (.Regno 11)).run σ = match xget σ 11 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x11 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_12 (σ : St) : (rX (.Regno 12)).run σ = match xget σ 12 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x12 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_13 (σ : St) : (rX (.Regno 13)).run σ = match xget σ 13 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x13 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_14 (σ : St) : (rX (.Regno 14)).run σ = match xget σ 14 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x14 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_15 (σ : St) : (rX (.Regno 15)).run σ = match xget σ 15 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x15 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_16 (σ : St) : (rX (.Regno 16)).run σ = match xget σ 16 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x16 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_17 (σ : St) : (rX (.Regno 17)).run σ = match xget σ 17 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x17 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_18 (σ : St) : (rX (.Regno 18)).run σ = match xget σ 18 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x18 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_19 (σ : St) : (rX (.Regno 19)).run σ = match xget σ 19 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x19 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_20 (σ : St) : (rX (.Regno 20)).run σ = match xget σ 20 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x20 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_21 (σ : St) : (rX (.Regno 21)).run σ = match xget σ 21 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x21 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_22 (σ : St) : (rX (.Regno 22)).run σ = match xget σ 22 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x22 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_23 (σ : St) : (rX (.Regno 23)).run σ = match xget σ 23 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x23 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_24 (σ : St) : (rX (.Regno 24)).run σ = match xget σ 24 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x24 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_25 (σ : St) : (rX (.Regno 25)).run σ = match xget σ 25 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x25 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_26 (σ : St) : (rX (.Regno 26)).run σ = match xget σ 26 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x26 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_27 (σ : St) : (rX (.Regno 27)).run σ = match xget σ 27 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x27 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_28 (σ : St) : (rX (.Regno 28)).run σ = match xget σ 28 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x28 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_29 (σ : St) : (rX (.Regno 29)).run σ = match xget σ 29 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x29 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_30 (σ : St) : (rX (.Regno 30)).run σ = match xget σ 30 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x30 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run_31 (σ : St) : (rX (.Regno 31)).run σ = match xget σ 31 with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  simp only [rX, xget, EStateM.run]
  cases h : σ.regs.get? Register.x31 <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, bind, pure, EStateM.pure, h, regval_from_reg]

theorem rX_run (σ : St) (n : Nat) (hn : n < 32) : (rX (.Regno n)).run σ = match xget σ n with
      | some v => .ok v σ
      | none => .error .Unreachable σ := by
  rcases lt32 n hn with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  · exact rX_run_0 σ
  · exact rX_run_1 σ
  · exact rX_run_2 σ
  · exact rX_run_3 σ
  · exact rX_run_4 σ
  · exact rX_run_5 σ
  · exact rX_run_6 σ
  · exact rX_run_7 σ
  · exact rX_run_8 σ
  · exact rX_run_9 σ
  · exact rX_run_10 σ
  · exact rX_run_11 σ
  · exact rX_run_12 σ
  · exact rX_run_13 σ
  · exact rX_run_14 σ
  · exact rX_run_15 σ
  · exact rX_run_16 σ
  · exact rX_run_17 σ
  · exact rX_run_18 σ
  · exact rX_run_19 σ
  · exact rX_run_20 σ
  · exact rX_run_21 σ
  · exact rX_run_22 σ
  · exact rX_run_23 σ
  · exact rX_run_24 σ
  · exact rX_run_25 σ
  · exact rX_run_26 σ
  · exact rX_run_27 σ
  · exact rX_run_28 σ
  · exact rX_run_29 σ
  · exact rX_run_30 σ
  · exact rX_run_31 σ

theorem reg_name_ok (σ : St) (r : regidx) :
    (reg_name_forwards r).run σ = .ok (reg_arch_name_raw_forwards (encdec_reg_forwards r)) σ := by
  simp [reg_name_forwards, encdec_reg_forwards_matches, get_config_use_abi_names, Functions.not,
    EStateM.run, pure, EStateM.pure]

theorem wX_run_0 (σ : St) (v : BitVec 64) : (wX (.Regno 0) v).run σ = .ok () (xset σ 0 v) := by
  simp [wX, xset, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg]

theorem wX_run_1 (σ : St) (v : BitVec 64) : (wX (.Regno 1) v).run σ = .ok () (xset σ 1 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x1 v } (.Regidx (to_bits (l := 5) 1))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_2 (σ : St) (v : BitVec 64) : (wX (.Regno 2) v).run σ = .ok () (xset σ 2 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x2 v } (.Regidx (to_bits (l := 5) 2))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_3 (σ : St) (v : BitVec 64) : (wX (.Regno 3) v).run σ = .ok () (xset σ 3 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x3 v } (.Regidx (to_bits (l := 5) 3))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_4 (σ : St) (v : BitVec 64) : (wX (.Regno 4) v).run σ = .ok () (xset σ 4 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x4 v } (.Regidx (to_bits (l := 5) 4))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_5 (σ : St) (v : BitVec 64) : (wX (.Regno 5) v).run σ = .ok () (xset σ 5 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x5 v } (.Regidx (to_bits (l := 5) 5))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_6 (σ : St) (v : BitVec 64) : (wX (.Regno 6) v).run σ = .ok () (xset σ 6 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x6 v } (.Regidx (to_bits (l := 5) 6))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_7 (σ : St) (v : BitVec 64) : (wX (.Regno 7) v).run σ = .ok () (xset σ 7 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x7 v } (.Regidx (to_bits (l := 5) 7))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_8 (σ : St) (v : BitVec 64) : (wX (.Regno 8) v).run σ = .ok () (xset σ 8 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x8 v } (.Regidx (to_bits (l := 5) 8))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_9 (σ : St) (v : BitVec 64) : (wX (.Regno 9) v).run σ = .ok () (xset σ 9 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x9 v } (.Regidx (to_bits (l := 5) 9))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_10 (σ : St) (v : BitVec 64) : (wX (.Regno 10) v).run σ = .ok () (xset σ 10 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x10 v } (.Regidx (to_bits (l := 5) 10))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_11 (σ : St) (v : BitVec 64) : (wX (.Regno 11) v).run σ = .ok () (xset σ 11 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x11 v } (.Regidx (to_bits (l := 5) 11))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_12 (σ : St) (v : BitVec 64) : (wX (.Regno 12) v).run σ = .ok () (xset σ 12 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x12 v } (.Regidx (to_bits (l := 5) 12))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_13 (σ : St) (v : BitVec 64) : (wX (.Regno 13) v).run σ = .ok () (xset σ 13 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x13 v } (.Regidx (to_bits (l := 5) 13))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_14 (σ : St) (v : BitVec 64) : (wX (.Regno 14) v).run σ = .ok () (xset σ 14 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x14 v } (.Regidx (to_bits (l := 5) 14))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_15 (σ : St) (v : BitVec 64) : (wX (.Regno 15) v).run σ = .ok () (xset σ 15 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x15 v } (.Regidx (to_bits (l := 5) 15))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_16 (σ : St) (v : BitVec 64) : (wX (.Regno 16) v).run σ = .ok () (xset σ 16 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x16 v } (.Regidx (to_bits (l := 5) 16))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_17 (σ : St) (v : BitVec 64) : (wX (.Regno 17) v).run σ = .ok () (xset σ 17 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x17 v } (.Regidx (to_bits (l := 5) 17))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_18 (σ : St) (v : BitVec 64) : (wX (.Regno 18) v).run σ = .ok () (xset σ 18 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x18 v } (.Regidx (to_bits (l := 5) 18))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_19 (σ : St) (v : BitVec 64) : (wX (.Regno 19) v).run σ = .ok () (xset σ 19 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x19 v } (.Regidx (to_bits (l := 5) 19))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_20 (σ : St) (v : BitVec 64) : (wX (.Regno 20) v).run σ = .ok () (xset σ 20 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x20 v } (.Regidx (to_bits (l := 5) 20))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_21 (σ : St) (v : BitVec 64) : (wX (.Regno 21) v).run σ = .ok () (xset σ 21 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x21 v } (.Regidx (to_bits (l := 5) 21))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_22 (σ : St) (v : BitVec 64) : (wX (.Regno 22) v).run σ = .ok () (xset σ 22 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x22 v } (.Regidx (to_bits (l := 5) 22))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_23 (σ : St) (v : BitVec 64) : (wX (.Regno 23) v).run σ = .ok () (xset σ 23 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x23 v } (.Regidx (to_bits (l := 5) 23))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_24 (σ : St) (v : BitVec 64) : (wX (.Regno 24) v).run σ = .ok () (xset σ 24 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x24 v } (.Regidx (to_bits (l := 5) 24))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_25 (σ : St) (v : BitVec 64) : (wX (.Regno 25) v).run σ = .ok () (xset σ 25 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x25 v } (.Regidx (to_bits (l := 5) 25))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_26 (σ : St) (v : BitVec 64) : (wX (.Regno 26) v).run σ = .ok () (xset σ 26 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x26 v } (.Regidx (to_bits (l := 5) 26))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_27 (σ : St) (v : BitVec 64) : (wX (.Regno 27) v).run σ = .ok () (xset σ 27 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x27 v } (.Regidx (to_bits (l := 5) 27))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_28 (σ : St) (v : BitVec 64) : (wX (.Regno 28) v).run σ = .ok () (xset σ 28 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x28 v } (.Regidx (to_bits (l := 5) 28))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_29 (σ : St) (v : BitVec 64) : (wX (.Regno 29) v).run σ = .ok () (xset σ 29 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x29 v } (.Regidx (to_bits (l := 5) 29))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_30 (σ : St) (v : BitVec 64) : (wX (.Regno 30) v).run σ = .ok () (xset σ 30 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x30 v } (.Regidx (to_bits (l := 5) 30))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run_31 (σ : St) (v : BitVec 64) : (wX (.Regno 31) v).run σ = .ok () (xset σ 31 v) := by
  have h := reg_name_ok { σ with regs := σ.regs.insert Register.x31 v } (.Regidx (to_bits (l := 5) 31))
  simp only [EStateM.run] at h
  simp [wX, xset, xreg_write_callback, h, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, PreSail.writeReg, regval_into_reg, Functor.map, EStateM.map]

theorem wX_run (σ : St) (n : Nat) (hn : n < 32) (v : BitVec 64) : (wX (.Regno n) v).run σ = .ok () (xset σ n v) := by
  rcases lt32 n hn with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  · exact wX_run_0 σ v
  · exact wX_run_1 σ v
  · exact wX_run_2 σ v
  · exact wX_run_3 σ v
  · exact wX_run_4 σ v
  · exact wX_run_5 σ v
  · exact wX_run_6 σ v
  · exact wX_run_7 σ v
  · exact wX_run_8 σ v
  · exact wX_run_9 σ v
  · exact wX_run_10 σ v
  · exact wX_run_11 σ v
  · exact wX_run_12 σ v
  · exact wX_run_13 σ v
  · exact wX_run_14 σ v
  · exact wX_run_15 σ v
  · exact wX_run_16 σ v
  · exact wX_run_17 σ v
  · exact wX_run_18 σ v
  · exact wX_run_19 σ v
  · exact wX_run_20 σ v
  · exact wX_run_21 σ v
  · exact wX_run_22 σ v
  · exact wX_run_23 σ v
  · exact wX_run_24 σ v
  · exact wX_run_25 σ v
  · exact wX_run_26 σ v
  · exact wX_run_27 σ v
  · exact wX_run_28 σ v
  · exact wX_run_29 σ v
  · exact wX_run_30 σ v
  · exact wX_run_31 σ v

/-- ADDI, for every immediate and every pair of registers: Sail's `execute` reads `x[rs1]`,
    writes `x[rs1] + sext imm` to `x[rd]` (dropped for `x0`), touches nothing else, and retires. -/
theorem addi_run (σ : St) (imm : BitVec 12) (rs1 rd : BitVec 5) (v : BitVec 64)
    (hv : xget σ rs1.toNat = some v) :
    (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .ADDI).run σ
      = .ok RETIRE_SUCCESS (xset σ rd.toNat (v + Sail.BitVec.signExtend imm 64)) := by
  have hr := rX_run σ rs1.toNat rs1.isLt
  have hw := wX_run σ rd.toNat rd.isLt (v + Sail.BitVec.signExtend imm 64)
  rw [hv] at hr
  simp only [EStateM.run] at hr hw
  simp [execute_ITYPE, rX_bits, wX_bits, BitVec.toNatInt, sign_extend, EStateM.run, bind,
    EStateM.bind, pure, EStateM.pure, hr, hw]

/-- BEQ with a 4-byte-aligned target (all the compiler emits): Sail's `execute` compares
    `x[rs1]` and `x[rs2]`; if equal it sets `nextPC` to `PC + sext imm`, else it changes nothing. -/
theorem beq_run (σ : St) (imm : BitVec 13) (rs1 rs2 : BitVec 5) (v1 v2 pc m : BitVec 64)
    (h1 : xget σ rs1.toNat = some v1) (h2 : xget σ rs2.toNat = some v2)
    (hpc : σ.regs.get? Register.PC = some pc) (hmisa : σ.regs.get? Register.misa = some m)
    (ha0 : (pc + Sail.BitVec.signExtend imm 64).getLsbD 0 = false)
    (ha1 : (pc + Sail.BitVec.signExtend imm 64).getLsbD 1 = false) :
    (execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) .BEQ).run σ
      = .ok RETIRE_SUCCESS (if v1 = v2 then
          { σ with regs := σ.regs.insert Register.nextPC (pc + Sail.BitVec.signExtend imm 64) }
        else σ) := by
  have hr1 := rX_run σ rs1.toNat rs1.isLt
  have hr2 := rX_run σ rs2.toNat rs2.isLt
  rw [h1] at hr1
  rw [h2] at hr2
  simp only [EStateM.run] at hr1 hr2
  by_cases hv : v1 = v2
  · simp [execute_BTYPE, rX_bits, BitVec.toNatInt, sign_extend, EStateM.run, bind, EStateM.bind,
      pure, EStateM.pure, hr1, hr2, hv, jump_to, ext_control_check_pc, currentlyEnabled,
      PreSail.readReg, hpc, hmisa, set_next_pc, PreSail.writeReg, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, get, getThe, MonadStateOf.get, EStateM.get,
      SailME.run, ha0, ha1, BitVec.access, PreSail.sail_assert, LeanRV64D.sail_assert,
      PreSail.PreSailME.run, ExceptT.run, ExceptT.pure, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, bit_to_bool,
      bool_bit_backwards, Functor.map, EStateM.map, ← BitVec.getLsbD_eq_getElem, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw]
  · simp [execute_BTYPE, rX_bits, BitVec.toNatInt, EStateM.run, bind, EStateM.bind, pure,
      EStateM.pure, hr1, hr2, hv]

end SSail
