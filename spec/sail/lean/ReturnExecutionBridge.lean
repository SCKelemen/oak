import ReturnExecution
import Std.Data.ExtDHashMap.Lemmas
namespace Oak.SailBridge.Return
open ReturnExecution ReturnExecution.Functions Sail PreSail
set_option linter.unusedSimpArgs false
abbrev State := PreSail.SequentialState ReturnExecution.RegisterType Sail.trivialChoiceSource
def ReturnsOnly {α : Type} (p : α → Prop) (m : SailM α) : Prop :=
 ∀ s v s', m.run s = .ok v s' → p v
private theorem returns_bind {α β : Type} (p : β → Prop)
 (m : SailM α) (k : α → SailM β) (h : ∀ a, ReturnsOnly p (k a)) :
 ReturnsOnly p (m >>= k) := by
 intro s v s' run
 cases hm : m s with
 | ok a next => exact h a next v s' (by simpa [EStateM.run, Bind.bind, EStateM.bind, hm] using run)
 | error e next => simp [EStateM.run, Bind.bind, EStateM.bind, hm] at run
private theorem returns_pure {α : Type} (p : α → Prop) (v : α) (h : p v) :
 ReturnsOnly p (pure v) := by
 intro s w s' run
 cases run
 exact h

set_option maxHeartbeats 1000000 in
theorem addrTop_result_range (b : Boundaries) (address : BitVec 64) (instr : Bool) (el : BitVec 2) :
 ReturnsOnly (fun v => v = 31 ∨ v = 55 ∨ v = 63) (AddrTop b address instr el) := by
 unfold AddrTop
 apply returns_bind; intro haveEL
 apply returns_bind; intro checked
 apply returns_bind; intro regime
 apply returns_bind; intro tbi
 apply returns_bind; intro tbid
 apply returns_bind; intro a32
 split
 · apply returns_pure; simp
 · apply returns_bind; rintro ⟨tbi, tbid⟩
   apply returns_bind; intro pac
   split
   · apply returns_pure; simp
   · apply returns_pure; simp


structure QueryProfile (b : Boundaries) : Prop where
 haveEL : b.HaveEL EL1 = pure true
 regime : b.S1TranslationRegime__0 EL1 = pure EL1
 a32 : b.ELUsingAArch32 EL1 = pure false
 pac : b.HavePACExt () = pure false
 usingA32 : b.UsingAArch32 () = pure false

def put (s : State) (r : ReturnExecution.Register) (v : ReturnExecution.RegisterType r) : State :=
 {s with regs := s.regs.insert r v}
private theorem undefined_bits_eq (width : Nat) :
 (PreSail.undefined_bitvector width : SailM (BitVec width)) = pure (0 : BitVec width) := by
 funext state
 have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
 change EStateM.Result.ok (0 : BitVec width) {state with choiceState := ()} = .ok _ state
 rw [← hc]

theorem addrTop_el1_no_tags (b : Boundaries) (q : QueryProfile b) (s : State)
 (tcr : s.regs.get? ReturnExecution.Register.TCR_EL1 = some (0 : BitVec 64))
 (address : BitVec 64) :
 (AddrTop b address true EL1).run s = .ok 63 s := by
 by_cases h : BitVec.join1 [BitVec.access address 55] = (1#1 : BitVec 1)
 all_goals simp +decide [h, AddrTop, q.haveEL, q.regime, q.a32, q.pac, undefined_bits_eq,
 readReg, PreSail.assert, tcr, EStateM.run,
 Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, MonadStateOf.get,
 EStateM.get, MonadState.get, getThe]

theorem branchAddr_el1_no_tags (b : Boundaries) (q : QueryProfile b) (s : State)
 (ps : ProcState) (pstate : s.regs.get? ReturnExecution.Register.PSTATE = some ps)
 (el : ps.EL = EL1)
 (tcr : s.regs.get? ReturnExecution.Register.TCR_EL1 = some (0 : BitVec 64))
 (address : BitVec 64) :
 (AArch64_BranchAddr b address).run s = .ok address s := by
 have top : AddrTop b address true EL1 s = .ok 63 s := addrTop_el1_no_tags b q s tcr address
 simp +decide [AArch64_BranchAddr, q.usingA32, pstate, el, top, readReg,
 PreSail.assert, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe]

theorem branchTo64_el1_no_tags (b : Boundaries) (q : QueryProfile b) (s : State)
 (ps : ProcState) (pstate : s.regs.get? ReturnExecution.Register.PSTATE = some ps)
 (el : ps.EL = EL1)
 (tcr : s.regs.get? ReturnExecution.Register.TCR_EL1 = some (0 : BitVec 64))
 (address : BitVec 64) (kind : BranchType) :
 (BranchTo b address kind).run s =
 .ok () (put (put s ._PC address) .__PC_changed true) := by
 have sliced : BitVec.slice address 0 64 = address := by simp [BitVec.slice]
 have branch : AArch64_BranchAddr b address s = .ok address s :=
  branchAddr_el1_no_tags b q s ps pstate el tcr address
 simp +decide [BranchTo, Hint_Branch, q.usingA32, Sail.BitVec.length, sliced,
 branch, put, PreSail.assert, writeReg, EStateM.run, Bind.bind, Pure.pure,
 EStateM.bind, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- A failed architectural mode query retains its complete returned state. -/
theorem branchTo64_query_failure (b : Boundaries) (s after : State)
 (err : Sail.Error ReturnExecution.exception) (target : BitVec 64) (kind : BranchType)
 (failed : (b.UsingAArch32 ()).run s = .error err after) :
 (BranchTo b target kind).run s = .error err after := by
 simp [BranchTo, Hint_Branch, Sail.BitVec.length, EStateM.run,
 Bind.bind, Pure.pure, EStateM.bind, EStateM.pure] at failed ⊢
 rw [failed]

#print axioms branchTo64_query_failure
#print axioms addrTop_result_range
#print axioms addrTop_el1_no_tags
#print axioms branchAddr_el1_no_tags
#print axioms branchTo64_el1_no_tags
end Oak.SailBridge.Return
