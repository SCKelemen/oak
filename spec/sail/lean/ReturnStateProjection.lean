import ScalarExecutionBridge
import ReturnComposition
namespace Oak.SailBridge.StateProjection
open Sail PreSail
set_option linter.unusedSimpArgs false

def projectPstate (p : ReturnExecution.ProcState) : ScalarExecution.ProcState :=
 { N := p.N
   Z := p.Z
   C := p.C
   V := p.V
   D := p.D
   A := p.A
   I := p.I
   F := p.F
   PAN := p.PAN
   UAO := p.UAO
   DIT := p.DIT
   TCO := p.TCO
   BTYPE := p.BTYPE
   SS := p.SS
   IL := p.IL
   EL := p.EL
   nRW := p.nRW
   SP := p.SP
   Q := p.Q
   GE := p.GE
   SSBS := p.SSBS
   IT := p.IT
   J := p.J
   T := p.T
   E := p.E
   M := p.M }

structure Related (old : Scalar.State) (extended : Return.State) : Prop where
 bank : old.regs.get? ScalarExecution.Register._R = extended.regs.get? ReturnExecution.Register._R
 pstate : old.regs.get? ScalarExecution.Register.PSTATE =
   (extended.regs.get? ReturnExecution.Register.PSTATE).map projectPstate
 guarded : old.regs.get? ScalarExecution.Register.InGuardedPage = extended.regs.get? ReturnExecution.Register.InGuardedPage
 btype : old.regs.get? ScalarExecution.Register.BTypeNext = extended.regs.get? ReturnExecution.Register.BTypeNext
 unconditional : old.regs.get? ScalarExecution.Register.__unconditional = extended.regs.get? ReturnExecution.Register.__unconditional
 see : old.regs.get? ScalarExecution.Register.SEE = extended.regs.get? ReturnExecution.Register.SEE
 choice : old.choiceState = extended.choiceState
 memory : old.mem = extended.mem
 tags : old.tags = extended.tags
 cycles : old.cycleCount = extended.cycleCount
 output : old.sailOutput = extended.sailOutput

private def putOptional
 (m : Std.ExtDHashMap ScalarExecution.Register ScalarExecution.RegisterType)
 (r : ScalarExecution.Register) (v : Option (ScalarExecution.RegisterType r)) :=
 match v with
 | none => m
 | some value => m.insert r value

@[simp] private theorem optional_get_ne
 (m : Std.ExtDHashMap ScalarExecution.Register ScalarExecution.RegisterType)
 (r k : ScalarExecution.Register) (v : Option (ScalarExecution.RegisterType r)) (h : k ≠ r) :
 (putOptional m r v).get? k = m.get? k := by
 cases v <;> simp [putOptional, Std.ExtDHashMap.get?_insert, h, Ne.symm h]

@[simp] private theorem optional_get_self
 (m : Std.ExtDHashMap ScalarExecution.Register ScalarExecution.RegisterType)
 (r : ScalarExecution.Register) (v : Option (ScalarExecution.RegisterType r)) :
 (putOptional m r v).get? r = v.orElse (fun _ => m.get? r) := by
 cases v <;> simp [putOptional]

/-- Total projection, including absence of uninitialized registers. -/
def project (s : Return.State) : Scalar.State :=
 let regs := putOptional ∅ ._R (s.regs.get? ReturnExecution.Register._R)
 let regs := putOptional regs .PSTATE ((s.regs.get? ReturnExecution.Register.PSTATE).map projectPstate)
 let regs := putOptional regs .InGuardedPage (s.regs.get? ReturnExecution.Register.InGuardedPage)
 let regs := putOptional regs .BTypeNext (s.regs.get? ReturnExecution.Register.BTypeNext)
 let regs := putOptional regs .__unconditional (s.regs.get? ReturnExecution.Register.__unconditional)
 let regs := putOptional regs .SEE (s.regs.get? ReturnExecution.Register.SEE)
 ⟨regs, s.choiceState, s.mem, s.tags, s.cycleCount, s.sailOutput⟩

theorem project_related (s : Return.State) : Related (project s) s := by
 constructor <;> simp [project]

theorem related_unique (a b : Scalar.State) (s : Return.State)
 (ha : Related a s) (hb : Related b s) : a = b := by
 have regs : a.regs = b.regs := by
  apply Std.ExtDHashMap.ext_get?
  intro r
  cases r
  · exact ha.see.trans hb.see.symm
  · exact ha.unconditional.trans hb.unconditional.symm
  · exact ha.btype.trans hb.btype.symm
  · exact ha.guarded.trans hb.guarded.symm
  · exact ha.pstate.trans hb.pstate.symm
  · exact ha.bank.trans hb.bank.symm
 have hc := ha.choice.trans hb.choice.symm
 have hm := ha.memory.trans hb.memory.symm
 have ht := ha.tags.trans hb.tags.symm
 have hy := ha.cycles.trans hb.cycles.symm
 have ho := ha.output.trans hb.output.symm
 cases a
 cases b
 simp_all

private theorem bank_same (op : Oak.BitwiseFunction.Op) (bank : Scalar.Bank) :
 Scalar.updatedBank (Scalar.externalOp op) bank = ExtendedScalar.updatedBank (ExtendedScalar.externalOp op) bank := by
 cases op <;> rfl

theorem requests_related (old : Scalar.State) (extended : Return.State)
 (h : Related old extended) (op : Oak.BitwiseFunction.Op) (bank : Scalar.Bank) :
 Related (Scalar.requestState op old bank) (ExtendedScalar.requestState op extended bank) := by
 constructor <;>
 simp [Scalar.requestState, Scalar.retControlState, Scalar.afterLogical, Scalar.logicalControlState, Scalar.put,
 ExtendedScalar.requestState, ExtendedScalar.retControlState, ExtendedScalar.afterLogical,
 ExtendedScalar.logicalControlState, ExtendedScalar.put, bank_same, h.pstate, h.guarded,
 h.choice, h.memory, h.tags, h.cycles, h.output, Std.ExtDHashMap.get?_insert]

theorem final_related (old : Scalar.State) (extended : Return.State)
 (h : Related old extended) (op : Oak.BitwiseFunction.Op) (bank : Scalar.Bank) :
 Related (Scalar.requestState op old bank) (ConcreteReturn.finalState op extended bank) := by
 have req := requests_related old extended h op bank
 constructor
 · simpa [ConcreteReturn.finalState, Return.put, Std.ExtDHashMap.get?_insert] using req.bank
 · simpa [ConcreteReturn.finalState, Return.put, Std.ExtDHashMap.get?_insert] using req.pstate
 · simpa [ConcreteReturn.finalState, Return.put, Std.ExtDHashMap.get?_insert] using req.guarded
 · simpa [ConcreteReturn.finalState, Return.put, Std.ExtDHashMap.get?_insert] using req.btype
 · simpa [ConcreteReturn.finalState, Return.put, Std.ExtDHashMap.get?_insert] using req.unconditional
 · simpa [ConcreteReturn.finalState, Return.put, Std.ExtDHashMap.get?_insert] using req.see
 · exact req.choice
 · exact req.memory
 · exact req.tags
 · exact req.cycles
 · exact req.output

theorem project_final (s : Return.State) (op : Oak.BitwiseFunction.Op) (bank : Scalar.Bank) :
 project (ConcreteReturn.finalState op s bank) = Scalar.requestState op (project s) bank := by
 apply related_unique _ _ (ConcreteReturn.finalState op s bank)
 · exact project_related _
 · exact final_related _ _ (project_related s) op bank

#print axioms project_final
#print axioms project_related
#print axioms requests_related
#print axioms final_related
end Oak.SailBridge.StateProjection
