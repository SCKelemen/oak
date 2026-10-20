import Oak.AArch64ControlFlow

/-!
# Register comparison to materialized Bool to branch

The full-width, register-resident OptIR comparison slice: unshifted CMP W/X,
CSET W (CSINC Wd, WZR, WZR with the inverse condition), then a certified
Boolean terminator. Decoding is independent of packing. NZCV uses the existing
Sail-connected ArmASL subtraction primitive. The theorem allows the Bool
destination to alias either comparison input, but refuses destination ZR.

This is a no-fault projected execution model, not the full Arm fetch loop.
Input register provenance, narrow-value normalization, spills, edge copies,
and universal correspondence of the Go compiler remain separate obligations.
-/

namespace Oak.AArch64ConditionProvenance

open Oak.AssemblerSemantics (Flags Cond flagsOf condHolds)
open Oak.AArch64BranchExecution
open Oak.AArch64ControlFlow

inductive Width | w32 | x64 deriving DecidableEq, Repr
def Width.bits : Width → Nat | .w32 => 32 | .x64 => 64

inductive Compare | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr

def Compare.condition : Compare → Cond
  | .eq => .eq | .ne => .ne | .ult => .lo | .ule => .ls | .ugt => .hi | .uge => .hs
  | .slt => .lt | .sle => .le | .sgt => .gt | .sge => .ge

def predicate {w : Nat} (op : Compare) (a b : BitVec w) : Bool :=
  match op with
  | .eq => a == b | .ne => !(a == b)
  | .ult => a.ult b | .ule => !(b.ult a) | .ugt => b.ult a | .uge => !(a.ult b)
  | .slt => a.slt b | .sle => !(b.slt a) | .sgt => b.slt a | .sge => !(a.slt b)

def operand (width : Width) (regs : Registers) (r : BitVec 5) : BitVec width.bits :=
  (readX regs r).truncate width.bits

theorem flags_predicate (width : Width) (op : Compare) (a b : BitVec width.bits) :
    op.condition.holds (Oak.ArmASL.subFlags a b) = predicate op a b := by
  rw [Oak.ArmASL.subFlags_eq_flagsOf (by cases width <;> decide)]
  cases width <;> simp only [Width.bits] at a b ⊢ <;> cases op <;>
    simp only [Compare.condition, predicate, Cond.holds, flagsOf, ← BitVec.ule_eq_decide] <;> bv_decide

def cmpWord (width : Width) (rn rm : BitVec 5) : BitVec 32 :=
  (match width with | .w32 => 0x6b00001f | .x64 => 0xeb00001f) |||
    (rm.zeroExtend 32 <<< 16) ||| (rn.zeroExtend 32 <<< 5)

def csetWord (op : Compare) (rd : BitVec 5) : BitVec 32 :=
  0x1a9f07e0#32 ||| (((Oak.ArmASL.Cond.encode op.condition) ^^^ 1#4).zeroExtend 32 <<< 12) |||
    rd.zeroExtend 32

def decodeCmp (word : BitVec 32) : Option (Width × BitVec 5 × BitVec 5) :=
  let rn := word.extractLsb' 5 5
  let rm := word.extractLsb' 16 5
  if word &&& 0xffe0fc1f#32 == 0x6b00001f#32 then some (.w32, rn, rm)
  else if word &&& 0xffe0fc1f#32 == 0xeb00001f#32 then some (.x64, rn, rm)
  else none

/-- Restricted CSINC row; the actual encoded condition is consumed directly. -/
def decodeSet (word : BitVec 32) : Option (BitVec 5 × BitVec 4) :=
  if word &&& 0xffff0fe0#32 == 0x1a9f07e0#32 then
    some (word.extractLsb' 0 5, word.extractLsb' 12 4)
  else none

theorem decode_cmpWord (width : Width) (rn rm : BitVec 5) :
    decodeCmp (cmpWord width rn rm) = some (width, rn, rm) := by
  have fields : (cmpWord width rn rm).extractLsb' 5 5 = rn ∧
      (cmpWord width rn rm).extractLsb' 16 5 = rm := by
    cases width <;> simp only [cmpWord] <;> bv_decide
  have tag : cmpWord width rn rm &&& 0xffe0fc1f#32 =
      (match width with | .w32 => 0x6b00001f | .x64 => 0xeb00001f) := by
    cases width <;> simp only [cmpWord] <;> bv_decide
  simp only [decodeCmp, fields.1, fields.2, tag]
  cases width <;> rfl

theorem decode_csetWord (op : Compare) (rd : BitVec 5) :
    decodeSet (csetWord op rd) = some (rd, Oak.ArmASL.Cond.encode op.condition ^^^ 1#4) := by
  have htag : csetWord op rd &&& 0xffff0fe0#32 = 0x1a9f07e0#32 := by
    unfold csetWord; bv_decide
  have hd : (csetWord op rd).extractLsb' 0 5 = rd := by unfold csetWord; bv_decide
  have hc : (csetWord op rd).extractLsb' 12 4 = Oak.ArmASL.Cond.encode op.condition ^^^ 1#4 := by
    unfold csetWord; bv_decide
  simp [decodeSet, htag, hd, hc]

theorem inverse_condition (c : Cond) (flags : Flags) :
    Oak.ArmASL.ConditionHolds (Oak.ArmASL.Cond.encode c ^^^ 1#4) flags = !(c.holds flags) := by
  obtain ⟨n,z,cf,v⟩ := flags
  cases c <;> cases n <;> cases z <;> cases cf <;> cases v <;> rfl

def writeW (regs : Registers) (rd : BitVec 5) (value : BitVec 32) : Registers :=
  fun r => if rd != 31#5 && r == rd then value.zeroExtend 64 else regs r

theorem writeW_other (regs : Registers) (rd r : BitVec 5) (v : BitVec 32) (h : r ≠ rd) :
    writeW regs rd v r = regs r := by simp [writeW, h]

def compareState (width : Width) (rn rm : BitVec 5) (s : State) : State :=
  { s with pc := s.pc + 4, flags := Oak.ArmASL.subFlags (operand width s.regs rn) (operand width s.regs rm) }

def setState (rd : BitVec 5) (encodedCondition : BitVec 4) (s : State) : State :=
  { s with pc := s.pc + 4,
           regs := writeW s.regs rd (Oak.ArmASL.conditionalSelect encodedCondition s.flags true false (0#32) (0#32)) }

def stepCmp (word : BitVec 32) (s : State) : Option State :=
  (decodeCmp word).map fun (width, rn, rm) => compareState width rn rm s

def stepSet (word : BitVec 32) (s : State) : Option State :=
  (decodeSet word).map fun (rd, code) => setState rd code s

def prepare (cmp set : BitVec 32) (s : State) : Option State := do
  let s' ← stepCmp cmp s
  stepSet set s'

def sourceValue (width : Width) (op : Compare) (rn rm : BitVec 5) (s : State) : Bool :=
  predicate op (operand width s.regs rn) (operand width s.regs rm)

def produced (width : Width) (op : Compare) (rn rm rd : BitVec 5) (s : State) : State :=
  { pc := s.pc + 8, flags := (compareState width rn rm s).flags,
    regs := writeW s.regs rd (if sourceValue width op rn rm s then 1 else 0) }

theorem prepare_encoded (width : Width) (op : Compare) (rn rm rd : BitVec 5) (s : State) :
    prepare (cmpWord width rn rm) (csetWord op rd) s = some (produced width op rn rm rd s) := by
  simp only [prepare, stepCmp, stepSet, decode_cmpWord, decode_csetWord, Option.map_some,
    Bind.bind, Option.bind, compareState, setState, Oak.ArmASL.conditionalSelect, inverse_condition,
    flags_predicate, produced, sourceValue]
  by_cases hv : predicate op (operand width s.regs rn) (operand width s.regs rm) = true <;>
    simp [hv, BitVec.add_assoc]

/-- Establish the previous routing theorem's Bool-register invariant. The
comparison reads the original inputs even when rd aliases rn or rm. -/
theorem produced_bool (width : Width) (op : Compare) (rn rm rd : BitVec 5) (s : State)
    (hd : rd ≠ 31#5) :
    boolValue (produced width op rn rm rd s).regs rd = sourceValue width op rn rm s := by
  cases hv : sourceValue width op rn rm s <;>
    simp [produced, boolValue, readX, writeW, hd, hv]

def checkProducer (width : Width) (op : Compare) (rn rm rd : BitVec 5) (cmp set : BitVec 32) : Bool :=
  rd != 31#5 && cmp == cmpWord width rn rm && set == csetWord op rd

theorem checked_prepare (width : Width) (op : Compare) (rn rm rd : BitVec 5)
    (cmp set : BitVec 32) (h : checkProducer width op rn rm rd cmp set = true) (s : State) :
    prepare cmp set s = some (produced width op rn rm rd s) ∧
    boolValue (produced width op rn rm rd s).regs rd = sourceValue width op rn rm s := by
  simp only [checkProducer, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  rcases h with ⟨⟨hd, hc⟩, hs⟩
  subst cmp; subst set
  exact ⟨prepare_encoded width op rn rm rd s, produced_bool width op rn rm rd s hd⟩

/-- The composed comparison/CSET/terminator no longer assumes that the
tested register represents the comparison: the prefix establishes it. -/
theorem checked_comparison_successor (width : Width) (op : Compare) (rn rm rd : BitVec 5)
    (cmp set : BitVec 32) (yes no : Nat) (next : Option Nat) (addr : Nat → BitVec 64)
    (words : List (BitVec 32)) (s : State)
    (hp : checkProducer width op rn rm rd cmp set = true)
    (hb : check yes no next (s.pc + 8) addr rd words = true) :
    (prepare cmp set s >>= fun s' => run words s') =
      some { produced width op rn rm rd s with
        pc := if sourceValue width op rn rm s then addr yes else addr no } := by
  have h := checked_prepare width op rn rm rd cmp set hp s
  rw [h.1]
  simp only [Bind.bind, Option.bind]
  have route := checked_successor yes no next (s.pc + 8) addr rd words hb
    (produced width op rn rm rd s).flags (produced width op rn rm rd s).regs
  rw [h.2] at route
  exact route

end Oak.AArch64ConditionProvenance
