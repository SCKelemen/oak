import Oak.CNFWordInput

/-!
# Independent read words in the checked input allocation

Scalar bits retain their production interleaved source identities. The eight
reserved positions and overflow blocks denote independent 32-bit read words,
rather than false. The canonical assignment is derived from the checked
source/output inverse. This establishes input binding, not read-class syntax
or concrete-memory embedding; those belong to the typed graph layer.
-/

set_option autoImplicit false

namespace Oak.CNFTypedReadInput

open Oak.RupCheck Oak.TseitinCNF Oak.CNFDenseAllocation
open Oak.CNFReplayTerm Oak.CNFWordInput

abbrev Reads := Nat → BitVec 32

def readSource (parameters slot bit : Nat) : Nat :=
  if slot < 8 then bit * (parameters + 8) + parameters + slot
  else 64 * (parameters + 8) + 64 * (slot - 8) + bit

/-- The overflow layout uses full 64-position blocks although this profile
admits only 32-bit reads. Unused positions are false. -/
def sourceBit (parameters : List Parameter) (inputs : Inputs) (reads : Reads)
    (source : Nat) : Bool :=
  let stride := parameters.length + 8
  if source / stride < 64 then
    if source % stride < parameters.length then
      Oak.CNFWordInput.sourceBit parameters inputs source
    else if source / stride < 32 then
      (reads (source % stride - parameters.length)).getLsbD (source / stride)
    else false
  else
    let offset := source - 64 * stride
    if offset % 64 < 32 then
      (reads (offset / 64 + 8)).getLsbD (offset % 64)
    else false

def initialAssignment (snapshot : Snapshot) (parameters : List Parameter)
    (inputs : Inputs) (reads : Reads) : Assignment := fun output =>
  match lookupSource? snapshot.inputs output with
  | none => false
  | some source => sourceBit parameters inputs reads source

theorem sourceBit_read (parameters : List Parameter) (inputs : Inputs) (reads : Reads)
    (slot bit : Nat) (within : bit < 32) :
    sourceBit parameters inputs reads (readSource parameters.length slot bit) =
      (reads slot).getLsbD bit := by
  have stridePositive : 0 < parameters.length + 8 := by omega
  by_cases early : slot < 8
  · have positionBound : parameters.length + slot < parameters.length + 8 := by omega
    have quotient :
        (bit * (parameters.length + 8) + (parameters.length + slot)) /
          (parameters.length + 8) = bit := by
      rw [Nat.mul_comm bit (parameters.length + 8), Nat.mul_add_div stridePositive]
      simp [Nat.div_eq_of_lt positionBound]
    have remainder :
        (bit * (parameters.length + 8) + (parameters.length + slot)) %
          (parameters.length + 8) = parameters.length + slot := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt positionBound]
    simp [sourceBit, readSource, early, Nat.add_assoc, quotient, remainder,
      Nat.not_lt_of_ge (Nat.le_add_right parameters.length slot), within, (by omega : bit < 64)]
  · have beyond :
        64 ≤ (64 * (parameters.length + 8) + 64 * (slot - 8) + bit) /
          (parameters.length + 8) := by
      apply (Nat.le_div_iff_mul_le stridePositive).mpr
      omega
    have offset :
        64 * (parameters.length + 8) + 64 * (slot - 8) + bit -
          64 * (parameters.length + 8) = 64 * (slot - 8) + bit := by omega
    have quotient : (64 * (slot - 8) + bit) / 64 = slot - 8 := by
      rw [Nat.mul_add_div (by decide : 0 < 64)]
      simp [Nat.div_eq_of_lt (by omega : bit < 64)]
    have remainder : (64 * (slot - 8) + bit) % 64 = bit := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : bit < 64)]
    have slotEq : slot - 8 + 8 = slot := by omega
    simp [sourceBit, readSource, early, Nat.not_lt_of_ge beyond,
      offset, quotient, remainder, slotEq, within]

theorem sourceBit_parameter {parameters : List Parameter} {position : Nat}
    {parameter : Parameter} (atIndex : parameters[position]? = some parameter)
    (bounded : position < parameters.length) (inputs : Inputs) (reads : Reads)
    (bit : Nat) (bitBound : bit < 64) :
    sourceBit parameters inputs reads (bit * (parameters.length + 8) + position) =
      if bit < parameter.width then (inputs parameter.name).getLsbD bit else false := by
  have stridePositive : 0 < parameters.length + 8 := by omega
  have positionBound : position < parameters.length + 8 := by omega
  have quotient :
      (bit * (parameters.length + 8) + position) / (parameters.length + 8) = bit := by
    rw [Nat.mul_comm bit (parameters.length + 8), Nat.mul_add_div stridePositive]
    simp [Nat.div_eq_of_lt positionBound]
  have remainder :
      (bit * (parameters.length + 8) + position) % (parameters.length + 8) = position := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt positionBound]
  simp only [sourceBit, quotient, bitBound, if_true, remainder, bounded]
  exact Oak.CNFWordInput.sourceBit_of_position atIndex bounded inputs bit

def projectReadBit (snapshot : Snapshot) (parameters maxInt slot bit : Nat) : Option Term :=
  if bit < 32 then
    let source := readSource parameters slot bit
    if source ≤ maxInt then
      match lookupInput? snapshot.inputs source with
      | none => none
      | some output =>
          if 0 < output ∧ output ≤ snapshot.variables ∧ output ≤ maxInt / 2 then
            some (.input output)
          else none
    else none
  else some (.constant false)

theorem projectReadBit_sound {snapshot : Snapshot} {gates : List RawGate}
    {parameters : List Parameter} {maxInt slot bit : Nat} {term : Term}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (projected : projectReadBit snapshot parameters.length maxInt slot bit = some term)
    (inputs : Inputs) (reads : Reads) :
    term.eval (initialAssignment snapshot parameters inputs reads) =
      (reads slot).getLsbD bit := by
  unfold projectReadBit at projected
  split at projected
  · rename_i within
    dsimp only at projected
    split at projected
    · cases found : lookupInput? snapshot.inputs (readSource parameters.length slot bit) with
      | none => simp [found] at projected
      | some output =>
          simp only [found] at projected
          split at projected
          · cases Option.some.inj projected
            simp only [Term.eval, initialAssignment, check_lookupSource_inverse accepted found]
            exact sourceBit_read parameters inputs reads slot bit within
          · contradiction
    · contradiction
  · rename_i outside
    cases Option.some.inj projected
    simp [Term.eval, BitVec.getLsbD_of_ge (reads slot) bit (Nat.le_of_not_gt outside)]

/-- Input lookup, accepted allocation and constructive gate evaluation
supply the bit's actual source value, including read slots. -/
theorem input_edge_meaning {snapshot : Snapshot} {gates : List RawGate}
    {source output : Nat} (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (found : lookupInput? snapshot.inputs source = some output) (positive : 0 < output)
    (parameters : List Parameter) (inputs : Inputs) (reads : Reads) :
    Oak.CNFReplayApply.evalEdge
      (evalSequence gates (initialAssignment snapshot parameters inputs reads)) (2 * output) =
        sourceBit parameters inputs reads source := by
  rw [Oak.CNFReplayApply.evalEdge_positive _ output positive]
  have member : output ∈ inputOutputs snapshot := by
    exact List.mem_map.mpr ⟨⟨source, output⟩, lookupInput?_mem found, rfl⟩
  rw [check_input_stable accepted _ member]
  simp [initialAssignment, check_lookupSource_inverse accepted found]

end Oak.CNFTypedReadInput
