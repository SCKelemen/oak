import Oak.CNFReplayTerm

/-!
# Named parameter bits and checked CNF input allocation

The narrow native replay numbers parameter bits as
`bit * (parameters.length + 8) + position`.  This module projects one such
bit into the Boolean replay language and constructs its initial assignment
by reversing the checked input allocation.  Accepted allocation makes that
reverse lookup exact; no semantic input-binding premise is assumed.

Parameter lists model already projected Go tables, including their order.
This does not prove that arbitrary Go tables or term fields project faithfully.
The natural-number model explicitly checks `position ≤ maxInt` before
subtraction. With an artificial maximum smaller than an allocated parameter
position this can refuse earlier than Go's signed, truncating division; actual
Go list positions fit the machine integer. List/stride representation and
negative Go fields remain obligations at the projection boundary.
-/

set_option autoImplicit false

namespace Oak.CNFWordInput

open Oak.CNFDenseAllocation Oak.CNFReplayTerm Oak.RupCheck Oak.TseitinCNF

structure Parameter where
  name : String
  width : Nat
  deriving Repr, DecidableEq

abbrev Inputs := String → BitVec 64

def parametersValid (parameters : List Parameter) : Bool :=
  decide (parameters.map Parameter.name).Nodup &&
    parameters.all fun parameter =>
      decide (parameter.name ≠ "" ∧ 1 ≤ parameter.width ∧ parameter.width ≤ 64)

def lookupParameter? : List Parameter → String → Option (Nat × Parameter)
  | [], _ => none
  | parameter :: rest, name =>
      if parameter.name = name then some (0, parameter)
      else (lookupParameter? rest name).map fun result => (result.1 + 1, result.2)

def lookupInput? : List InputAllocation → Nat → Option Nat
  | [], _ => none
  | allocation :: rest, source =>
      if allocation.source = source then some allocation.output
      else lookupInput? rest source

def lookupSource? : List InputAllocation → Nat → Option Nat
  | [], _ => none
  | allocation :: rest, output =>
      if allocation.output = output then some allocation.source
      else lookupSource? rest output

def projectInputBit (snapshot : Snapshot) (parameters : List Parameter)
    (maxInt : Nat) (name : String) (declared bit : Nat) : Option Term :=
  if parametersValid parameters then
    match lookupParameter? parameters name with
    | none => none
    | some (position, parameter) =>
        if parameter.width = declared then
          if bit < declared then
            let stride := parameters.length + 8
            if position ≤ maxInt ∧ bit ≤ (maxInt - position) / stride then
              match lookupInput? snapshot.inputs (bit * stride + position) with
              | none => none
              | some output =>
                  if 0 < output ∧ output ≤ snapshot.variables ∧ output ≤ maxInt / 2 then
                    some (.input output)
                  else none
            else none
          else some (.constant false)
        else none
  else none

/-- Decode one interleaved source key. Reserved select slots, unrecognized
positions, and bits outside the parameter's declaration all denote false. -/
def sourceBit (parameters : List Parameter) (inputs : Inputs) (source : Nat) : Bool :=
  let stride := parameters.length + 8
  match parameters[source % stride]? with
  | none => false
  | some parameter =>
      if source / stride < parameter.width then
        (inputs parameter.name).getLsbD (source / stride)
      else false

def initialAssignment (snapshot : Snapshot) (parameters : List Parameter)
    (inputs : Inputs) : Assignment := fun output =>
  match lookupSource? snapshot.inputs output with
  | none => false
  | some source => sourceBit parameters inputs source

theorem lookupParameter?_at {parameters : List Parameter} {name : String}
    {position : Nat} {parameter : Parameter}
    (found : lookupParameter? parameters name = some (position, parameter)) :
    parameters[position]? = some parameter ∧ parameter.name = name ∧
      position < parameters.length := by
  induction parameters generalizing position with
  | nil => simp [lookupParameter?] at found
  | cons head rest induction =>
      simp only [lookupParameter?] at found
      split at found
      · have equal := Option.some.inj found
        have positionEq := congrArg Prod.fst equal
        have parameterEq := congrArg Prod.snd equal
        simp only at positionEq parameterEq
        subst position
        subst parameter
        simp_all
      · cases tail : lookupParameter? rest name with
        | none => simp [tail] at found
        | some result =>
            rcases result with ⟨tailPosition, tailParameter⟩
            simp only [tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨positionEq, parameterEq⟩ := found
            subst position
            subst parameter
            obtain ⟨atIndex, named, bounded⟩ := induction tail
            exact ⟨by simpa using atIndex, named, by simp; omega⟩

theorem lookupInput?_mem {allocations : List InputAllocation} {source output : Nat}
    (found : lookupInput? allocations source = some output) :
    (⟨source, output⟩ : InputAllocation) ∈ allocations := by
  induction allocations with
  | nil => simp [lookupInput?] at found
  | cons allocation rest induction =>
      simp only [lookupInput?] at found
      split at found
      · have sourceEq : allocation.source = source := by assumption
        have outputEq : allocation.output = output := Option.some.inj found
        have allocationEq : allocation = ⟨source, output⟩ := by
          cases allocation
          simp_all
        exact List.mem_cons.mpr (Or.inl allocationEq.symm)
      · exact List.mem_cons_of_mem _ (induction found)

theorem lookupSource?_of_mem {allocations : List InputAllocation}
    (unique : (allocations.map InputAllocation.output).Nodup)
    {allocation : InputAllocation} (member : allocation ∈ allocations) :
    lookupSource? allocations allocation.output = some allocation.source := by
  induction allocations with
  | nil => contradiction
  | cons head rest induction =>
      have separated := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | tailMember
      · simp [lookupSource?]
      · have different : head.output ≠ allocation.output := by
          intro equal
          apply separated.1
          exact equal ▸ List.mem_map.mpr ⟨allocation, tailMember, rfl⟩
        simp only [lookupSource?, different, if_false]
        exact induction separated.2 tailMember

/-- Checked input-output injectivity supplies the inverse source key. -/
theorem check_lookupSource_inverse {snapshot : Snapshot} {gates : List RawGate}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    {source output : Nat}
    (found : lookupInput? snapshot.inputs source = some output) :
    lookupSource? snapshot.inputs output = some source := by
  have unique : (snapshot.inputs.map InputAllocation.output).Nodup :=
    (List.nodup_append.mp (check_accepted accepted).shape.outputUnique).1
  exact lookupSource?_of_mem unique (lookupInput?_mem found)

theorem sourceBit_of_position {parameters : List Parameter} {position : Nat}
    {parameter : Parameter}
    (atIndex : parameters[position]? = some parameter)
    (bounded : position < parameters.length) (inputs : Inputs) (bit : Nat) :
    sourceBit parameters inputs (bit * (parameters.length + 8) + position) =
      if bit < parameter.width then (inputs parameter.name).getLsbD bit else false := by
  have positionBound : position < parameters.length + 8 := by omega
  have stridePositive : 0 < parameters.length + 8 := by omega
  have remainder : (bit * (parameters.length + 8) + position) % (parameters.length + 8) =
      position := by simp [Nat.add_mod, Nat.mod_eq_of_lt positionBound]
  have quotient : (bit * (parameters.length + 8) + position) / (parameters.length + 8) =
      bit := by
        rw [Nat.mul_comm bit (parameters.length + 8), Nat.mul_add_div stridePositive]
        simp [Nat.div_eq_of_lt positionBound]
  simp [sourceBit, remainder, quotient, atIndex]

/-- A successful named-bit projection reads exactly that parameter bit at
the canonical assignment obtained from the accepted shared allocation. -/
theorem projectInputBit_sound {snapshot : Snapshot} {gates : List RawGate}
    {parameters : List Parameter} {maxInt : Nat} {name : String}
    {declared bit : Nat} {term : Term}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (projected : projectInputBit snapshot parameters maxInt name declared bit = some term)
    (inputs : Inputs) :
    term.eval (initialAssignment snapshot parameters inputs) =
      if bit < declared then (inputs name).getLsbD bit else false := by
  unfold projectInputBit at projected
  split at projected
  · cases foundParameter : lookupParameter? parameters name with
    | none => simp [foundParameter] at projected
    | some result =>
        rcases result with ⟨position, parameter⟩
        simp only [foundParameter] at projected
        split at projected
        · rename_i widthEqual
          split at projected
          · rename_i inWidth
            split at projected
            · cases foundInput : lookupInput? snapshot.inputs
                  (bit * (parameters.length + 8) + position) with
              | none => simp [foundInput] at projected
              | some output =>
                  simp only [foundInput] at projected
                  split at projected
                  · have termEqual := Option.some.inj projected
                    subst term
                    obtain ⟨atIndex, named, bounded⟩ := lookupParameter?_at foundParameter
                    have inverse := check_lookupSource_inverse accepted foundInput
                    simp only [Term.eval, initialAssignment, inverse]
                    rw [sourceBit_of_position atIndex bounded inputs bit, widthEqual, named]
                  · contradiction
            · contradiction
          · rename_i outside
            have termEqual := Option.some.inj projected
            subst term
            simp [Term.eval, outside]
        · contradiction
  · contradiction

end Oak.CNFWordInput
