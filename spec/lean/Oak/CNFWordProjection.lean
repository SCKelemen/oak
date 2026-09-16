import Oak.CNFWordInput

/-!
# Checked word syntax to Boolean replay expressions

The supplied grammar retains widths, raw declared-width overrides, constants,
parameter names and pointwise binary operations. Projection checks the narrow
1..64-bit profile and constructs each output bit with explicit zero extension
or truncation. Its semantics is independent of the projected bit expressions.
Named inputs are interpreted at their declared widths: bits above that width
are zero even when the supplied 64-bit carrier contains nonzero high bits.
No equality with an unnormalized arbitrary Go `uint64` environment is claimed.

This is not a refinement of arbitrary Go term graphs, pointer memoization or
the replay's complete-reachability check. Projecting whole children validates
their syntax, but discarded high bits need not appear in the projected parent
or be replayed as intermediate CNF roots.
-/

set_option autoImplicit false

namespace Oak.CNFWordProjection

open Oak.RupCheck Oak.TseitinCNF Oak.CNFDenseAllocation
open Oak.CNFReplayApply Oak.CNFReplayTerm Oak.CNFWordInput

inductive WordTerm where
  | constant (width value : Nat)
  | param (width declared : Nat) (name : String)
  | binary (width op : Nat) (left right : WordTerm)
  deriving Repr

def WordTerm.width : WordTerm → Nat
  | .constant width _ => width
  | .param width _ _ => width
  | .binary width _ _ _ => width

/-- A zero raw override uses the term width, as in `term.declaredWidth`. -/
def effectiveDeclared (width declared : Nat) : Nat :=
  if declared = 0 then width else declared

/-- Independent, zero-padded bit semantics of the supplied word grammar. -/
def WordTerm.bitValue (inputs : Inputs) : WordTerm → Nat → Bool
  | .constant width value, bit =>
      if bit < width then value.testBit bit else false
  | .param width declared name, bit =>
      if bit < width then
        if bit < effectiveDeclared width declared then (inputs name).getLsbD bit else false
      else false
  | .binary width op left right, bit =>
      if bit < width then binaryValue op (left.bitValue inputs bit) (right.bitValue inputs bit)
      else false

theorem bitValue_outside_width (inputs : Inputs) (term : WordTerm) (bit : Nat)
    (outside : term.width ≤ bit) : term.bitValue inputs bit = false := by
  cases term <;> simp only [WordTerm.width] at outside <;>
    simp [WordTerm.bitValue, Nat.not_lt_of_ge outside]

/-- Enumerate a fixed bit interval while retaining every admission decision. -/
def projectBits (project : Nat → Option Term) (start : Nat) : Nat → Option (List Term)
  | 0 => some []
  | count + 1 =>
      match project start, projectBits project (start + 1) count with
      | some bit, some rest => some (bit :: rest)
      | _, _ => none

theorem projectBits_spec {project : Nat → Option Term} {start count : Nat}
    {bits : List Term} (projected : projectBits project start count = some bits) :
    bits.length = count ∧ ∀ bit, bit < count →
      project (start + bit) = some (bits.getD bit (.constant false)) := by
  induction count generalizing start bits with
  | zero =>
      simp only [projectBits, Option.some.injEq] at projected
      subst bits
      simp
  | succ count induction =>
      simp only [projectBits] at projected
      cases head : project start with
      | none => simp [head] at projected
      | some value =>
          cases tail : projectBits project (start + 1) count with
          | none => simp [head, tail] at projected
          | some rest =>
              simp only [head, tail, Option.some.injEq] at projected
              subst bits
              obtain ⟨length, meaning⟩ := induction tail
              constructor
              · simp [length]
              · intro bit before
                cases bit with
                | zero => simpa using head
                | succ bit =>
                    simpa [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using meaning bit (by omega)

/-- Check every node and construct its result bits in low-to-high order. -/
def projectWord (snapshot : Snapshot) (parameters : List Parameter) (maxInt : Nat) :
    WordTerm → Option (List Term)
  | .constant width value =>
      if 0 < width ∧ width ≤ 64 ∧ value < 2 ^ width then
        some ((List.range width).map fun bit => .constant (value.testBit bit))
      else none
  | .param width declared name =>
      if 0 < width ∧ width ≤ 64 then
        projectBits (projectInputBit snapshot parameters maxInt name
          (effectiveDeclared width declared)) 0 width
      else none
  | .binary width op left right =>
      if 0 < width ∧ width ≤ 64 ∧ op < 3 then
        match projectWord snapshot parameters maxInt left,
            projectWord snapshot parameters maxInt right with
        | some leftBits, some rightBits =>
            some ((List.range width).map fun bit =>
              .binary op (leftBits.getD bit (.constant false))
                (rightBits.getD bit (.constant false)))
        | _, _ => none
      else none

theorem projectWord_length {snapshot : Snapshot} {parameters : List Parameter}
    {maxInt : Nat} {term : WordTerm} {bits : List Term}
    (projected : projectWord snapshot parameters maxInt term = some bits) :
    bits.length = term.width := by
  cases term with
  | constant width value =>
      unfold projectWord at projected
      split at projected
      · cases Option.some.inj projected
        simp [WordTerm.width]
      · contradiction
  | param width declared name =>
      unfold projectWord at projected
      split at projected
      · exact (projectBits_spec projected).1
      · contradiction
  | binary width op left right =>
      unfold projectWord at projected
      split at projected
      · cases leftProjected : projectWord snapshot parameters maxInt left with
        | none => simp [leftProjected] at projected
        | some leftBits =>
            cases rightProjected : projectWord snapshot parameters maxInt right with
            | none => simp [leftProjected, rightProjected] at projected
            | some rightBits =>
                simp only [leftProjected, rightProjected, Option.some.injEq] at projected
                subst bits
                simp [WordTerm.width]
      · contradiction

private theorem getD_map_range {α : Type} (function : Nat → α) (width bit : Nat)
    (fallback : α) (within : bit < width) :
    ((List.range width).map function).getD bit fallback = function bit := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range within]

private theorem projectWord_getD_outside {snapshot : Snapshot}
    {parameters : List Parameter} {maxInt : Nat} {term : WordTerm} {bits : List Term}
    (projected : projectWord snapshot parameters maxInt term = some bits)
    (assignment : Assignment) (bit : Nat) (outside : term.width ≤ bit) :
    (bits.getD bit (.constant false)).eval assignment = false := by
  have absent : bits.length ≤ bit := by rw [projectWord_length projected]; exact outside
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none absent, Term.eval]

/-- Every bit of accepted projection agrees with the independent word
semantics, including zero padding outside the word's width. Input binding is
derived from the checked snapshot and parameter projection. -/
theorem projectWord_sound_all {snapshot : Snapshot} {gates : List RawGate}
    {parameters : List Parameter} {maxInt : Nat} {term : WordTerm} {bits : List Term}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (projected : projectWord snapshot parameters maxInt term = some bits) :
    ∀ (inputs : Inputs) (bit : Nat),
      (bits.getD bit (.constant false)).eval (initialAssignment snapshot parameters inputs) =
        term.bitValue inputs bit := by
  induction term generalizing bits with
  | constant width value =>
      intro inputs bit
      by_cases within : bit < width
      · unfold projectWord at projected
        split at projected
        · cases Option.some.inj projected
          rw [getD_map_range _ _ _ _ within]
          simp [Term.eval, WordTerm.bitValue, within]
        · contradiction
      · exact (projectWord_getD_outside projected _ bit (by simpa [WordTerm.width] using Nat.le_of_not_gt within)).trans
          (bitValue_outside_width inputs (.constant width value) bit (by simpa [WordTerm.width] using Nat.le_of_not_gt within)).symm
  | param width declared name =>
      intro inputs bit
      by_cases within : bit < width
      · unfold projectWord at projected
        split at projected
        · have projectedBit := (projectBits_spec projected).2 bit within
          simp only [Nat.zero_add] at projectedBit
          simpa [WordTerm.bitValue, within] using
            projectInputBit_sound accepted projectedBit inputs
        · contradiction
      · exact (projectWord_getD_outside projected _ bit (by simpa [WordTerm.width] using Nat.le_of_not_gt within)).trans
          (bitValue_outside_width inputs (.param width declared name) bit (by simpa [WordTerm.width] using Nat.le_of_not_gt within)).symm
  | binary width op left right leftIH rightIH =>
      intro inputs bit
      by_cases within : bit < width
      · unfold projectWord at projected
        split at projected
        · cases leftProjected : projectWord snapshot parameters maxInt left with
          | none => simp [leftProjected] at projected
          | some leftBits =>
              cases rightProjected : projectWord snapshot parameters maxInt right with
              | none => simp [leftProjected, rightProjected] at projected
              | some rightBits =>
                  simp only [leftProjected, rightProjected, Option.some.injEq] at projected
                  subst bits
                  rw [getD_map_range _ _ _ _ within]
                  simp only [Term.eval, WordTerm.bitValue, within, if_true]
                  rw [leftIH leftProjected inputs bit, rightIH rightProjected inputs bit]
        · contradiction
      · exact (projectWord_getD_outside projected _ bit (by simpa [WordTerm.width] using Nat.le_of_not_gt within)).trans
          (bitValue_outside_width inputs (.binary width op left right) bit (by simpa [WordTerm.width] using Nat.le_of_not_gt within)).symm

theorem projectWord_sound {snapshot : Snapshot} {gates : List RawGate}
    {parameters : List Parameter} {maxInt : Nat} {term : WordTerm} {bits : List Term}
    (accepted : Oak.CNFDenseAllocation.check snapshot = some gates)
    (projected : projectWord snapshot parameters maxInt term = some bits)
    (inputs : Inputs) (bit : Nat) (_within : bit < term.width) :
    (bits.getD bit (.constant false)).eval (initialAssignment snapshot parameters inputs) =
      term.bitValue inputs bit :=
  projectWord_sound_all accepted projected inputs bit

/-- Pack the independent semantics, not the result of projection. -/
def WordTerm.eval (inputs : Inputs) (term : WordTerm) : BitVec term.width :=
  (BitVec.ofBoolListLE ((List.range term.width).map (term.bitValue inputs))).cast (by simp)

end Oak.CNFWordProjection
