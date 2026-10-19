import Oak.CNFCheckComposition

/-!
# Checked extraction witnesses for the existing output allocation list

An extraction index selects one existing value and preserves the order of the
remaining values. Successful extraction of a supplied value sequence proves a
permutation of the original list. The final theorem derives the unchanged
output-uniqueness and dense-coverage fields from an exact range permutation.
-/

set_option autoImplicit false

namespace Oak.CNFOutputPermutation

open Oak.CNFDenseAllocation

def extractAt (index : Nat) (before : List Nat) : Option (Nat × List Nat) :=
  match index, before with
  | _, [] => none
  | 0, value :: rest => some (value, rest)
  | index + 1, head :: rest =>
      match extractAt index rest with
      | none => none
      | some (value, after) => some (value, head :: after)
termination_by structural index

def extractValues (values indices before : List Nat) : Option (List Nat) :=
  match values, indices, before with
  | [], [], before => some before
  | value :: values, index :: indices, before =>
      match extractAt index before with
      | none => none
      | some (found, after) =>
          if found = value then extractValues values indices after else none
  | _, _, _ => none
termination_by structural values

theorem extractAt_perm {index value : Nat} {before after : List Nat}
    (accepted : extractAt index before = some (value, after)) :
    (value :: after).Perm before := by
  induction index generalizing value before after with
  | zero =>
      cases before with
      | nil => simp [extractAt] at accepted
      | cons head rest =>
          have same : head = value ∧ rest = after := by
            simpa only [extractAt, Option.some.injEq, Prod.mk.injEq] using accepted
          rcases same with ⟨rfl, rfl⟩
          exact List.Perm.refl _
  | succ index induction =>
      cases before with
      | nil => simp [extractAt] at accepted
      | cons head rest =>
          cases extracted : extractAt index rest with
          | none => simp [extractAt, extracted] at accepted
          | some result =>
              rcases result with ⟨found, remaining⟩
              have same : found = value ∧ head :: remaining = after := by
                simpa only [extractAt, extracted, Option.some.injEq,
                  Prod.mk.injEq] using accepted
              rcases same with ⟨rfl, rfl⟩
              exact (List.Perm.swap head found remaining).trans
                ((induction extracted).cons head)

theorem extractValues_perm {values indices before after : List Nat}
    (accepted : extractValues values indices before = some after) :
    (values ++ after).Perm before := by
  induction values generalizing indices before after with
  | nil =>
      cases indices with
      | nil =>
          have same : before = after := Option.some.inj accepted
          subst after
          exact List.Perm.refl _
      | cons index indices => simp [extractValues] at accepted
  | cons value values induction =>
      cases indices with
      | nil => simp [extractValues] at accepted
      | cons index indices =>
          cases extracted : extractAt index before with
          | none => simp [extractValues, extracted] at accepted
          | some result =>
              rcases result with ⟨found, remaining⟩
              by_cases same : found = value
              · have tailAccepted : extractValues values indices remaining = some after := by
                  simpa only [extractValues, extracted, same, if_true] using accepted
                have removed : (value :: remaining).Perm before := by
                  simpa only [same] using (extractAt_perm extracted)
                exact ((induction tailAccepted).cons value).trans removed
              · simp [extractValues, extracted, same] at accepted

theorem perm_chain {left right before middle after : List Nat}
    (first : (left ++ middle).Perm before)
    (second : (right ++ after).Perm middle) :
    ((left ++ right) ++ after).Perm before := by
  simpa only [List.append_assoc] using
    (List.Perm.append_left left second).trans first

theorem outputs_shape_of_perm
    {snapshot : Oak.CNFDenseAllocation.Snapshot}
    (permuted : (outputs snapshot).Perm (List.range' 1 snapshot.variables)) :
    (outputs snapshot).Nodup ∧ denseCoverage snapshot = true := by
  constructor
  · exact permuted.symm.nodup (List.nodup_range' 1)
  · unfold denseCoverage
    apply List.all_eq_true.mpr
    intro index member
    apply decide_eq_true
    apply permuted.mem_iff.mpr
    apply List.mem_range'.mpr
    exact ⟨index, List.mem_range.mp member, by omega⟩

example : extractValues [3, 1, 2] [2, 0, 0] [1, 2, 3] = some [] := by decide

example : extractValues [3] [3] [1, 2, 3] = none := by decide

example : extractValues [2] [0] [1, 2, 3] = none := by decide

example : extractValues [1] [] [1, 2, 3] = none := by decide

end Oak.CNFOutputPermutation
