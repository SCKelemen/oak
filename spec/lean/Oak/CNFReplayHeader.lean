import Oak.CNFWordInput

/-!
# Checked metadata for the narrow native CNF replay

This models the metadata portion of `newNativeCNFReplay`, before its separate
gate/memo validation. Ordered parameter names, index entries and width entries
must agree exactly. A missing index entry is distinct from an entry containing
zero, including at the first parameter position.

Go maps are represented by lists with explicit key uniqueness. Acceptance
does not prove faithful projection of Go memory, pointer presence, signed
integer conversion, gate allocation or replay reachability. Those boundaries
remain separate from this supplied-header theorem.
-/

set_option autoImplicit false

namespace Oak.CNFReplayHeader

open Oak.CNFWordInput

structure Snapshot where
  params : List String
  index : List (String × Nat)
  widths : List (String × Nat)
  grouped : Bool
  assumed : Bool
  selects : Nat
  deriving Repr

def lookup? : List (String × Nat) → String → Option Nat
  | [], _ => none
  | entry :: rest, name =>
      if entry.1 = name then some entry.2 else lookup? rest name

def Shape (snapshot : Snapshot) : Prop :=
  snapshot.grouped = false ∧ snapshot.assumed = false ∧ snapshot.selects = 0 ∧
    snapshot.params.Nodup ∧ (snapshot.index.map Prod.fst).Nodup ∧
    (snapshot.widths.map Prod.fst).Nodup ∧
    snapshot.index.length = snapshot.params.length ∧
    snapshot.widths.length = snapshot.params.length

instance (snapshot : Snapshot) : Decidable (Shape snapshot) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

inductive AcceptedFrom (index widths : List (String × Nat)) :
    Nat → List String → List Parameter → Prop where
  | nil (position : Nat) : AcceptedFrom index widths position [] []
  | cons {position width : Nat} {name : String} {names : List String}
      {parameters : List Parameter}
      (nonempty : name ≠ "")
      (indexed : lookup? index name = some position)
      (sized : lookup? widths name = some width)
      (range : 1 ≤ width ∧ width ≤ 64)
      (tail : AcceptedFrom index widths (position + 1) names parameters) :
      AcceptedFrom index widths position (name :: names) (⟨name, width⟩ :: parameters)

def checkFrom (index widths : List (String × Nat)) :
    Nat → List String → Option (List Parameter)
  | _, [] => some []
  | position, name :: names =>
      match lookup? index name, lookup? widths name with
      | some actualPosition, some width =>
          if name ≠ "" ∧ actualPosition = position ∧ 1 ≤ width ∧ width ≤ 64 then
            match checkFrom index widths (position + 1) names with
            | some parameters => some (⟨name, width⟩ :: parameters)
            | none => none
          else none
      | _, _ => none

def check (snapshot : Snapshot) : Option (List Parameter) :=
  if Shape snapshot then checkFrom snapshot.index snapshot.widths 0 snapshot.params
  else none

theorem checkFrom_accepted {index widths : List (String × Nat)}
    {position : Nat} {names : List String} {parameters : List Parameter}
    (accepted : checkFrom index widths position names = some parameters) :
    AcceptedFrom index widths position names parameters := by
  induction names generalizing position parameters with
  | nil =>
      simp only [checkFrom, Option.some.injEq] at accepted
      subst parameters
      exact .nil position
  | cons name names induction =>
      simp only [checkFrom] at accepted
      cases indexed : lookup? index name with
      | none => simp [indexed] at accepted
      | some actualPosition =>
          cases sized : lookup? widths name with
          | none => simp [indexed, sized] at accepted
          | some width =>
              simp only [indexed, sized] at accepted
              split at accepted
              · rename_i conditions
                cases checkedTail : checkFrom index widths (position + 1) names with
                | none => simp [checkedTail] at accepted
                | some tailParameters =>
                    simp only [checkedTail, Option.some.injEq] at accepted
                    subst parameters
                    exact .cons conditions.1 (indexed.trans (congrArg some conditions.2.1))
                      sized conditions.2.2 (induction checkedTail)
              · contradiction

theorem check_accepted {snapshot : Snapshot} {parameters : List Parameter}
    (accepted : check snapshot = some parameters) :
    Shape snapshot ∧ AcceptedFrom snapshot.index snapshot.widths 0 snapshot.params parameters := by
  unfold check at accepted
  split at accepted
  · exact ⟨by assumption, checkFrom_accepted accepted⟩
  · contradiction

theorem AcceptedFrom.names {index widths : List (String × Nat)} {position : Nat}
    {names : List String} {parameters : List Parameter}
    (accepted : AcceptedFrom index widths position names parameters) :
    parameters.map Parameter.name = names := by
  induction accepted with
  | nil => rfl
  | cons nonempty indexed sized range tail induction => simp [induction]

theorem AcceptedFrom.parameter_valid {index widths : List (String × Nat)}
    {position : Nat} {names : List String} {parameters : List Parameter}
    (accepted : AcceptedFrom index widths position names parameters)
    {parameter : Parameter} (member : parameter ∈ parameters) :
    parameter.name ≠ "" ∧ 1 ≤ parameter.width ∧ parameter.width ≤ 64 := by
  induction accepted with
  | nil => contradiction
  | cons nonempty indexed sized range tail induction =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨nonempty, range⟩
      · exact induction member

/-- Acceptance supplies the global parameter validity required even by
constant-only word expressions, without depending on parameter leaves. -/
theorem check_parameters_valid {snapshot : Snapshot} {parameters : List Parameter}
    (accepted : check snapshot = some parameters) : parametersValid parameters = true := by
  obtain ⟨shape, walk⟩ := check_accepted accepted
  simp only [parametersValid, Bool.and_eq_true]
  constructor
  · have unique : (parameters.map Parameter.name).Nodup := by
      rw [walk.names]
      exact shape.2.2.2.1
    exact decide_eq_true unique
  · apply List.all_eq_true.mpr
    intro parameter member
    exact decide_eq_true (walk.parameter_valid member)

theorem check_names {snapshot : Snapshot} {parameters : List Parameter}
    (accepted : check snapshot = some parameters) :
    parameters.map Parameter.name = snapshot.params :=
  (check_accepted accepted).2.names

theorem AcceptedFrom.at {index widths : List (String × Nat)} {start : Nat}
    {names : List String} {parameters : List Parameter}
    (accepted : AcceptedFrom index widths start names parameters)
    {position : Nat} {parameter : Parameter}
    (atIndex : parameters[position]? = some parameter) :
    names[position]? = some parameter.name ∧
      lookup? index parameter.name = some (start + position) ∧
      lookup? widths parameter.name = some parameter.width ∧
      parameter.name ≠ "" ∧ 1 ≤ parameter.width ∧ parameter.width ≤ 64 := by
  induction accepted generalizing position with
  | nil => simp at atIndex
  | cons nonempty indexed sized range tail induction =>
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
          subst parameter
          exact ⟨rfl, by simpa using indexed, sized, nonempty, range⟩
      | succ position =>
          have result := induction atIndex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- Every returned parameter has its exact ordered name, an explicitly
present index entry and its declared width entry. -/
theorem check_parameter_at {snapshot : Snapshot} {parameters : List Parameter}
    (accepted : check snapshot = some parameters)
    {position : Nat} {parameter : Parameter}
    (atIndex : parameters[position]? = some parameter) :
    snapshot.params[position]? = some parameter.name ∧
      lookup? snapshot.index parameter.name = some position ∧
      lookup? snapshot.widths parameter.name = some parameter.width ∧
      parameter.name ≠ "" ∧ 1 ≤ parameter.width ∧ parameter.width ≤ 64 := by
  simpa using (check_accepted accepted).2.at atIndex

theorem lookup?_mem {table : List (String × Nat)} {name : String} {value : Nat}
    (found : lookup? table name = some value) : (name, value) ∈ table := by
  induction table with
  | nil => simp [lookup?] at found
  | cons entry rest induction =>
      simp only [lookup?] at found
      split at found
      · have keyEq : entry.1 = name := by assumption
        have valueEq : entry.2 = value := Option.some.inj found
        exact List.mem_cons.mpr (Or.inl (Prod.ext keyEq valueEq).symm)
      · exact List.mem_cons_of_mem _ (induction found)

theorem AcceptedFrom.names_subset_keys {index widths : List (String × Nat)} {position : Nat}
    {names : List String} {parameters : List Parameter}
    (accepted : AcceptedFrom index widths position names parameters) :
    names ⊆ index.map Prod.fst ∧ names ⊆ widths.map Prod.fst := by
  induction accepted with
  | nil => simp
  | cons nonempty indexed sized range tail induction =>
      constructor
      · intro name member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_map.mpr ⟨_, lookup?_mem indexed, rfl⟩
        · exact induction.1 member
      · intro name member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_map.mpr ⟨_, lookup?_mem sized, rfl⟩
        · exact induction.2 member

private theorem reverse_subset_of_length {α : Type} {left right : List α}
    (unique : left.Nodup) (subset : left ⊆ right)
    (sameLength : left.length = right.length) : right ⊆ left := by
  classical
  intro value member
  by_cases missing : value ∈ left
  · exact missing
  have enlargedUnique : (value :: left).Nodup := List.nodup_cons.mpr ⟨missing, unique⟩
  have enlargedSubset : value :: left ⊆ right := by
    intro item itemMember
    rcases List.mem_cons.mp itemMember with rfl | itemMember
    · exact member
    · exact subset itemMember
  have tooLong := enlargedUnique.length_le_of_subset enlargedSubset
  simp only [List.length_cons] at tooLong
  omega

/-- Equal counts plus the complete ordered walk exclude hidden extra keys in
either table; successful lookups cannot be balanced by unrelated entries. -/
theorem check_keys_exact {snapshot : Snapshot} {parameters : List Parameter}
    (accepted : check snapshot = some parameters) (name : String) :
    (name ∈ snapshot.index.map Prod.fst ↔ name ∈ snapshot.params) ∧
      (name ∈ snapshot.widths.map Prod.fst ↔ name ∈ snapshot.params) := by
  obtain ⟨shape, walk⟩ := check_accepted accepted
  have subsets := walk.names_subset_keys
  have indexLength : snapshot.params.length = (snapshot.index.map Prod.fst).length := by
    simpa using shape.2.2.2.2.2.2.1.symm
  have widthLength : snapshot.params.length = (snapshot.widths.map Prod.fst).length := by
    simpa using shape.2.2.2.2.2.2.2.symm
  exact ⟨⟨fun member => reverse_subset_of_length shape.2.2.2.1 subsets.1 indexLength member,
      fun member => subsets.1 member⟩,
    ⟨fun member => reverse_subset_of_length shape.2.2.2.1 subsets.2 widthLength member,
      fun member => subsets.2 member⟩⟩

end Oak.CNFReplayHeader
