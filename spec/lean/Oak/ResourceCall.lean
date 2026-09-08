import Oak.ResourceFlow

namespace Oak.ResourceCall

/-- Resource parameter access modes are semantic callable facts. They do not
freeze any source spelling. Shared borrowing preserves authority and may alias;
mutable borrowing and consumption require call-local exclusivity. -/
inductive ParameterMode where
  | borrowed
  | borrowedMut
  | consumed
  deriving DecidableEq, Repr

/-- Two mode-marked arguments may carry the same resource authority class only
when both accesses are shared borrows. -/
def Compatible : ParameterMode -> ParameterMode -> Prop
  | .borrowed, .borrowed => True
  | _, _ => False

theorem borrowed_alias_compatible :
    Compatible .borrowed .borrowed := by
  simp [Compatible]

theorem borrowedMut_requires_exclusive (other : ParameterMode) :
    ¬ Compatible .borrowedMut other := by
  cases other <;> simp [Compatible]

theorem consumed_requires_exclusive (other : ParameterMode) :
    ¬ Compatible .consumed other := by
  cases other <;> simp [Compatible]

theorem compatibility_symmetric (left right : ParameterMode) :
    Compatible left right ↔ Compatible right left := by
  cases left <;> cases right <;> simp [Compatible]

theorem compatible_iff_shared (left right : ParameterMode) :
    Compatible left right ↔ left = .borrowed ∧ right = .borrowed := by
  cases left <;> cases right <;> simp [Compatible]

/-- `commit` models the permanent resource effect after call-local authority
checks have completed. Rejected calls are identity transitions; shared and
mutable borrows are temporary and also preserve permanent authority. -/
def commit : Bool -> ParameterMode -> Oak.ResourceFlow.State -> Oak.ResourceFlow.Name -> Oak.ResourceFlow.State
  | false, _, s, _ => s
  | true, .consumed, s, name => Oak.ResourceFlow.consume s name
  | true, _, s, _ => s

theorem rejected_call_preserves_state (mode : ParameterMode)
    (s : Oak.ResourceFlow.State) (name : Oak.ResourceFlow.Name) :
    commit false mode s name = s := by
  rfl

theorem shared_call_preserves_state (s : Oak.ResourceFlow.State)
    (name : Oak.ResourceFlow.Name) :
    commit true .borrowed s name = s := by
  rfl

theorem mutable_call_preserves_state (s : Oak.ResourceFlow.State)
    (name : Oak.ResourceFlow.Name) :
    commit true .borrowedMut s name = s := by
  rfl

theorem consumed_call_commits_consumption (s : Oak.ResourceFlow.State)
    (name : Oak.ResourceFlow.Name) :
    commit true .consumed s name = Oak.ResourceFlow.consume s name := by
  rfl

end Oak.ResourceCall
