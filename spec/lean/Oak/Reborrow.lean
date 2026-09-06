namespace Oak.Reborrow

/-- Writable authority has exactly one usable point in a reborrow chain. -/
inductive WritableState where
  | parentUsable
  | childActive
  | ended
  deriving DecidableEq, Repr

/-- A writable child may only be created while the parent is usable. -/
def reborrow : WritableState -> Option WritableState
  | .parentUsable => some .childActive
  | .childActive => none
  | .ended => none

/-- Releasing the child restores the suspended parent authority. -/
def releaseChild : WritableState -> WritableState
  | .childActive => .parentUsable
  | state => state

/-- Direct parent access exists only in the parent-usable state. -/
def ParentUsable : WritableState -> Prop
  | .parentUsable => True
  | _ => False

/-- Child writable access exists only while the reborrow is active. -/
def ChildActive : WritableState -> Prop
  | .childActive => True
  | _ => False

/-- Successful reborrowing necessarily suspends direct parent use. -/
theorem successful_reborrow_suspends_parent {before after : WritableState}
    (h : reborrow before = some after) :
    after = .childActive ∧ ¬ ParentUsable after := by
  cases before <;> simp [reborrow] at h
  subst after
  simp [ParentUsable]

/-- No state grants simultaneous writable use through parent and child. -/
theorem parent_child_exclusive (state : WritableState) :
    ¬ (ParentUsable state ∧ ChildActive state) := by
  cases state <;> simp [ParentUsable, ChildActive]

/-- Ending a writable child restores the parent exactly. -/
theorem release_restores_parent :
    releaseChild .childActive = .parentUsable := by
  rfl

/-- A second child cannot be derived directly from an already active child state. -/
theorem active_child_rejects_sibling :
    reborrow .childActive = none := by
  rfl

end Oak.Reborrow
