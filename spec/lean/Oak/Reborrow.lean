import Oak.BorrowRegions

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

/-- A second child cannot be derived directly from an already active child state
    when no region facts are available (the fail-closed single-chain model). -/
theorem active_child_rejects_sibling :
    reborrow .childActive = none := by
  rfl

/-! ### Disjoint sibling reborrows

With exact regions, one parent span may be split into several live writable
children, provided their regions are statically proven pairwise disjoint.
The parent stays suspended while any child is live and is restored when the
last child is released. Region identity and disjointness are the authoritative
`Oak.BorrowRegions` facts (in particular, zero-length regions alias nothing);
this section only adds the admission discipline. Unknown regions are not
representable here: `Oak.ReborrowRefinement` proves the concrete compiler
procedure fails closed and admits no sibling next to an unknown region. -/

namespace Split

open Oak.BorrowRegions

instance (a b : Region) : Decidable (Disjoint a b) := by
  unfold Oak.BorrowRegions.Disjoint
  exact inferInstance

/-- Executable disjointness test used by the admission check. -/
def disjointB (a b : Region) : Bool := decide (Disjoint a b)

theorem disjointB_iff {a b : Region} : disjointB a b = true ↔ Disjoint a b :=
  decide_eq_true_iff

/-- Disjointness is symmetric (restated from `Oak.BorrowRegions`). -/
theorem disjoint_symm {a b : Region} (h : Disjoint a b) : Disjoint b a :=
  disjoint_symmetric.mp h

/-- A candidate child is admitted only when disjoint from every live sibling. -/
def admits : List Region → Region → Bool
  | [], _ => true
  | c :: rest, r => disjointB r c && admits rest r

theorem admits_iff {s : List Region} {r : Region} :
    admits s r = true ↔ ∀ c ∈ s, Disjoint r c := by
  induction s with
  | nil => simp [admits]
  | cons c rest ih => simp [admits, disjointB_iff, ih]

/-- The parent span is directly usable only while no writable child is live. -/
def ParentUsable (children : List Region) : Prop := children = []

/-- Deriving a writable child: admitted children join the live set; anything
    that cannot be proven disjoint from every live sibling is rejected. -/
def reborrowChild (children : List Region) (r : Region) : Option (List Region) :=
  if admits children r then some (r :: children) else none

/-- Any successful reborrow suspends direct use of the parent. -/
theorem reborrow_suspends_parent {children after : List Region} {r : Region}
    (h : reborrowChild children r = some after) : ¬ ParentUsable after := by
  unfold reborrowChild at h
  cases hadm : admits children r with
  | false => simp [hadm] at h
  | true =>
    simp [hadm] at h
    subst h
    simp [ParentUsable]

/-- A reborrow overlapping any live sibling is rejected. -/
theorem overlapping_reborrow_rejected {children : List Region} {r c : Region}
    (hmem : c ∈ children) (hover : ¬ Disjoint r c) :
    reborrowChild children r = none := by
  unfold reborrowChild
  cases hadm : admits children r with
  | false => simp
  | true => exact absurd (admits_iff.mp hadm c hmem) hover

/-- Admission preserves pairwise disjointness of the live children. -/
theorem reborrow_preserves_pairwise_disjoint {children after : List Region} {r : Region}
    (hpair : children.Pairwise Disjoint) (h : reborrowChild children r = some after) :
    after.Pairwise Disjoint := by
  unfold reborrowChild at h
  cases hadm : admits children r with
  | false => simp [hadm] at h
  | true =>
    simp [hadm] at h
    subst h
    exact List.Pairwise.cons (admits_iff.mp hadm) hpair

/-- Releasing one live child. -/
def releaseChildAt (children : List Region) (i : Nat) : List Region :=
  children.eraseIdx i

/-- Releasing the last live child restores direct parent authority. -/
theorem release_last_restores_parent (r : Region) :
    ParentUsable (releaseChildAt [r] 0) := by
  rfl

/-- Releasing a child never revokes disjointness among the remaining children. -/
theorem release_preserves_pairwise_disjoint {children : List Region} {i : Nat}
    (hpair : children.Pairwise Disjoint) :
    (releaseChildAt children i).Pairwise Disjoint :=
  hpair.eraseIdx i

end Split

end Oak.Reborrow
