import Oak.Borrowing

namespace Oak.ResourceFlow

/-- Source-level resource names and alias classes are abstract identities here.
The executable checker may use strings/integers; the proof only needs equality. -/
abbrev Name := Nat
abbrev ClassId := Nat

/-- Resource authority is deliberately separate from Oak.Borrowing.State.
A unique writable borrow is temporary; consumed authority never returns. -/
inductive Authority where
  | live
  | consumed
  deriving DecidableEq, Repr

/-- `classOf` is provenance/alias membership. Authority belongs to the alias
class, not to an individual spelling, so consuming one member invalidates all
members of that class. -/
structure State where
  classOf : Name -> ClassId
  authority : ClassId -> Authority

/-- A name is usable exactly while its alias class still has live authority. -/
def Usable (s : State) (name : Name) : Prop :=
  s.authority (s.classOf name) = .live

/-- Two names alias the same resource authority when they belong to one class. -/
def Aliases (s : State) (left right : Name) : Prop :=
  s.classOf left = s.classOf right

/-- Consumption changes authority for exactly one alias class. Provenance is
unchanged: aliases remain aliases, but the class no longer carries authority. -/
def consumeClass (s : State) (classId : ClassId) : State :=
  { s with
    authority := fun candidate =>
      if candidate = classId then .consumed else s.authority candidate }

/-- Consuming a name consumes the authority of its entire alias class. -/
def consume (s : State) (name : Name) : State :=
  consumeClass s (s.classOf name)

inductive Action where
  | use : Name -> Action
  | consume : Name -> Action
  deriving Repr

/-- The local resource-flow transition system. There is intentionally no
transition that restores consumed authority. -/
inductive Step : Action -> State -> State -> Prop where
  | use {s : State} {name : Name} :
      Usable s name -> Step (.use name) s s
  | consume {s : State} {name : Name} :
      Usable s name -> Step (.consume name) s (consume s name)

/-- Consumption immediately invalidates the syntactic name that was consumed. -/
theorem consume_invalidates_self (s : State) (name : Name) :
    ¬ Usable (consume s name) name := by
  simp [Usable, consume, consumeClass]

/-- Consumption invalidates every alias whose authority belongs to the same
class, not merely the name passed to the consuming operation. -/
theorem consume_invalidates_alias {s : State} {source alias : Name}
    (h : Aliases s source alias) :
    ¬ Usable (consume s source) alias := by
  simp [Usable, consume, consumeClass, Aliases, h]

/-- An unrelated alias class keeps exactly the authority it had before another
class was consumed. -/
theorem consume_preserves_unrelated {s : State} {source other : Name}
    (h : ¬ Aliases s source other) :
    Usable (consume s source) other ↔ Usable s other := by
  have hne : s.classOf other ≠ s.classOf source := by
    intro heq
    exact h heq.symm
  simp [Usable, consume, consumeClass, hne]

/-- Resource-flow steps never change provenance/alias-class membership. -/
theorem step_preserves_class {action : Action} {before after : State}
    (h : Step action before after) (name : Name) :
    after.classOf name = before.classOf name := by
  cases h <;> rfl

/-- Therefore an alias relationship, once established for this local flow,
remains the same across uses and consumption. -/
theorem step_preserves_aliases {action : Action} {before after : State}
    (hstep : Step action before after) {left right : Name}
    (halias : Aliases before left right) :
    Aliases after left right := by
  unfold Aliases at halias ⊢
  rw [step_preserves_class hstep left, step_preserves_class hstep right]
  exact halias

/-- Once an alias class is consumed, every later legal step preserves that
fact. This is the core permanence property distinguishing consumption from a
borrow that can later be released. -/
theorem consumed_class_stays_consumed {action : Action} {before after : State}
    {classId : ClassId}
    (hconsumed : before.authority classId = .consumed)
    (hstep : Step action before after) :
    after.authority classId = .consumed := by
  cases hstep with
  | use _ =>
      exact hconsumed
  | consume _ =>
      simp [consume, consumeClass, hconsumed]

/-- A consumed name cannot be used. -/
theorem consumed_cannot_use {s : State} {name : Name}
    (hconsumed : s.authority (s.classOf name) = .consumed) :
    ¬ Step (.use name) s s := by
  intro hstep
  cases hstep with
  | use husable =>
      simp [Usable, hconsumed] at husable

/-- Consuming already-consumed authority is also rejected: a consuming call is
itself a use of the old authority. -/
theorem consumed_cannot_consume {s after : State} {name : Name}
    (hconsumed : s.authority (s.classOf name) = .consumed) :
    ¬ Step (.consume name) s after := by
  intro hstep
  cases hstep with
  | consume husable =>
      simp [Usable, hconsumed] at husable

/-- Borrow admission and resource consumption are separate axes. Consumption is
allowed only when the resource is live and no local borrow currently holds its
access authority. -/
def CanConsume (borrow : Oak.Borrowing.State) (authority : Authority) : Prop :=
  borrow = .free ∧ authority = .live

theorem free_live_can_consume : CanConsume .free .live := by
  simp [CanConsume]

theorem shared_borrow_blocks_consume (n : Nat) :
    ¬ CanConsume (.shared (n + 1)) .live := by
  simp [CanConsume]

theorem unique_borrow_blocks_consume :
    ¬ CanConsume .unique .live := by
  simp [CanConsume]

theorem consumed_authority_cannot_be_consumed (borrow : Oak.Borrowing.State) :
    ¬ CanConsume borrow .consumed := by
  simp [CanConsume]

end Oak.ResourceFlow
