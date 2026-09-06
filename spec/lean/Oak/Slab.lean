namespace Oak.Slab

structure State where
  live : Nat
  capacity : Nat
  deriving DecidableEq, Repr

def Valid (s : State) : Prop := s.live ≤ s.capacity

inductive Action where
  | allocate
  | free
  deriving DecidableEq, Repr

/-- Slab transitions are only admitted when their explicit capacity/precondition holds. -/
inductive Step : Action -> State -> State -> Prop where
  | allocate (live capacity : Nat) (h : live < capacity) :
      Step .allocate
        { live := live, capacity := capacity }
        { live := live + 1, capacity := capacity }
  | free (live capacity : Nat) :
      Step .free
        { live := live + 1, capacity := capacity }
        { live := live, capacity := capacity }

/-- No valid slab transition can exceed its fixed capacity. -/
theorem step_preserves_capacity {action : Action} {before after : State}
    (hvalid : Valid before) (hstep : Step action before after) : Valid after := by
  cases hstep with
  | allocate live capacity hlt =>
      exact Nat.succ_le_of_lt hlt
  | free live capacity =>
      exact Nat.le_trans (Nat.le_succ live) hvalid

/-- Allocation from a full slab has no legal transition. -/
theorem full_slab_cannot_allocate (capacity : Nat) :
    ¬ Step .allocate
      { live := capacity, capacity := capacity }
      { live := capacity + 1, capacity := capacity } := by
  intro h
  cases h with
  | allocate _ _ hlt => exact (Nat.lt_irrefl capacity hlt)

end Oak.Slab
