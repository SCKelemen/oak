namespace Oak.Borrowing

inductive State where
  | free
  | shared : Nat -> State
  | unique
  deriving DecidableEq, Repr

/-- Shared states must contain at least one live reader. -/
def Valid : State -> Prop
  | .free => True
  | .shared n => 0 < n
  | .unique => True

/-- The only valid local ownership transitions for one owner. -/
inductive Step : State -> State -> Prop where
  | acquireReadFree : Step .free (.shared 1)
  | acquireReadShared (n : Nat) : Step (.shared (n + 1)) (.shared (n + 2))
  | acquireWrite : Step .free .unique
  | releaseLastRead : Step (.shared 1) .free
  | releaseRead (n : Nat) : Step (.shared (n + 2)) (.shared (n + 1))
  | releaseWrite : Step .unique .free

/-- Every legal transition preserves the representation invariant. -/
theorem step_preserves_valid {before after : State}
    (hvalid : Valid before) (hstep : Step before after) : Valid after := by
  cases hstep <;> simp [Valid]

/-- Writable authority can only be acquired from the free state. -/
theorem acquire_write_only_from_free {before : State}
    (h : Step before .unique) : before = .free := by
  cases h
  rfl

/-- A read acquisition never creates unique-write authority. -/
theorem read_acquisition_not_unique {before : State}
    (h : Step before (.shared 1)) : before = .free := by
  cases h
  rfl

/-- No legal transition acquires a writer while readers remain live. -/
theorem shared_cannot_step_to_unique (n : Nat) :
    ¬ Step (.shared (n + 1)) .unique := by
  intro h
  cases h

/-- Unique-write state cannot acquire another writer. -/
theorem unique_cannot_step_to_unique : ¬ Step .unique .unique := by
  intro h
  cases h

/-- Unique-write state cannot acquire a read borrow. -/
theorem unique_cannot_step_to_shared (n : Nat) :
    ¬ Step .unique (.shared n) := by
  intro h
  cases h

/-- Releasing a reader never produces an invalid zero-reader shared state. -/
theorem no_shared_zero_after_step {before after : State}
    (hvalid : Valid before) (hstep : Step before after) : after ≠ .shared 0 := by
  intro hz
  have havalid := step_preserves_valid hvalid hstep
  rw [hz] at havalid
  simp [Valid] at havalid

/-- The abstract state never represents simultaneous shared-read and unique-write authority. -/
def HasReaders : State -> Prop
  | .shared n => 0 < n
  | _ => False

def HasWriter : State -> Prop
  | .unique => True
  | _ => False

theorem readers_and_writer_exclusive (s : State) :
    ¬ (HasReaders s ∧ HasWriter s) := by
  cases s <;> simp [HasReaders, HasWriter]

end Oak.Borrowing
