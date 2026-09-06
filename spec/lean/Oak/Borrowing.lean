namespace Oak.Borrowing

inductive State where
  | free
  | shared : Nat -> State
  | unique
  deriving DecidableEq, Repr

inductive Action where
  | acquireRead
  | acquireWrite
  | releaseRead
  | releaseWrite
  deriving DecidableEq, Repr

/-- Shared states must contain at least one live reader. -/
def Valid : State -> Prop
  | .free => True
  | .shared n => 0 < n
  | .unique => True

/-- The only valid local ownership transitions for one owner. -/
inductive Step : Action -> State -> State -> Prop where
  | acquireReadFree : Step .acquireRead .free (.shared 1)
  | acquireReadShared (n : Nat) :
      Step .acquireRead (.shared (n + 1)) (.shared (n + 2))
  | acquireWrite : Step .acquireWrite .free .unique
  | releaseLastRead : Step .releaseRead (.shared 1) .free
  | releaseRead (n : Nat) :
      Step .releaseRead (.shared (n + 2)) (.shared (n + 1))
  | releaseWrite : Step .releaseWrite .unique .free

/-- Every legal transition preserves the representation invariant. -/
theorem step_preserves_valid {action : Action} {before after : State}
    (hvalid : Valid before) (hstep : Step action before after) : Valid after := by
  cases hstep <;> simp [Valid]

/-- Writable authority can only be acquired from the free state. -/
theorem acquire_write_only_from_free {before after : State}
    (h : Step .acquireWrite before after) : before = .free ∧ after = .unique := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A read acquisition never creates unique-write authority. -/
theorem acquire_read_not_unique {before after : State}
    (h : Step .acquireRead before after) : after ≠ .unique := by
  cases h <;> simp

/-- No writer can be acquired while readers remain live. -/
theorem shared_cannot_acquire_write (n : Nat) :
    ¬ Step .acquireWrite (.shared (n + 1)) .unique := by
  intro h
  cases h

/-- Unique-write state cannot acquire another writer. -/
theorem unique_cannot_acquire_write :
    ¬ Step .acquireWrite .unique .unique := by
  intro h
  cases h

/-- Unique-write state cannot acquire a read borrow. -/
theorem unique_cannot_acquire_read (after : State) :
    ¬ Step .acquireRead .unique after := by
  intro h
  cases h

/-- Releasing a reader never produces an invalid zero-reader shared state. -/
theorem no_shared_zero_after_step {action : Action} {before after : State}
    (hvalid : Valid before) (hstep : Step action before after) : after ≠ .shared 0 := by
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
