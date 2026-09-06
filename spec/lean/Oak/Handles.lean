namespace Oak.Handles

structure Handle where
  slot : Nat
  generation : Nat
  deriving DecidableEq, Repr

structure Slot where
  generation : Nat
  occupied : Bool
  deriving DecidableEq, Repr

/-- A handle resolves only when the slot is occupied and the generation matches. -/
def Resolves (h : Handle) (s : Slot) : Prop :=
  s.occupied = true ∧ h.generation = s.generation

/-- Reusing a slot advances its generation before making the new object live. -/
def reuse (s : Slot) : Slot :=
  { generation := s.generation + 1, occupied := true }

/-- A handle that resolved before slot reuse cannot resolve to the replacement object. -/
theorem stale_handle_cannot_resolve_after_reuse
    (h : Handle) (s : Slot) (hres : Resolves h s) :
    ¬ Resolves h (reuse s) := by
  intro hnew
  have hold : h.generation = s.generation := hres.2
  have hnext : h.generation = s.generation + 1 := by
    simpa [reuse] using hnew.2
  have impossible : s.generation = s.generation + 1 := by
    calc
      s.generation = h.generation := hold.symm
      _ = s.generation + 1 := hnext
  exact (Nat.ne_of_lt (Nat.lt_succ_self s.generation)) impossible

/-- Marking a slot unoccupied makes every handle fail resolution. -/
def clear (s : Slot) : Slot := { s with occupied := false }

theorem cleared_slot_never_resolves (h : Handle) (s : Slot) :
    ¬ Resolves h (clear s) := by
  intro hres
  simp [Resolves, clear] at hres

end Oak.Handles
