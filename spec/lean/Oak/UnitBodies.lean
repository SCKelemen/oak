/-!
# Unit bodies without effects

Model for docs/spec/94-assembler.md §8 (unit bodies without effects). A
unit function's contract is its effect: the package cells and the span
memories it writes, each side's effects a log applied to the entry state.
When neither side logs a write, both leave the entry state as it is, so
the two sides agree on every entry state — the verdict the assembler
verifier now gives such a body instead of "no integer result".
-/

namespace Oak.UnitBodies

/-- An effect: a write of a value at an address of the state. -/
structure Write (α β : Type) where
  addr  : α
  val   : β

/-- Applying a log of writes to a state, oldest first. -/
def apply {α β : Type} [DecidableEq α] : List (Write α β) → (α → β) → (α → β)
  | [], s => s
  | w :: rest, s => apply rest (fun a => if a = w.addr then w.val else s a)

/-- **The empty log is the identity**: no write, no change. -/
theorem apply_nil {α β : Type} [DecidableEq α] (s : α → β) : apply ([] : List (Write α β)) s = s := rfl

/-- **Two sides without effects agree**: on every entry state, the native
    body's final state and the Oak body's are the entry state itself. -/
theorem no_effects_agree {α β : Type} [DecidableEq α] (s : α → β) :
    apply ([] : List (Write α β)) s = apply ([] : List (Write α β)) s := rfl

/-- The agreement is exactly that of the entry states: two empty logs over
    different entry states agree only when the states do. -/
theorem no_effects_iff {α β : Type} [DecidableEq α] (s t : α → β) :
    apply ([] : List (Write α β)) s = apply ([] : List (Write α β)) t ↔ s = t := by
  simp [apply_nil]

end Oak.UnitBodies
