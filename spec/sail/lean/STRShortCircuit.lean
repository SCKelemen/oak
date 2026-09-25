import Init

/-!
The pinned Sail Lean exporter lifts Boolean operands eagerly. Its interpreter
and Lem Boolean operations instead short-circuit. These laws justify the
explicit conditional-action form used for the two pinned export conditions;
they do not establish a general Sail-to-Lean compiler refinement.
-/

namespace STRExecution.ShortCircuit

def guardedAnd (left right : EStateM Error State Bool) : EStateM Error State Bool := do
  let value ← left
  if value then right else pure false

def guardedOr (left right : EStateM Error State Bool) : EStateM Error State Bool := do
  let value ← left
  if value then pure true else right

/-- The inner `do` delimits nested-action lifting before Boolean selection. -/
def normalizedAnd (left right : EStateM Error State Bool) : EStateM Error State Bool := do
  pure (← do if (← left) then pure (← right) else pure false)

def normalizedOr (left right : EStateM Error State Bool) : EStateM Error State Bool := do
  pure (← do if (← left) then pure true else pure (← right))

theorem normalized_and (left right : EStateM Error State Bool) :
    normalizedAnd left right = guardedAnd left right := by
  funext state
  cases result : left state with
  | ok value afterLeft =>
    cases value <;>
      simp [normalizedAnd, guardedAnd, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, result]
    cases right afterLeft <;> rfl
  | error error afterLeft =>
    simp [normalizedAnd, guardedAnd, Bind.bind, EStateM.bind,
      result]

theorem normalized_or (left right : EStateM Error State Bool) :
    normalizedOr left right = guardedOr left right := by
  funext state
  cases result : left state with
  | ok value afterLeft =>
    cases value <;>
      simp [normalizedOr, guardedOr, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, result]
    cases right afterLeft <;> rfl
  | error error afterLeft =>
    simp [normalizedOr, guardedOr, Bind.bind, EStateM.bind,
      result]

namespace Examples

private def left (value : Bool) : EStateM String Nat Bool :=
  fun state => .ok value (state + 1)

private def poison : EStateM String Nat Bool :=
  fun state => .error "poison" (state + 100)

/-- This is the exact uncorrected backend shape, not the production export. -/
private def eagerAnd (a b : EStateM String Nat Bool) : EStateM String Nat Bool := do
  pure ((← a) && (← b))

private def eagerOr (a b : EStateM String Nat Bool) : EStateM String Nat Bool := do
  pure ((← a) || (← b))

theorem eager_and_counterexample :
    (eagerAnd (left false) poison).run 0 = .error "poison" 101 := rfl
theorem eager_or_counterexample :
    (eagerOr (left true) poison).run 0 = .error "poison" 101 := rfl
theorem and_skips_poison :
    (normalizedAnd (left false) poison).run 0 = .ok false 1 := rfl
theorem or_skips_poison :
    (normalizedOr (left true) poison).run 0 = .ok true 1 := rfl
theorem and_keeps_right_error :
    (normalizedAnd (left true) poison).run 0 = .error "poison" 101 := rfl
theorem or_keeps_right_error :
    (normalizedOr (left false) poison).run 0 = .error "poison" 101 := rfl
theorem and_keeps_left_error :
    (normalizedAnd poison (left true)).run 0 = .error "poison" 100 := rfl
theorem or_keeps_left_error :
    (normalizedOr poison (left true)).run 0 = .error "poison" 100 := rfl

end Examples

/-- info: 'STRExecution.ShortCircuit.normalized_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_and
/-- info: 'STRExecution.ShortCircuit.normalized_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_or
/-- info: 'STRExecution.ShortCircuit.Examples.and_skips_poison' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.and_skips_poison
/-- info: 'STRExecution.ShortCircuit.Examples.or_skips_poison' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.or_skips_poison
/-- info: 'STRExecution.ShortCircuit.Examples.eager_and_counterexample' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.eager_and_counterexample
/-- info: 'STRExecution.ShortCircuit.Examples.eager_or_counterexample' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.eager_or_counterexample

end STRExecution.ShortCircuit
