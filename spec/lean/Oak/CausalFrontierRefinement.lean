import Oak.CausalFrontier

namespace Oak.CausalFrontier.Refinement

/-- Mirrors the Oak source expression used by `causal_frontier_join_into` for
    one component: `left < right ? right | left`. -/
def execJoinComponent (left right : Nat) : Nat :=
  if left < right then right else left

/-- The executable branch expression is exactly pointwise maximum. -/
theorem execJoinComponent_eq_max (left right : Nat) :
    execJoinComponent left right = max left right := by
  by_cases h : left < right
  · simp [execJoinComponent, h, Nat.max_eq_right (Nat.le_of_lt h)]
  · have hrle : right ≤ left := Nat.le_of_not_gt h
    simp [execJoinComponent, h, Nat.max_eq_left hrle]

/-- Pointwise lifting of the Oak join loop body. The surrounding loop only
    visits each bounded actor slot once, so this is its mathematical result. -/
def execJoin {n : Nat} (left right : Frontier n) : Frontier n :=
  fun i => execJoinComponent (left i) (right i)

/-- The executable join algorithm refines the normative pointwise-max model. -/
theorem execJoin_refines_join {n : Nat} (left right : Frontier n) :
    execJoin left right = join left right := by
  funext i
  exact execJoinComponent_eq_max (left i) (right i)

/-- Mirrors the per-component comparison accumulated by
    `causal_frontier_le`. -/
def execLe {n : Nat} (left right : Frontier n) : Prop :=
  ∀ i, left i ≤ right i

/-- The executable comparison result is the normative pointwise order. -/
theorem execLe_refines_LE {n : Nat} (left right : Frontier n) :
    execLe left right ↔ LE left right := by
  rfl

/-- Mirrors `causal_frontier_covers` after its actor-bounds check. -/
def execCovers {n : Nat} (frontier : Frontier n) (actor : Fin n) (seq : Nat) : Prop :=
  seq ≤ frontier actor

/-- Coverage in the executable algorithm is exactly model coverage. -/
theorem execCovers_refines_covers {n : Nat} (frontier : Frontier n)
    (actor : Fin n) (seq : Nat) :
    execCovers frontier actor seq ↔ covers frontier actor seq := by
  rfl

/-- Mirrors the Oak source expression used by `causal_frontier_observe` for
    the selected actor component. -/
def execObserveComponent (current seq : Nat) : Nat :=
  if current < seq then seq else current

/-- Observe is precisely a monotone pointwise maximum update. -/
theorem execObserveComponent_eq_max (current seq : Nat) :
    execObserveComponent current seq = max current seq := by
  exact execJoinComponent_eq_max current seq

/-- Re-observing an older/equal sequence cannot regress the frontier. -/
theorem execObserveComponent_monotone (current seq : Nat) :
    current ≤ execObserveComponent current seq := by
  rw [execObserveComponent_eq_max]
  exact Nat.le_max_left _ _

/-- After observing a sequence, that event dot is covered at the selected
    actor component. -/
theorem execObserveComponent_covers (current seq : Nat) :
    seq ≤ execObserveComponent current seq := by
  rw [execObserveComponent_eq_max]
  exact Nat.le_max_right _ _

end Oak.CausalFrontier.Refinement
