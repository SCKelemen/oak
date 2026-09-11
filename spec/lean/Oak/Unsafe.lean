namespace Oak.Unsafe

/-! # Unsafe boundary discipline

Model for the unsafe boundary of `docs/spec/00-constitution.md` and
`docs/spec/50-borrowing.md`: `unsafe` does not disable checking — it admits
narrowly scoped assumptions the compiler cannot establish itself, and every
unrelated invariant remains checked. The assumption vocabulary contains
exactly two entries: the writable-disjointness assumption of `50-borrowing`
section 6 — writable regions whose disjointness cannot be proven are rejected
in safe code and admissible only inside an unsafe boundary — and the foreign
buffer contract of `92-ffi` section 2.7 — an inbound buffer borrow asserts
that a runtime pointer addresses the stated count of elements, valid and
unaliased for writes for the block's extent. In both cases the compiler
records the assumption instead of silently dropping the obligation. -/

/-- The obligations the compiler discharges for safe code. -/
inductive Obligation where
  | typing
  | bounds
  | borrowExclusivity
  | writableDisjointness
  | foreignValidity
  | effects
  deriving DecidableEq, Repr

/-- The assumptions an unsafe boundary may admit. -/
inductive Assumption where
  | disjointWritable
  | foreignBuffer
  deriving DecidableEq, Repr

/-- The one obligation each assumption is about. -/
def target : Assumption → Obligation
  | .disjointWritable => .writableDisjointness
  | .foreignBuffer => .foreignValidity

/-- Which obligation a given assumption discharges. Each assumption is
    narrow: it discharges exactly one obligation kind, its target. -/
def discharges (a : Assumption) (o : Obligation) : Bool := decide (o = target a)

/-- Lexical unsafe nesting. Safe code has depth zero. -/
structure Scope where
  unsafeDepth : Nat
  deriving DecidableEq, Repr

def enter (s : Scope) : Scope := ⟨s.unsafeDepth + 1⟩

def exit (s : Scope) : Scope := ⟨s.unsafeDepth - 1⟩

/-- An obligation may be admitted (assumed rather than proven) only inside an
    unsafe scope, and only by an assumption that discharges exactly it. -/
def Admits (s : Scope) (a : Assumption) (o : Obligation) : Prop :=
  0 < s.unsafeDepth ∧ discharges a o = true

/-- Safe code admits nothing: every obligation must be proven. -/
theorem safe_code_admits_nothing (a : Assumption) (o : Obligation) :
    ¬ Admits ⟨0⟩ a o := by
  intro ⟨hdepth, _⟩
  simp at hdepth

/-- Each assumption discharges only its target: the disjointness assumption
    only writable disjointness, the foreign buffer contract only the validity
    of the borrowed foreign memory. Typing, bounds, exclusivity, and effects
    remain checked inside every unsafe boundary, and neither assumption
    reaches the other's obligation. -/
theorem assumption_is_narrow (a : Assumption) {o : Obligation}
    (h : discharges a o = true) : o = target a := by
  simpa [discharges] using h

/-- Consequently, no assumption in the vocabulary can admit an unrelated
    obligation, at any unsafe depth. -/
theorem unrelated_obligations_remain (s : Scope) (a : Assumption)
    {o : Obligation} (h : o ≠ target a) :
    ¬ Admits s a o := by
  intro ⟨_, hdis⟩
  exact h (assumption_is_narrow a hdis)

/-- The two assumptions are about different obligations: admitting the
    foreign buffer contract never admits writable disjointness, and the
    reverse. -/
theorem assumptions_do_not_overlap (s : Scope) :
    ¬ Admits s .foreignBuffer .writableDisjointness ∧
    ¬ Admits s .disjointWritable .foreignValidity :=
  ⟨unrelated_obligations_remain s .foreignBuffer (by decide),
   unrelated_obligations_remain s .disjointWritable (by decide)⟩

/-- Entering an unsafe boundary enables admission of each assumption's own
    obligation. -/
theorem enter_enables_admission (s : Scope) (a : Assumption) :
    Admits (enter s) a (target a) := by
  refine ⟨?_, by simp [discharges]⟩
  show 0 < s.unsafeDepth + 1
  omega

/-- Leaving the last unsafe boundary ends admission: the assumption is
    lexically scoped and does not leak into the surrounding safe code. -/
theorem exit_ends_admission (a : Assumption) (o : Obligation) :
    ¬ Admits (exit ⟨1⟩) a o := by
  intro ⟨hdepth, _⟩
  simp [exit] at hdepth

end Oak.Unsafe
