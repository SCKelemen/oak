namespace Oak.Unsafe

/-! # Unsafe boundary discipline

Model for the unsafe boundary of `docs/spec/00-constitution.md` and
`docs/spec/50-borrowing.md`: `unsafe` does not disable checking — it admits
narrowly scoped assumptions the compiler cannot establish itself, and every
unrelated invariant remains checked. The v1 assumption vocabulary contains
exactly the writable-disjointness assumption of `50-borrowing` section 6:
writable regions whose disjointness cannot be proven are rejected in safe
code and admissible only inside an unsafe boundary, where the compiler
records the assumption instead of silently dropping the obligation. -/

/-- The obligations the compiler discharges for safe code. -/
inductive Obligation where
  | typing
  | bounds
  | borrowExclusivity
  | writableDisjointness
  | effects
  deriving DecidableEq, Repr

/-- The assumptions an unsafe boundary may admit. -/
inductive Assumption where
  | disjointWritable
  deriving DecidableEq, Repr

/-- Which obligation a given assumption discharges. Each assumption is
    narrow: it discharges exactly one obligation kind. -/
def discharges : Assumption → Obligation → Bool
  | .disjointWritable, .writableDisjointness => true
  | .disjointWritable, _ => false

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

/-- The disjointness assumption discharges only the writable-disjointness
    obligation; typing, bounds, exclusivity, and effects remain checked
    inside every unsafe boundary. -/
theorem assumption_is_narrow {o : Obligation}
    (h : discharges .disjointWritable o = true) :
    o = .writableDisjointness := by
  cases o <;> simp [discharges] at h ⊢

/-- Consequently, no assumption in the vocabulary can admit an unrelated
    obligation, at any unsafe depth. -/
theorem unrelated_obligations_remain (s : Scope) (a : Assumption)
    {o : Obligation} (h : o ≠ .writableDisjointness) :
    ¬ Admits s a o := by
  intro ⟨_, hdis⟩
  cases a
  exact h (assumption_is_narrow hdis)

/-- Entering an unsafe boundary enables admission of the assumption's own
    obligation. -/
theorem enter_enables_admission (s : Scope) :
    Admits (enter s) .disjointWritable .writableDisjointness := by
  refine ⟨?_, rfl⟩
  show 0 < s.unsafeDepth + 1
  omega

/-- Leaving the last unsafe boundary ends admission: the assumption is
    lexically scoped and does not leak into the surrounding safe code. -/
theorem exit_ends_admission (a : Assumption) (o : Obligation) :
    ¬ Admits (exit ⟨1⟩) a o := by
  intro ⟨hdepth, _⟩
  simp [exit] at hdepth

end Oak.Unsafe
