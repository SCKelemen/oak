/-!
# Oak.EffectRows — effect rows on function types

Model of docs/spec/60-effects-allocation.md section 2a (compiler/effects.go,
`checkEffectRows`). A program has functions `F`; each has the effects it
declares itself, the functions it calls by name, and the *slots* `S` through
which it calls function values — parameters or locals whose type carries an
effect row. A run installs a concrete function in every slot. The row check
admits a run only when each installed function's static bound lies inside
its slot's row.

* `bound` is what the compiler computes for a function: its own effects, the
  rows of its slots, and the bounds of its callees (fuel-indexed; a program
  is finite, so some fuel reaches the fixed point).
* `perform` is what a run may perform: own effects, callees, and whatever
  the installed functions perform.
* `perform_subset_bound`: under the row check, everything a run performs is
  in the static bound, so `forbids_sound`: a `forbids { E }` on a function
  whose bound excludes `E` holds for every admitted run. Without a row the
  compiler has no bound for a value call and fails closed (`OAK-E0103`),
  which this model does not need to represent.
-/

namespace Oak.EffectRows

structure Program (F S E : Type) where
  own : F → List E
  callees : F → List F
  slots : F → List S
  row : S → List E

variable {F S E : Type}

/-- The static bound of a function's effects, as the compiler computes it. -/
def bound (P : Program F S E) : Nat → F → List E
  | 0, _ => []
  | n + 1, f => P.own f ++ (P.slots f).flatMap P.row ++ (P.callees f).flatMap (bound P n)

/-- What a run with the slots filled by `σ` may perform. -/
def perform (P : Program F S E) (σ : S → F) : Nat → F → List E
  | 0, _ => []
  | n + 1, f =>
    P.own f ++ (P.callees f).flatMap (perform P σ n) ++
      (P.slots f).flatMap (fun s => perform P σ n (σ s))

/-- The row check: every installed function's bound is inside its slot's row. -/
def Admitted (P : Program F S E) (σ : S → F) : Prop :=
  ∀ f, ∀ s ∈ P.slots f, ∀ n, bound P n (σ s) ⊆ P.row s

/-- **Rows are sound.** Under the row check, a run performs only effects in
the static bound. -/
theorem perform_subset_bound (P : Program F S E) (σ : S → F) (h : Admitted P σ) :
    ∀ n f, perform P σ n f ⊆ bound P n f := by
  intro n
  induction n with
  | zero => intro f; simp [perform, bound]
  | succ n ih =>
    intro f e he
    simp only [perform, List.mem_append, List.mem_flatMap] at he
    simp only [bound, List.mem_append, List.mem_flatMap]
    rcases he with (hown | ⟨g, hg, hge⟩) | ⟨s, hs, hse⟩
    · exact Or.inl (Or.inl hown)
    · exact Or.inr ⟨g, hg, ih g hge⟩
    · exact Or.inl (Or.inr ⟨s, hs, h f s hs n (ih (σ s) hse)⟩)

/-- **`forbids` sees through rows.** An effect outside a function's bound is
never performed by an admitted run. -/
theorem forbids_sound (P : Program F S E) (σ : S → F) (h : Admitted P σ) (f : F) (e : E)
    (n : Nat) (hf : e ∉ bound P n f) : e ∉ perform P σ n f :=
  fun he => hf (perform_subset_bound P σ h n f he)

end Oak.EffectRows
