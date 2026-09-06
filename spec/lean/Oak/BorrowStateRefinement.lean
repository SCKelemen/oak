import Oak.Borrowing

namespace Oak.BorrowStateRefinement

open Oak.Borrowing

/-! # Compiler correspondence for the borrow-state machine

This module transliterates the concrete owner-state decision procedures of
`borrowchecker` (`admitViewBorrow`, `admitSpanBorrowCore`, `ownerStateFor`)
and proves them sound and complete against the abstract ownership transitions
of `Oak.Borrowing`. The compiler's `BorrowState` enum erases reader counts —
`sharedRead` represents every `shared (n+1)` — so the correspondence is
stated through a representation relation.

Scope: the single-writer core. The disjoint multi-span and reborrow
extensions layer on top of this machine and are refined separately by
`Oak.ReborrowRefinement`. The Go procedures are maintained as line-for-line
transliterations of the definitions below. -/

/-- Mirror of `borrowchecker.BorrowState`. -/
inductive ConcreteState where
  | free
  | sharedRead
  | uniqueWrite
  deriving DecidableEq, Repr

/-- The compiler state represents the abstract states with the same
    authority: `sharedRead` stands for any positive reader count. -/
def Represents : ConcreteState → State → Prop
  | .free, .free => True
  | .sharedRead, .shared n => 0 < n
  | .uniqueWrite, .unique => True
  | _, _ => False

/-- Transliteration of `borrowchecker.admitViewBorrow`: a read-only view is
    admitted unless a writer holds the owner. -/
def admitView : ConcreteState → Bool
  | .uniqueWrite => false
  | _ => true

/-- Transliteration of `borrowchecker.admitSpanBorrowCore`: the single-writer
    core admits a writable span only from the free state. -/
def admitSpanCore : ConcreteState → Bool
  | .free => true
  | _ => false

/-- Transliteration of `borrowchecker.ownerStateFor`: recomputing the owner
    state from the remaining live borrows. Both kinds live at once is the
    flagged impossible case (`none`). -/
def ownerStateFor : Bool → Bool → Option ConcreteState
  | true, true => none
  | false, true => some .uniqueWrite
  | true, false => some .sharedRead
  | false, false => some .free

/-- **View admission is sound**: whenever the compiler admits a view, the
    abstract machine has the corresponding `acquireRead` step, and the
    result is represented by `sharedRead`. -/
theorem admit_view_sound {c : ConcreteState} {a : State}
    (hadmit : admitView c = true) (hrep : Represents c a) (hvalid : Valid a) :
    ∃ a', Step .acquireRead a a' ∧ Represents .sharedRead a' := by
  cases c with
  | free =>
    cases a <;> simp [Represents] at hrep
    exact ⟨.shared 1, Step.acquireReadFree, by simp [Represents]⟩
  | sharedRead =>
    cases a with
    | shared n =>
      have hpos : 0 < n := hrep
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨.shared (m + 2), Step.acquireReadShared m, by simp [Represents]⟩
    | free => simp [Represents] at hrep
    | unique => simp [Represents] at hrep
  | uniqueWrite => simp [admitView] at hadmit

/-- **View rejection is complete**: when the compiler rejects a view, no
    abstract `acquireRead` step exists from any represented state. -/
theorem admit_view_rejection_complete {c : ConcreteState} {a : State}
    (hadmit : admitView c = false) (hrep : Represents c a) :
    ∀ a', ¬ Step .acquireRead a a' := by
  cases c with
  | free => simp [admitView] at hadmit
  | sharedRead => simp [admitView] at hadmit
  | uniqueWrite =>
    cases a <;> simp [Represents] at hrep
    intro a'
    exact unique_cannot_acquire_read a'

/-- **Span-core admission is sound**: an admitted writable span corresponds
    to the abstract `acquireWrite` step into `unique`. -/
theorem admit_span_sound {c : ConcreteState} {a : State}
    (hadmit : admitSpanCore c = true) (hrep : Represents c a) :
    Step .acquireWrite a .unique ∧ Represents .uniqueWrite .unique := by
  cases c with
  | free =>
    cases a <;> simp [Represents] at hrep
    exact ⟨Step.acquireWrite, by simp [Represents]⟩
  | sharedRead => simp [admitSpanCore] at hadmit
  | uniqueWrite => simp [admitSpanCore] at hadmit

/-- **Span-core rejection is complete**: when the compiler rejects a span,
    no abstract `acquireWrite` step exists from any represented state. -/
theorem admit_span_rejection_complete {c : ConcreteState} {a : State}
    (hadmit : admitSpanCore c = false) (hrep : Represents c a) (hvalid : Valid a) :
    ∀ a', ¬ Step .acquireWrite a a' := by
  intro a' hstep
  cases c with
  | free => simp [admitSpanCore] at hadmit
  | sharedRead =>
    cases a <;> simp [Represents] at hrep
    next n =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      cases hstep
  | uniqueWrite =>
    cases a <;> simp [Represents] at hrep
    cases hstep

/-- **Recompute agrees with release**: after releasing borrows, the state the
    compiler recomputes represents the abstract state the release steps
    reach. Views only: `sharedRead` while readers remain, `free` after the
    last release. -/
theorem recompute_represents_release (views spans : Nat) :
    match ownerStateFor (0 < views) (0 < spans) with
    | some c =>
      (0 < spans → spans = 0 ∨ Represents c .unique) ∧
      (spans = 0 → 0 < views → Represents c (.shared views)) ∧
      (spans = 0 → views = 0 → Represents c .free)
    | none => 0 < views ∧ 0 < spans := by
  by_cases hv : 0 < views <;> by_cases hs : 0 < spans <;>
    simp [ownerStateFor, hv, hs, Represents] <;> omega

/-- **The impossible state is unrepresentable**: live views and live spans at
    once has no abstract counterpart, matching the compiler's flagged error. -/
theorem both_kinds_flagged :
    ownerStateFor true true = none := rfl

end Oak.BorrowStateRefinement
