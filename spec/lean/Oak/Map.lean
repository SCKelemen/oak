/-!
# Verified map vectorization

`nativegen/vector_map.go` (docs/spec/94-assembler.md §9 "Map
vectorization") rewrites an element-wise map over two spans of the same
length — or one span in place — before lowering,

    while i < len(a) { dst[i] = f(a[i]); i = i + 1 }

into a main loop that maps each block of `L` elements as one vector
(`simd.load`, the lane-wise operations, `simd.store`) under the slack guard
`len(a) >= L && i <= len(a) - L`, and the remainder loop as written. The
verifier proves the assembly against the rewritten body; this file is the
rewrite's own correctness: over the list of the source span's elements,
the blocked map equals the element-wise map. Nothing is assumed of `f`
beyond being a function of one element — each simd operation is lane-wise
by its specification (docs/spec/93-simd.md §1), so the vector's lane `k`
holds `f` of element `i + k`. No law of the element type is used, which is
why floats vectorize here where a reduction's would not.
-/

namespace Oak.Map

/-- The rewritten loops with a trip budget: while at least `L` elements
    remain (and `L` is positive), one block of `L` is mapped as a vector
    and the loop continues past it; otherwise the remainder is mapped one
    element at a time. The budget is the loop's trip bound; `blocked`
    below spends the list's length, which every run stays within. -/
def blockedFuel {α β : Type} (L : Nat) (f : α → β) : Nat → List α → List β
  | 0, l => l.map f
  | n + 1, l =>
    if L ≤ l.length ∧ 0 < L then (l.take L).map f ++ blockedFuel L f n (l.drop L)
    else l.map f

/-- The rewritten loops over the elements. -/
def blocked {α β : Type} (L : Nat) (f : α → β) (l : List α) : List β :=
  blockedFuel L f l.length l

/-- One block: the first `L` elements mapped as one vector, followed by
    the rest mapped as the loops continue, is the element-wise map. -/
theorem block_eq {α β : Type} (L : Nat) (f : α → β) (l : List α) :
    (l.take L).map f ++ (l.drop L).map f = l.map f := by
  rw [← List.map_append, List.take_append_drop]

theorem blockedFuel_eq {α β : Type} (L : Nat) (f : α → β) :
    ∀ (n : Nat) (l : List α), blockedFuel L f n l = l.map f := by
  intro n
  induction n with
  | zero => intro l; rfl
  | succ n ih =>
    intro l
    simp only [blockedFuel]
    split
    · rw [ih, block_eq]
    · rfl

/-- The blocked map equals the element-wise map: the memory the vector
    main loop and the scalar remainder leave in `dst` is the memory the
    scalar loop leaves. -/
theorem blocked_eq {α β : Type} (L : Nat) (f : α → β) (l : List α) :
    blocked L f l = l.map f :=
  blockedFuel_eq L f l.length l

end Oak.Map
