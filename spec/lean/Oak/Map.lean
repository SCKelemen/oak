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

/-- Two consecutive vector blocks followed by the remaining elements.
    This law preserves the order and never reassociates element arithmetic. -/
theorem two_blocks_eq {α β : Type} (L : Nat) (f : α → β) (l : List α) :
    (l.take L).map f ++ (l.drop L |>.take L).map f ++
      (l.drop L |>.drop L).map f = l.map f := by
  rw [List.append_assoc, block_eq, block_eq]

/-- Two vectors per main-loop trip, then ordinary single-vector cleanup.
    The guard covers both blocks; cleanup keeps short inputs vectorized. -/
def groupedFuel {α β : Type} (L : Nat) (f : α → β) : Nat → List α → List β
  | 0, l => blocked L f l
  | n + 1, l =>
    if 2 * L ≤ l.length ∧ 0 < L then
      (l.take L).map f ++ (l.drop L |>.take L).map f ++
        groupedFuel L f n (l.drop L |>.drop L)
    else blocked L f l

def grouped {α β : Type} (L : Nat) (f : α → β) (l : List α) : List β :=
  groupedFuel L f l.length l

theorem groupedFuel_eq {α β : Type} (L : Nat) (f : α → β) :
    ∀ (n : Nat) (l : List α), groupedFuel L f n l = l.map f := by
  intro n
  induction n with
  | zero => intro l; exact blocked_eq L f l
  | succ n ih =>
    intro l
    simp only [groupedFuel]
    split
    · rw [ih, two_blocks_eq]
    · exact blocked_eq L f l

/-- The two-vector loop, single-vector cleanup and scalar tail implement
    the same element-wise map. -/
theorem grouped_eq {α β : Type} (L : Nat) (f : α → β) (l : List α) :
    grouped L f l = l.map f :=
  groupedFuel_eq L f l.length l

/-- The main-loop slack guard bounds both vector blocks and the updated
    index. Taking `limit = 2^32 - 1` excludes unsigned index wraparound. -/
theorem grouped_bounds (i n L limit : Nat)
    (hn : n ≤ limit) (hL : 2 * L ≤ n) (hi : i ≤ n - 2 * L) :
    i + L + L ≤ n ∧ i + 2 * L ≤ limit := by
  omega

end Oak.Map
