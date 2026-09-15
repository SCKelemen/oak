/-!
# Copies at the boundary

The native lane's two copy elisions at the call and return boundary
(docs/spec/94-assembler.md §9 "Copies at the boundary"). A by-reference
aggregate argument the callee only reads is passed as the address of the
caller's own storage: the callee's reads through that address are the
reads it would have made of a copy, since nothing writes the storage
during the call. A record local the function returns is built in the
caller's result area: the writes that build it, made at the area's
address, leave the area holding what a copy of the finished local would
have put there.
-/

namespace Oak.BoundaryCopies

/-- Memory: words by address. -/
def Mem := Nat → Nat

/-- A store of `v` at `a`. -/
def store (m : Mem) (a v : Nat) : Mem := fun x => if x = a then v else m x

/-- The callee's copy of an aggregate of `size` words at `src`, laid at
address zero: word `k` of the copy is word `src + k` of the caller. -/
def copyOf (m : Mem) (src : Nat) : Mem := fun k => m (src + k)

/-- Reading the copy at `k` is reading the caller's storage at `src + k`:
with no store to the storage during the call, the callee's reads through
the caller's address are the reads of the copy. -/
theorem read_in_place (m : Mem) (src k : Nat) : copyOf m src k = m (src + k) := rfl

/-- The writes that build an aggregate, as (offset, value) pairs applied
at a base address. -/
def build (ws : List (Nat × Nat)) (m : Mem) (base : Nat) : Mem :=
  ws.foldl (fun acc w => store acc (base + w.1) w.2) m

/-- Building at one base and building at another agree word for word when
the two memories agree word for word under the bases: the finished
aggregate's content does not depend on where it was built. So a local
built in the result area (base `dst`) holds, at each offset, what a
local built in the frame (base `tmp`) and then copied to `dst` would. -/
theorem build_in_place (ws : List (Nat × Nat)) (m m' : Mem) (dst tmp : Nat)
    (agree : ∀ k, m (dst + k) = m' (tmp + k)) :
    ∀ k, build ws m dst (dst + k) = build ws m' tmp (tmp + k) := by
  induction ws generalizing m m' with
  | nil => intro k; exact agree k
  | cons w ws ih =>
    intro k
    apply ih
    intro j
    simp only [store]
    by_cases h : j = w.1
    · subst h; simp
    · have h1 : dst + j ≠ dst + w.1 := fun e => h (Nat.add_left_cancel e)
      have h2 : tmp + j ≠ tmp + w.1 := fun e => h (Nat.add_left_cancel e)
      simp [h1, h2, agree j]

end Oak.BoundaryCopies
