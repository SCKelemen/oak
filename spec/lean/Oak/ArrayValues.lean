/-!
# Owned arrays as values

The native lane's model of an owned array of scalars `[N]T` crossing the
function boundary (docs/spec/94-assembler.md §9, forty-seventh increment):
the array is the one-field composite the C backend's wrapper struct is, so
the record rules apply unchanged — leaves at `k * size`, register chunks of
eight bytes up to sixteen, by reference beyond — and the verifier names its
leaves `p[k]`, as the Oak side names the elements of an array-typed
aggregate.
-/

namespace Oak.ArrayValues

/-- The byte offset of element `k` of an array whose elements take `size`
bytes: the composite's single array field lies at offset zero. -/
def leafOffset (size k : Nat) : Nat := k * size

/-- Every element lies inside the composite of `n` elements. -/
theorem leaf_inside (size n k : Nat) (hk : k < n) :
    leafOffset size k + size ≤ n * size := by
  unfold leafOffset
  have h : (k + 1) * size ≤ n * size := Nat.mul_le_mul_right size hk
  rw [Nat.succ_mul] at h
  exact h

/-- Distinct elements occupy disjoint byte ranges: the earlier one ends
before the later one begins. -/
theorem leaf_disjoint (size i j : Nat) (hij : i < j) :
    leafOffset size i + size ≤ leafOffset size j := by
  unfold leafOffset
  have h : (i + 1) * size ≤ j * size := Nat.mul_le_mul_right size hij
  rw [Nat.succ_mul] at h
  exact h

/-- The register chunk an element lands in when the composite travels by
value (AAPCS64: eight-byte chunks). -/
def chunkOf (size k : Nat) : Nat := leafOffset size k / 8

/-- A composite of at most sixteen bytes travels in at most two chunks:
every element of such an array lands in chunk 0 or chunk 1. -/
theorem chunk_lt_two (size n k : Nat) (hk : k < n) (hs : 0 < size)
    (h16 : n * size ≤ 16) : chunkOf size k < 2 := by
  unfold chunkOf
  have h := leaf_inside size n k hk
  have : leafOffset size k < 16 := by omega
  omega

/-- The composite's size is exact: `n` elements of `size` bytes, no
padding (the wrapper struct's alignment is the element's). -/
theorem size_exact (size n : Nat) : n * size = leafOffset size n := by
  unfold leafOffset; rfl

/-- Homogeneous floating-point aggregates (AAPCS64 §5.9.5.3): an array of
floats counts its elements as members, so it is an HFA exactly when it has
at most four — `[4]f32` travels in `v` registers, `[8]f32` by reference. -/
def isHFA (float : Bool) (n : Nat) : Bool := float && decide (n ≤ 4)

theorem isHFA_float (n : Nat) : isHFA true n = decide (n ≤ 4) := by
  simp [isHFA]

theorem isHFA_int (n : Nat) : isHFA false n = false := by
  simp [isHFA]

/-- The verifier's leaf name for element `k` of a composite's array field
(`compositeLeaves`): `p.f[k]` for a named field, `p[k]` for the array
itself (the empty field name). -/
def compositeLeafName (field root : String) (k : Nat) : String :=
  if field = "" then root ++ "[" ++ toString k ++ "]"
  else root ++ "." ++ field ++ "[" ++ toString k ++ "]"

/-- The Oak side's name for element `k` of an array-typed aggregate
(`aggregateFrom`). -/
def aggregateLeafName (root : String) (k : Nat) : String :=
  root ++ "[" ++ toString k ++ "]"

/-- The two sides name an array value's leaves alike, so a parameter's
element read binds to the leaf the chunks or the referenced copy carry. -/
theorem leaf_names_agree (root : String) (k : Nat) :
    compositeLeafName "" root k = aggregateLeafName root k := by
  simp [compositeLeafName, aggregateLeafName]

end Oak.ArrayValues
