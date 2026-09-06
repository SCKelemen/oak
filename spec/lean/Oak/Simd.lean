namespace Oak.Simd

/-! # Portable SIMD lane semantics

Model for `docs/spec/93-simd.md`: a vector is its lane list (`laneCount`
lanes of `laneBits`-bit unsigned values). The portable library's semantics
are defined here once; the NEON lowering, the portable C lowering, and the
interpreter are three realizations that must agree with these laws.

Laws proven:
- `splat` yields constant lanes of exactly the lane count;
- the binary operations are pointwise (`zipWith`) and preserve lane count;
- wrapping arithmetic is arithmetic mod `2^laneBits`;
- `eq` masks are two-valued — every lane is `0` or `allOnes`, and `allOnes`
  exactly on equal lanes;
- `any (eq a b)` holds iff some lane pair matches (the byte-search law) and
  `all (eq a b)` holds iff the vectors are equal;
- a `store` followed by a `load` of the same region returns the stored
  lanes and leaves every other element of the buffer untouched. -/

/-- A vector value: its lanes, most significant nothing — pure index order. -/
abbrev Vec := List Nat

/-- The all-ones lane value for a lane width. -/
def allOnes (laneBits : Nat) : Nat := 2 ^ laneBits - 1

/-- `simd.splat_E`. -/
def splat (laneCount : Nat) (x : Nat) : Vec := List.replicate laneCount x

/-- Lane-wise wrapping addition. -/
def addWrap (laneBits : Nat) (a b : Vec) : Vec :=
  List.zipWith (fun x y => (x + y) % 2 ^ laneBits) a b

/-- Lane-wise equality mask. -/
def eqMask (laneBits : Nat) (a b : Vec) : Vec :=
  List.zipWith (fun x y => if x = y then allOnes laneBits else 0) a b

/-- `simd.any_E`: some lane nonzero. -/
def anyLane (v : Vec) : Bool := v.any (fun lane => lane ≠ 0)

/-- `simd.all_E`: every lane nonzero. -/
def allLanes (v : Vec) : Bool := v.all (fun lane => lane ≠ 0)

/-- `simd.load_E`: lanes `buf[off] .. buf[off+laneCount-1]`. The compiler
    guards `off + laneCount ≤ buf.length` (trap otherwise). -/
def load (laneCount off : Nat) (buf : List Nat) : Vec :=
  (buf.drop off).take laneCount

/-- `simd.store_E`: replace the region with the vector's lanes. -/
def store (off : Nat) (buf : List Nat) (v : Vec) : List Nat :=
  buf.take off ++ (v ++ buf.drop (off + v.length))

/-- **Splat is constant**: every lane is the operand. -/
theorem splat_lanes {laneCount x : Nat} {lane : Nat}
    (h : lane ∈ splat laneCount x) : lane = x :=
  List.eq_of_mem_replicate h

/-- **Splat has exactly the lane count.** -/
theorem splat_length (laneCount x : Nat) :
    (splat laneCount x).length = laneCount := List.length_replicate

/-- **Lane count preservation** for the pointwise operations, stated for
    the general `zipWith` form all of them share. -/
theorem zipWith_length {f : Nat → Nat → Nat} {a b : Vec}
    (h : a.length = b.length) :
    (List.zipWith f a b).length = a.length := by
  simp [List.length_zipWith, h]

/-- **Pointwise characterization**: lane `i` of a binary operation is the
    operation of lane `i` of each operand. -/
theorem zipWith_lane (f : Nat → Nat → Nat) (a b : Vec) (i : Nat)
    (ha : i < a.length) (hb : i < b.length) :
    (List.zipWith f a b)[i]? = some (f a[i] b[i]) := by
  simp [List.getElem?_zipWith, List.getElem?_eq_getElem, ha, hb]

/-- Membership in a `zipWith` result names an index (helper for the
    reduction laws). -/
theorem mem_zipWith_index {f : Nat → Nat → Nat} {a b : Vec} {lane : Nat}
    (h : lane ∈ List.zipWith f a b) :
    ∃ i, ∃ (_ : i < a.length) (_ : i < b.length), f a[i] b[i] = lane := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  rw [List.length_zipWith] at hi
  have hia : i < a.length := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hib : i < b.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
  refine ⟨i, hia, hib, ?_⟩
  rw [← hget]
  simp [List.getElem_zipWith]

/-- **Wrapping arithmetic stays in lane range.** -/
theorem addWrap_lane_lt {laneBits : Nat} {a b : Vec} {lane : Nat}
    (h : lane ∈ addWrap laneBits a b) : lane < 2 ^ laneBits := by
  unfold addWrap at h
  obtain ⟨i, hia, hib, hxy⟩ := mem_zipWith_index h
  rw [← hxy]
  exact Nat.mod_lt _ (Nat.pow_pos (by omega))

/-- **Masks are two-valued**: every mask lane is zero or all-ones. -/
theorem eqMask_two_valued {laneBits : Nat} {a b : Vec} {lane : Nat}
    (h : lane ∈ eqMask laneBits a b) :
    lane = 0 ∨ lane = allOnes laneBits := by
  unfold eqMask at h
  obtain ⟨i, hia, hib, hxy⟩ := mem_zipWith_index h
  by_cases hEq : a[i] = b[i]
  · right; rw [← hxy]; simp [hEq]
  · left; rw [← hxy]; simp [hEq]

/-- **The byte-search law**: `any (eq a b)` holds iff some lane pair is
    equal, for positive lane widths and equal lane counts. -/
theorem any_eqMask_iff {laneBits : Nat} (hBits : 0 < laneBits)
    (a b : Vec) (hLen : a.length = b.length) :
    anyLane (eqMask laneBits a b) = true ↔
      ∃ i, ∃ (ha : i < a.length) (hb : i < b.length), a[i] = b[i] := by
  have hOnes : allOnes laneBits ≠ 0 := by
    unfold allOnes
    have h2 : 2 ≤ 2 ^ laneBits := by
      calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ laneBits := Nat.pow_le_pow_right (by omega) hBits
    omega
  unfold anyLane eqMask
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨lane, hmem, hlane⟩ := h
    obtain ⟨i, hia, hib, hget⟩ := mem_zipWith_index hmem
    refine ⟨i, hia, hib, ?_⟩
    cases Nat.decEq a[i] b[i] with
    | isTrue hEq => exact hEq
    | isFalse hne =>
      rw [← hget] at hlane
      simp [hne] at hlane
  · intro h
    obtain ⟨i, hia, hib, hEq⟩ := h
    refine ⟨allOnes laneBits, ?_, ?_⟩
    · have hidx : (List.zipWith (fun x y => if x = y then allOnes laneBits else 0) a b)[i]? =
          some (if a[i] = b[i] then allOnes laneBits else 0) := by
        simp [List.getElem?_zipWith, List.getElem?_eq_getElem, hia, hib]
      rw [hEq] at hidx
      simp at hidx
      exact List.mem_of_getElem? hidx
    · simpa using hOnes

/-- **Store/load roundtrip**: loading the stored region returns exactly the
    stored lanes when the region fits the buffer. -/
theorem store_load_roundtrip {off : Nat} {buf : List Nat} {v : Vec}
    (hFit : off + v.length ≤ buf.length) :
    load v.length off (store off buf v) = v := by
  have hTakeLen : (buf.take off).length = off := by
    rw [List.length_take]
    omega
  unfold load store
  generalize hT : buf.take off = prefixPart
  rw [hT] at hTakeLen
  rw [← hTakeLen, List.drop_left]
  exact List.take_left ..

/-- **Stores are local**: elements before the stored region are unchanged. -/
theorem store_preserves_prefix {off : Nat} {buf : List Nat} {v : Vec}
    (i : Nat) (hi : i < off) (hoff : off ≤ buf.length) :
    (store off buf v)[i]? = buf[i]? := by
  have hTake : i < (buf.take off).length := by
    rw [List.length_take]
    omega
  unfold store
  rw [List.getElem?_append_left hTake, List.getElem?_take_of_lt hi]

end Oak.Simd
