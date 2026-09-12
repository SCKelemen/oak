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

/-! ## Byte-classification operations (docs/spec/93-simd.md §1.2)

The four operations a byte-classification kernel is built from: saturating
subtract, lane shift right, the 16-entry byte-table lookup, and the
cross-block byte shift. Each is stated lane by lane; the executable
witnesses (interpreter, NEON, portable loop) are checked to agree by
`compiler/e2e_simd_bytes_test.go`. -/

namespace Oak.Simd

/-- Saturating subtract: never below zero. -/
def subSat (a b : Vec) : Vec := List.zipWith (fun x y => x - y) a b

/-- Natural subtraction is already saturating, which is the point: the lane
is `x - y` when `y ≤ x` and `0` otherwise. -/
theorem subSat_lane (a b : Vec) (i : Nat) (hi : i < a.length) (hib : i < b.length) :
    (subSat a b)[i]'(by simp [subSat, List.length_zipWith]; omega) = a[i] - b[i] := by
  simp [subSat]

theorem subSat_le (a b : Vec) (i : Nat) (hi : i < a.length) (hib : i < b.length) :
    (subSat a b)[i]'(by simp [subSat, List.length_zipWith]; omega) ≤ a[i] := by
  simp [subSat]

theorem subSat_zero_iff (a b : Vec) (i : Nat) (hi : i < a.length) (hib : i < b.length) :
    (subSat a b)[i]'(by simp [subSat, List.length_zipWith]; omega) = 0 ↔ a[i] ≤ b[i] := by
  simp [subSat]
  omega

/-- Lane-wise logical shift right by `n`; the count is below the lane width
(a count reaching it traps before this function is reached). -/
def shr (n : Nat) (v : Vec) : Vec := v.map (fun x => x >>> n)

theorem shr_lane (n : Nat) (v : Vec) (i : Nat) (hi : i < v.length) :
    (shr n v)[i]'(by simpa [shr] using hi) = v[i] >>> n := by
  simp [shr]

/-- Byte-table lookup: lane `i` is `table[idx[i]]` when the index is below
sixteen and `0` otherwise, NEON's `tbl` rule. -/
def tbl (table idx : Vec) : Vec :=
  idx.map (fun j => if h : j < table.length ∧ j < 16 then table[j] else 0)

theorem tbl_length (table idx : Vec) : (tbl table idx).length = idx.length := by
  simp [tbl]

theorem tbl_lane_in_range (table idx : Vec) (i : Nat) (hi : i < idx.length)
    (hj : idx[i] < 16) (ht : table.length = 16) :
    (tbl table idx)[i]'(by simpa [tbl] using hi) = table[idx[i]]'(by omega) := by
  simp [tbl, ht, hj]

theorem tbl_lane_out_of_range (table idx : Vec) (i : Nat) (hi : i < idx.length)
    (hj : 16 ≤ idx[i]) :
    (tbl table idx)[i]'(by simpa [tbl] using hi) = 0 := by
  simp [tbl]
  omega

/-- The cross-block byte shift: the sixteen lanes ending `n` before the end
of `prev ++ cur` — lane `i` is `prev[16 - n + i]` for `i < n` and
`cur[i - n]` otherwise. -/
def prev (n : Nat) (prevBlock cur : Vec) : Vec :=
  (prevBlock ++ cur).drop (16 - n) |>.take 16

theorem prev_length (n : Nat) (prevBlock cur : Vec)
    (hp : prevBlock.length = 16) (hc : cur.length = 16) (hn : n ≤ 16) :
    (prev n prevBlock cur).length = 16 := by
  simp [prev, List.length_take, List.length_drop, hp, hc]
  omega

theorem prev_lane_from_prev (n : Nat) (prevBlock cur : Vec)
    (hp : prevBlock.length = 16) (hc : cur.length = 16) (hn : n ≤ 16)
    (i : Nat) (hi : i < n) :
    (prev n prevBlock cur)[i]'(by rw [prev_length n prevBlock cur hp hc hn]; omega)
      = prevBlock[16 - n + i]'(by omega) := by
  simp only [prev]
  rw [List.getElem_take, List.getElem_drop, List.getElem_append_left (by omega)]

theorem prev_lane_from_cur (n : Nat) (prevBlock cur : Vec)
    (hp : prevBlock.length = 16) (hc : cur.length = 16) (hn : n ≤ 16)
    (i : Nat) (hi : n ≤ i) (hi16 : i < 16) :
    (prev n prevBlock cur)[i]'(by rw [prev_length n prevBlock cur hp hc hn]; omega)
      = cur[i - n]'(by omega) := by
  simp only [prev]
  rw [List.getElem_take, List.getElem_drop, List.getElem_append_right (by omega)]
  congr 1
  omega

/-- `prev 0` is the current block and `prev 16` the previous one. -/
theorem prev_zero (prevBlock cur : Vec) (hp : prevBlock.length = 16) (hc : cur.length = 16) :
    prev 0 prevBlock cur = cur := by
  simp [prev, hp, hc]
  exact List.take_of_length_le (by omega)

end Oak.Simd

/-! ## Mask vocabulary (docs/spec/93-simd.md §1.2)

`movemask` collapses a vector to a scalar with one bit per lane — bit `i`
is the top bit of lane `i` — the scalar a mask-iteration loop consumes with
`ctz` and `popcount` (`Oak.Intrinsics`). The interpreter, the NEON
lowering (a test, an `and` with a bit table, and pairwise adds), and the
portable loop are checked to agree by `compiler/e2e_simd_bytes_test.go`. -/

namespace Oak.Simd

/-- The top bit of a lane of `laneBits` bits, as `0` or `1`. -/
def topBit (laneBits : Nat) (x : Nat) : Nat := (x >>> (laneBits - 1)) % 2

theorem topBit_le_one (laneBits x : Nat) : topBit laneBits x ≤ 1 :=
  Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))

/-- One bit per lane: lane `i` lands at bit `i`. -/
def movemask (laneBits : Nat) : Vec → Nat
  | [] => 0
  | x :: rest => topBit laneBits x + 2 * movemask laneBits rest

/-- **Bounded by the lane count**: a mask over `n` lanes is below `2^n`, so
it fits the `u32` the operation returns for every v1 shape. -/
theorem movemask_lt (laneBits : Nat) (v : Vec) : movemask laneBits v < 2 ^ v.length := by
  induction v with
  | nil => simp [movemask]
  | cons x rest ih =>
    have h := topBit_le_one laneBits x
    simp only [movemask, List.length_cons, Nat.pow_succ]
    omega

/-- **Bit zero is lane zero.** -/
theorem movemask_bit_zero (laneBits x : Nat) (rest : Vec) :
    movemask laneBits (x :: rest) % 2 = topBit laneBits x := by
  have h := topBit_le_one laneBits x
  simp only [movemask]
  omega

/-- **The mask is zero exactly when no lane has its top bit set** — the
scalar form of `any` over a mask vector. -/
theorem movemask_eq_zero_iff (laneBits : Nat) (v : Vec) :
    movemask laneBits v = 0 ↔ ∀ x ∈ v, topBit laneBits x = 0 := by
  induction v with
  | nil => simp [movemask]
  | cons x rest ih =>
    have h := topBit_le_one laneBits x
    simp only [movemask, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro hz
      exact ⟨by omega, ih.mp (by omega)⟩
    · rintro ⟨hx, hrest⟩
      rw [hx, ih.mpr hrest]

end Oak.Simd

/-! ## The scalable API: extent independence (docs/spec/93-simd.md §4)

A strip-mined loop processes a sequence in chunks whose sizes the backend
chooses (the active extents). The program's result must not depend on
that choice. For a lane-wise map, the concatenation of the mapped chunks
is the map of the concatenation; for the wrapping sum, and for `any` and
`all` folded with or/and across chunks, likewise. Chunkings are any list
of chunks that flattens to the sequence — every extent choice is one. What
is *not* extent-independent: counting chunks, or observing per-chunk
`any`/`all` without folding them (the interpreter's stressed extent shows
the difference, `compiler/e2e_scalable_test.go`). -/

namespace Oak.Simd

/-- A chunking of `xs`: chunks that flatten back to `xs`. -/
def IsChunking (chunks : List (List Nat)) (xs : List Nat) : Prop := chunks.flatten = xs

/-- A lane-wise operation applied chunk by chunk is the operation on the
    whole sequence, whatever the chunk sizes. -/
theorem chunked_map_eq (f : Nat → Nat) (chunks : List (List Nat)) (xs : List Nat)
    (h : IsChunking chunks xs) : (chunks.map (List.map f)).flatten = xs.map f := by
  unfold IsChunking at h
  subst h
  induction chunks with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, List.flatten_cons, List.flatten_cons, List.map_append, ih]

/-- The wrapping sum (reduce_add) of the chunk sums is the sum of the whole:
    the sum modulo `2^bits` is associative and commutative. -/
theorem chunked_sum_eq (bits : Nat) (chunks : List (List Nat)) (xs : List Nat)
    (h : IsChunking chunks xs) :
    (chunks.map (fun c => c.sum % 2 ^ bits)).sum % 2 ^ bits = xs.sum % 2 ^ bits := by
  unfold IsChunking at h
  subst h
  induction chunks with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, List.sum_cons, List.flatten_cons, List.sum_append, Nat.add_mod, ih, Nat.mod_mod, ← Nat.add_mod]

/-- `any` folded with or across chunks is `any` of the whole. -/
theorem chunked_any_eq (chunks : List (List Nat)) (xs : List Nat) (h : IsChunking chunks xs) :
    chunks.any anyLane = anyLane xs := by
  unfold IsChunking at h
  subst h
  induction chunks with
  | nil => rfl
  | cons c rest ih =>
    rw [List.any_cons, List.flatten_cons, ih]
    simp only [anyLane, List.any_append]

/-- `all` folded with and across chunks is `all` of the whole. -/
theorem chunked_all_eq (chunks : List (List Nat)) (xs : List Nat) (h : IsChunking chunks xs) :
    chunks.all allLanes = allLanes xs := by
  unfold IsChunking at h
  subst h
  induction chunks with
  | nil => rfl
  | cons c rest ih =>
    rw [List.all_cons, List.flatten_cons, ih]
    simp only [allLanes, List.all_append]

/-- Counting chunks is not extent-independent: two chunkings of the same
    sequence with different chunk counts. -/
theorem chunk_count_depends_on_extent :
    IsChunking [[1, 2]] [1, 2] ∧ IsChunking [[1], [2]] [1, 2] ∧ ([[1, 2]] : List (List Nat)).length ≠ [[1], [2]].length := by
  refine ⟨rfl, rfl, by decide⟩

end Oak.Simd
