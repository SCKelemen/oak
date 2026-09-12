import Oak.Utf8Stream

/-!
# The stream by position

`Oak.Utf8Stream.scan` walks a byte list carrying a context. The vector
program instead addresses the stream by position: block `b`, lane `i` is
byte `16 * b + i`, the byte `n` back is at `16 * b + i - n`, and every
position past the end reads zero — the zero-padded tail. This file states
the lane error by position (`flatError`) and proves it is the same
computation as the scan: the scan's elements are the errors at positions
below the length, the context the scan leaves behind is the context at the
length (`ctxAt`), and past the length the zero bytes' lane errors are
exactly the block-end `incomplete` test and nothing more (`flat_beyond`,
`flatError_at_end`). `flat_valid` is the stream theorem restated over
positions, the form `Oak.Utf8Blocks` consumes.
-/

namespace Oak.Utf8Flat

open Oak.Utf8Stream

/-- The byte at a position; zero past the end. -/
def byteAt (bs : List (BitVec 8)) (k : Nat) : BitVec 8 := bs.getD k 0

/-- The byte `n` back from position `k`; zero before the start. -/
def back (bs : List (BitVec 8)) (k n : Nat) : BitVec 8 :=
  if n ≤ k then byteAt bs (k - n) else 0

/-- The lane error at a position. -/
def flatError (bs : List (BitVec 8)) (k : Nat) : BitVec 8 :=
  laneError (back bs k 3) (back bs k 2) (back bs k 1) (byteAt bs k)

/-- The context at a position: the three bytes before it. -/
def ctxAt (bs : List (BitVec 8)) (k : Nat) : BitVec 8 × BitVec 8 × BitVec 8 :=
  (back bs k 3, back bs k 2, back bs k 1)

theorem byteAt_past {bs : List (BitVec 8)} {k : Nat} (hk : bs.length ≤ k) : byteAt bs k = 0 := by
  unfold byteAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hk]
  rfl

theorem back_succ_succ (bs : List (BitVec 8)) (k n : Nat) : back bs (k + 1) (n + 1) = back bs k n := by
  unfold back
  by_cases h : n ≤ k
  · rw [if_pos (by omega), if_pos h]
    congr 1
    omega
  · rw [if_neg (by omega), if_neg h]

theorem back_succ_one (bs : List (BitVec 8)) (k : Nat) : back bs (k + 1) 1 = byteAt bs k := by
  unfold back
  rw [if_pos (by omega)]
  congr 1

theorem back_zero (bs : List (BitVec 8)) (n : Nat) (hn : 1 ≤ n) : back bs 0 n = 0 := by
  unfold back
  rw [if_neg (by omega)]

/-- A byte `n` back from a position at least `n` past the end is zero. -/
theorem back_past {bs : List (BitVec 8)} {k n : Nat} (hk : bs.length + n ≤ k) : back bs k n = 0 := by
  unfold back
  rw [if_pos (by omega)]
  exact byteAt_past (by omega)

/-! ## The scan by position -/

/-- The scan of a suffix starting at position `k`, entered with the context
at `k`, lists the lane errors at positions `k`, `k + 1`, ... -/
theorem scan_eq (bs : List (BitVec 8)) :
    ∀ (rest : List (BitVec 8)) (k : Nat), (∀ j, byteAt bs (k + j) = rest.getD j 0) →
      scan (back bs k 3) (back bs k 2) (back bs k 1) rest =
        (List.range rest.length).map (fun j => flatError bs (k + j)) := by
  intro rest
  induction rest with
  | nil => intro k _; rfl
  | cons c rest ih =>
    intro k h
    have hc : byteAt bs k = c := by simpa using h 0
    have h' : ∀ j, byteAt bs (k + 1 + j) = rest.getD j 0 := by
      intro j
      have := h (j + 1)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    have tail := ih (k + 1) h'
    rw [back_succ_succ, back_succ_succ, back_succ_one, hc] at tail
    simp only [scan, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [tail]
    have hhead : laneError (back bs k 3) (back bs k 2) (back bs k 1) c = flatError bs (k + 0) := by
      unfold flatError; rw [Nat.add_zero, hc]
    rw [hhead]
    congr 1
    apply List.map_congr_left
    intro j _
    show flatError bs (k + 1 + j) = flatError bs (k + (j + 1))
    rw [show k + (j + 1) = k + 1 + j by omega]

/-- The context a suffix leaves behind is the context at its end. -/
theorem ctxAfter_eq (bs : List (BitVec 8)) :
    ∀ (rest : List (BitVec 8)) (k : Nat), (∀ j, byteAt bs (k + j) = rest.getD j 0) →
      ctxAfter (back bs k 3) (back bs k 2) (back bs k 1) rest = ctxAt bs (k + rest.length) := by
  intro rest
  induction rest with
  | nil => intro k _; rfl
  | cons c rest ih =>
    intro k h
    have hc : byteAt bs k = c := by simpa using h 0
    have h' : ∀ j, byteAt bs (k + 1 + j) = rest.getD j 0 := by
      intro j
      have := h (j + 1)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    have tail := ih (k + 1) h'
    rw [back_succ_succ, back_succ_succ, back_succ_one, hc] at tail
    simp only [ctxAfter, List.length_cons]
    rw [tail, show k + 1 + rest.length = k + (rest.length + 1) by omega]

theorem scan_zero_eq (bs : List (BitVec 8)) :
    scan 0 0 0 bs = (List.range bs.length).map (flatError bs) := by
  have := scan_eq bs bs 0 (fun j => by simp [byteAt])
  rw [back_zero bs 3 (by omega), back_zero bs 2 (by omega), back_zero bs 1 (by omega)] at this
  simpa using this

theorem ctxAfter_zero_eq (bs : List (BitVec 8)) : ctxAfter 0 0 0 bs = ctxAt bs bs.length := by
  have := ctxAfter_eq bs bs 0 (fun j => by simp [byteAt])
  rw [back_zero bs 3 (by omega), back_zero bs 2 (by omega), back_zero bs 1 (by omega)] at this
  simpa using this

theorem scan_all_zero_iff (bs : List (BitVec 8)) :
    (∀ e ∈ scan 0 0 0 bs, e = 0) ↔ ∀ k < bs.length, flatError bs k = 0 := by
  rw [scan_zero_eq]
  constructor
  · intro h k hk
    exact h _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  · intro h e he
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
    exact h k (List.mem_range.mp hk)

/-! ## Past the end -/

/-- A zero byte's lane error is exactly the block-end `incomplete` test on
the three bytes before it: nonzero iff they leave a sequence open. -/
theorem laneError_zero_byte (p3 p2 p1 : BitVec 8) :
    laneError p3 p2 p1 0 = 0 ↔ Boundary p3 p2 p1 := by
  unfold Boundary laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

theorem laneError_after_boundary_one (p3 p2 p1 : BitVec 8) (hb : Boundary p3 p2 p1) :
    laneError p2 p1 0 0 = 0 := by
  unfold Boundary at hb; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

theorem laneError_after_boundary_two (p3 p2 p1 : BitVec 8) (hb : Boundary p3 p2 p1) :
    laneError p1 0 0 0 = 0 := by
  unfold Boundary at hb; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

theorem laneError_zeros : laneError 0 0 0 0 = 0 := by
  unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  decide

/-- The lane error at a position at or past the end is zero iff the context
there is a boundary. -/
theorem flatError_at_end (bs : List (BitVec 8)) (m : Nat) (hm : bs.length ≤ m) :
    flatError bs m = 0 ↔ BoundaryCtx (ctxAt bs m) := by
  unfold flatError
  rw [byteAt_past hm]
  exact laneError_zero_byte _ _ _

/-- Past a position at or beyond the end whose context is a boundary, every
lane error is zero: the padding raises nothing. -/
theorem flat_beyond (bs : List (BitVec 8)) (m : Nat) (hm : bs.length ≤ m)
    (hb : BoundaryCtx (ctxAt bs m)) : ∀ k, m ≤ k → flatError bs k = 0 := by
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
  unfold BoundaryCtx ctxAt at hb
  unfold flatError
  rw [byteAt_past (by omega)]
  match d with
  | 0 => exact (laneError_zero_byte _ _ _).mpr hb
  | 1 =>
    rw [back_succ_succ, back_succ_succ, back_succ_one, byteAt_past hm]
    exact laneError_after_boundary_one _ _ _ hb
  | 2 =>
    rw [show m + 2 = m + 1 + 1 by rfl, back_succ_succ, back_succ_succ, back_succ_one,
      back_succ_succ, back_succ_one, byteAt_past hm, byteAt_past (by omega)]
    exact laneError_after_boundary_two _ _ _ hb
  | d + 3 =>
    rw [back_past (by omega), back_past (by omega), back_past (by omega)]
    exact laneError_zeros

/-! ## The stream theorem by position -/

/-- Every lane error of the stream is zero — at every position, the zero
padding included — iff the bytes are valid UTF-8. -/
theorem flat_valid (bs : List (BitVec 8)) :
    (∀ k, flatError bs k = 0) ↔ Oak.Utf8Validity.Valid (bs.map BitVec.toNat) := by
  rw [← scan_valid, scan_all_zero_iff, ctxAfter_zero_eq]
  constructor
  · intro h
    exact ⟨fun k _ => h k, (flatError_at_end bs _ (Nat.le_refl _)).mp (h _)⟩
  · intro ⟨hlt, hend⟩ k
    by_cases hk : k < bs.length
    · exact hlt k hk
    · exact flat_beyond bs _ (Nat.le_refl _) hend k (by omega)

end Oak.Utf8Flat
