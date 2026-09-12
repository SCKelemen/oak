import Std.Tactic.BVDecide
import Oak.Utf8Lookup
import Oak.Utf8Validity

/-!
# The UTF-8 stream: the lane function composes, and all-zero means valid

`stdlib/utf8.oak` computes, for every byte of the input, one error byte from
the byte itself and the three before it (`check_block`); the stream is valid
when every error byte is zero and no sequence is left open at the end. This
file is the argument that those lane errors, taken together, decide Unicode
Table 3-7 exactly — the sequence-level model `Oak.Utf8Validity.Valid`.

* `laneError` is the lane function exactly as the Oak source spells it, the
  three table lookups and the saturating subtractions included; `laneError_eq`
  ties it to the pairwise classification of `Oak.Utf8Lookup`.
* `scan` runs the lane function down a byte list carrying the three previous
  bytes; `ctxAfter` is the context a list leaves behind. A context is a
  `Boundary` when it leaves no sequence open — the negation of the block-end
  `incomplete` test.
* `scan_valid` is the theorem: with the zero context of the stream start,
  every lane error is zero and the final context is a boundary **iff** the
  byte list is `Valid`. Both directions go through the same per-sequence
  facts, each decided by bit-blasting over the bytes of one sequence and
  its context.

The block-level file `Oak.Utf8Blocks` shows the vector program computes
exactly these lane errors block by block and that the ASCII shortcut and
the sixty-four-byte step change nothing.
-/

namespace Oak.Utf8Stream

open Oak.Utf8Validity (Seq Valid)

/-- Saturating subtraction: the lane semantics of `simd.subs_u8x16`. -/
def satSub (a b : BitVec 8) : BitVec 8 := if b ≤ a then a - b else 0

/-- `table_high1` as `simd.tbl_u8x16` reads it: sixteen entries by index value, zero for any index past 15 (which the nibble indices never are). -/
def high1Tbl (n : BitVec 8) : BitVec 8 :=
  if n = 0 then 2 else if n = 1 then 2 else if n = 2 then 2 else if n = 3 then 2 else if n = 4 then 2 else if n = 5 then 2 else if n = 6 then 2 else if n = 7 then 2 else if n = 8 then 128 else if n = 9 then 128 else if n = 10 then 128 else if n = 11 then 128 else if n = 12 then 33 else if n = 13 then 1 else if n = 14 then 21 else if n = 15 then 73 else 0

/-- `table_low1`. -/
def low1Tbl (n : BitVec 8) : BitVec 8 :=
  if n = 0 then 231 else if n = 1 then 163 else if n = 2 then 131 else if n = 3 then 131 else if n = 4 then 139 else if n = 5 then 203 else if n = 6 then 203 else if n = 7 then 203 else if n = 8 then 203 else if n = 9 then 203 else if n = 10 then 203 else if n = 11 then 203 else if n = 12 then 203 else if n = 13 then 219 else if n = 14 then 203 else if n = 15 then 203 else 0

/-- `table_high2`. -/
def high2Tbl (n : BitVec 8) : BitVec 8 :=
  if n = 0 then 1 else if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 1 else if n = 4 then 1 else if n = 5 then 1 else if n = 6 then 1 else if n = 7 then 1 else if n = 8 then 230 else if n = 9 then 174 else if n = 10 then 186 else if n = 11 then 186 else if n = 12 then 1 else if n = 13 then 1 else if n = 14 then 1 else if n = 15 then 1 else 0

/-- `special_cases`: the AND of the three lookups, indexed by the previous
byte's nibbles and the current byte's high nibble. -/
def specialCases (p1 c : BitVec 8) : BitVec 8 :=
  high1Tbl (p1 >>> 4) &&& low1Tbl (p1 &&& 15) &&& high2Tbl (c >>> 4)

/-- The TWO_CONTS permission of `check_block`: the high bit of
`subs(prev2, 96) | subs(prev3, 112)`. -/
def must23 (p3 p2 : BitVec 8) : BitVec 8 := (satSub p2 96 ||| satSub p3 112) &&& 128

/-- One lane of `check_block`: the byte `c` against the three before it. -/
def laneError (p3 p2 p1 c : BitVec 8) : BitVec 8 := must23 p3 p2 ^^^ specialCases p1 c

/-- The tables as functions agree with the nibble classification of
`Oak.Utf8Lookup`, so `laneError` is that pair classification, its TWO_CONTS
bit cancelled by the permission. -/
theorem specialCases_eq (p c : BitVec 8) : specialCases p c = Oak.Utf8Lookup.sc p c := by
  unfold specialCases high1Tbl low1Tbl high2Tbl Oak.Utf8Lookup.sc Oak.Utf8Lookup.high1
    Oak.Utf8Lookup.low1 Oak.Utf8Lookup.high2
  bv_decide

theorem must23_eq (p3 p2 : BitVec 8) :
    (must23 p3 p2 ≠ 0) ↔ (0xE0#8 ≤ p2 ∨ 0xF0#8 ≤ p3) := by
  unfold must23 satSub
  bv_decide

/-- The three bytes before a position leave a sequence open: what the
block-end `incomplete` lanes detect (`Oak.Utf8Lookup.incomplete_*`). -/
def incompleteAt (p3 p2 p1 : BitVec 8) : Prop := 0xF0#8 ≤ p3 ∨ 0xE0#8 ≤ p2 ∨ 0xC0#8 ≤ p1

/-- A context that leaves nothing open: a sequence boundary. -/
def Boundary (p3 p2 p1 : BitVec 8) : Prop := p3 < 0xF0#8 ∧ p2 < 0xE0#8 ∧ p1 < 0xC0#8

theorem boundary_iff_not_incomplete (p3 p2 p1 : BitVec 8) :
    Boundary p3 p2 p1 ↔ ¬ incompleteAt p3 p2 p1 := by
  unfold Boundary incompleteAt
  bv_decide

/-- The lane errors of a byte list under a starting context. -/
def scan : BitVec 8 → BitVec 8 → BitVec 8 → List (BitVec 8) → List (BitVec 8)
  | _, _, _, [] => []
  | p3, p2, p1, c :: rest => laneError p3 p2 p1 c :: scan p2 p1 c rest

/-- The context a byte list leaves behind. -/
def ctxAfter : BitVec 8 → BitVec 8 → BitVec 8 → List (BitVec 8) → BitVec 8 × BitVec 8 × BitVec 8
  | p3, p2, p1, [] => (p3, p2, p1)
  | _, p2, p1, c :: rest => ctxAfter p2 p1 c rest

def BoundaryCtx (ctx : BitVec 8 × BitVec 8 × BitVec 8) : Prop := Boundary ctx.1 ctx.2.1 ctx.2.2

/-! ## Per-sequence facts

Each is a statement about at most seven bytes, decided by `bv_decide`. The
`*_ok` facts carry a well-formed sequence across a boundary: its lanes are
zero and it ends at a boundary. The `*_next` facts read a well-formed
sequence off zero lanes: a lead byte at a boundary whose following lanes are
zero is followed by exactly the continuations Table 3-7 requires. -/

theorem ascii_ok (p3 p2 p1 c : BitVec 8) (hb : Boundary p3 p2 p1) (hc : c < 0x80#8) :
    laneError p3 p2 p1 c = 0 ∧ Boundary p2 p1 c := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

theorem two_ok (p3 p2 p1 b0 b1 : BitVec 8) (hb : Boundary p3 p2 p1)
    (h0 : 0xC2#8 ≤ b0 ∧ b0 ≤ 0xDF#8) (h1 : 0x80#8 ≤ b1 ∧ b1 ≤ 0xBF#8) :
    laneError p3 p2 p1 b0 = 0 ∧ laneError p2 p1 b0 b1 = 0 ∧ Boundary p1 b0 b1 := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

theorem three_ok (p3 p2 p1 b0 b1 b2 : BitVec 8) (hb : Boundary p3 p2 p1)
    (h0 : 0xE0#8 ≤ b0 ∧ b0 ≤ 0xEF#8) (h1 : 0x80#8 ≤ b1 ∧ b1 ≤ 0xBF#8)
    (hE0 : b0 = 0xE0#8 → 0xA0#8 ≤ b1) (hED : b0 = 0xED#8 → b1 ≤ 0x9F#8)
    (h2 : 0x80#8 ≤ b2 ∧ b2 ≤ 0xBF#8) :
    laneError p3 p2 p1 b0 = 0 ∧ laneError p2 p1 b0 b1 = 0 ∧ laneError p1 b0 b1 b2 = 0 ∧
      Boundary b0 b1 b2 := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

theorem four_ok (p3 p2 p1 b0 b1 b2 b3 : BitVec 8) (hb : Boundary p3 p2 p1)
    (h0 : 0xF0#8 ≤ b0 ∧ b0 ≤ 0xF4#8) (h1 : 0x80#8 ≤ b1 ∧ b1 ≤ 0xBF#8)
    (hF0 : b0 = 0xF0#8 → 0x90#8 ≤ b1) (hF4 : b0 = 0xF4#8 → b1 ≤ 0x8F#8)
    (h2 : 0x80#8 ≤ b2 ∧ b2 ≤ 0xBF#8) (h3 : 0x80#8 ≤ b3 ∧ b3 ≤ 0xBF#8) :
    laneError p3 p2 p1 b0 = 0 ∧ laneError p2 p1 b0 b1 = 0 ∧ laneError p1 b0 b1 b2 = 0 ∧
      laneError b0 b1 b2 b3 = 0 ∧ Boundary b1 b2 b3 := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

/-- A continuation at a boundary is a stray continuation: its lane is nonzero. -/
theorem cont_stray (p3 p2 p1 c : BitVec 8) (hb : Boundary p3 p2 p1)
    (hc : 0x80#8 ≤ c ∧ c ≤ 0xBF#8) : laneError p3 p2 p1 c ≠ 0 := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

theorem two_next (p3 p2 p1 b0 b1 : BitVec 8) (hb : Boundary p3 p2 p1)
    (h0 : 0xC0#8 ≤ b0 ∧ b0 ≤ 0xDF#8) (h : laneError p2 p1 b0 b1 = 0) :
    (0xC2#8 ≤ b0 ∧ b0 ≤ 0xDF#8) ∧ (0x80#8 ≤ b1 ∧ b1 ≤ 0xBF#8) ∧ Boundary p1 b0 b1 := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl at *
  bv_decide

theorem three_next (p3 p2 p1 b0 b1 b2 : BitVec 8) (hb : Boundary p3 p2 p1)
    (h0 : 0xE0#8 ≤ b0 ∧ b0 ≤ 0xEF#8) (h1 : laneError p2 p1 b0 b1 = 0)
    (h2 : laneError p1 b0 b1 b2 = 0) :
    (0x80#8 ≤ b1 ∧ b1 ≤ 0xBF#8) ∧ (b0 = 0xE0#8 → 0xA0#8 ≤ b1) ∧ (b0 = 0xED#8 → b1 ≤ 0x9F#8) ∧
      (0x80#8 ≤ b2 ∧ b2 ≤ 0xBF#8) ∧ Boundary b0 b1 b2 := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl at *
  bv_decide

theorem four_next (p3 p2 p1 b0 b1 b2 b3 : BitVec 8) (hb : Boundary p3 p2 p1)
    (h0 : 0xF0#8 ≤ b0) (h1 : laneError p2 p1 b0 b1 = 0)
    (h2 : laneError p1 b0 b1 b2 = 0) (h3 : laneError b0 b1 b2 b3 = 0) :
    (0xF0#8 ≤ b0 ∧ b0 ≤ 0xF4#8) ∧ (0x80#8 ≤ b1 ∧ b1 ≤ 0xBF#8) ∧
      (b0 = 0xF0#8 → 0x90#8 ≤ b1) ∧ (b0 = 0xF4#8 → b1 ≤ 0x8F#8) ∧
      (0x80#8 ≤ b2 ∧ b2 ≤ 0xBF#8) ∧ (0x80#8 ≤ b3 ∧ b3 ≤ 0xBF#8) ∧ Boundary b1 b2 b3 := by
  unfold Boundary at *; unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl at *
  bv_decide

/-- A sequence cut short leaves no boundary: a lead byte as the last byte,
a three- or four-byte lead as the second-to-last, a four-byte lead as the
third-to-last. -/
theorem cut_after_lead (p2 p1 c : BitVec 8) (hc : 0xC0#8 ≤ c) : ¬ Boundary p2 p1 c := by
  unfold Boundary; bv_decide
theorem cut_after_two (p1 c c1 : BitVec 8) (hc : 0xE0#8 ≤ c) : ¬ Boundary p1 c c1 := by
  unfold Boundary; bv_decide
theorem cut_after_three (c c1 c2 : BitVec 8) (hc : 0xF0#8 ≤ c) : ¬ Boundary c c1 c2 := by
  unfold Boundary; bv_decide

/-! ## Between bytes as bit vectors and bytes as naturals -/

theorem toNat_ge {k : Nat} {a : BitVec 8} (h : BitVec.ofNat 8 k ≤ a) (hk : k < 256) :
    k ≤ a.toNat := by
  rw [BitVec.le_def, BitVec.toNat_ofNat] at h
  simpa [Nat.mod_eq_of_lt hk] using h

theorem toNat_le {k : Nat} {a : BitVec 8} (h : a ≤ BitVec.ofNat 8 k) (hk : k < 256) :
    a.toNat ≤ k := by
  rw [BitVec.le_def, BitVec.toNat_ofNat] at h
  simpa [Nat.mod_eq_of_lt hk] using h

theorem ofNat_le_ofNat {k b : Nat} (h : k ≤ b) (hb : b < 256) :
    BitVec.ofNat 8 k ≤ BitVec.ofNat 8 b := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simpa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h hb)] using h

theorem ofNat_eq_of_eq {k b : Nat} (h : b = k) : BitVec.ofNat 8 b = BitVec.ofNat 8 k := by
  rw [h]

theorem eq_of_ofNat_eq {k b : Nat} (h : BitVec.ofNat 8 b = BitVec.ofNat 8 k) (hb : b < 256)
    (hk : k < 256) : b = k := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hk] at this

theorem ofNat_lt_ofNat {k b : Nat} (h : b < k) (hk : k < 256) :
    BitVec.ofNat 8 b < BitVec.ofNat 8 k := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simpa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (Nat.lt_trans h hk)] using h

/-! ## Valid streams scan to zero -/

/-- A valid byte list, entered at a boundary, has zero lane errors and ends
at a boundary. Induction over the sequences of `Valid`; each sequence is one
of the `*_ok` facts. -/
theorem scan_of_valid (ns : List Nat) (hv : Valid ns) :
    (∀ n ∈ ns, n < 256) → ∀ p3 p2 p1 : BitVec 8, Boundary p3 p2 p1 →
      (∀ e ∈ scan p3 p2 p1 (ns.map (BitVec.ofNat 8)), e = 0) ∧
        BoundaryCtx (ctxAfter p3 p2 p1 (ns.map (BitVec.ofNat 8))) := by
  induction hv with
  | nil =>
    intro _ p3 p2 p1 hb
    exact ⟨fun e he => absurd he (List.not_mem_nil), hb⟩
  | @app seq rest s hseq _ ih =>
    intro h256 p3 p2 p1 hb
    have hrest : ∀ n ∈ rest, n < 256 := fun n hn => h256 n (List.mem_append_right _ hn)
    cases hseq with
    | ascii hb0 =>
      have h0 : s < 256 := h256 s (by simp)
      have hc : BitVec.ofNat 8 s < 0x80#8 := ofNat_lt_ofNat (by omega) (by decide)
      obtain ⟨hz, hnext⟩ := ascii_ok p3 p2 p1 _ hb hc
      obtain ⟨ihz, ihb⟩ := ih hrest p2 p1 _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz, ihz⟩, ihb⟩
    | @two b0 b1 hb0 hb0' hb1 hb1' =>
      have h0 : b0 < 256 := h256 b0 (by simp)
      have h1 : b1 < 256 := h256 b1 (by simp)
      obtain ⟨hz0, hz1, hnext⟩ := two_ok p3 p2 p1 _ _ hb
        ⟨ofNat_le_ofNat hb0 h0, ofNat_le_ofNat hb0' (by decide)⟩
        ⟨ofNat_le_ofNat hb1 h1, ofNat_le_ofNat hb1' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest p1 _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, ihz⟩, ihb⟩
    | @threeE0 b1 b2 hb1 hb1' hb2 hb2' =>
      have h1 : b1 < 256 := h256 b1 (by simp)
      have h2 : b2 < 256 := h256 b2 (by simp)
      obtain ⟨hz0, hz1, hz2, hnext⟩ := three_ok p3 p2 p1 (BitVec.ofNat 8 0xE0) _ _ hb
        ⟨by decide, by decide⟩
        ⟨ofNat_le_ofNat (by omega) h1, ofNat_le_ofNat hb1' (by decide)⟩
        (fun _ => ofNat_le_ofNat hb1 h1) (fun h => absurd h (by decide))
        ⟨ofNat_le_ofNat hb2 h2, ofNat_le_ofNat hb2' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest _ _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, hz2, ihz⟩, ihb⟩
    | @threeMid b0 b1 b2 hb0 hb0' hb1 hb1' hb2 hb2' =>
      have h0 : b0 < 256 := h256 b0 (by simp)
      have h1 : b1 < 256 := h256 b1 (by simp)
      have h2 : b2 < 256 := h256 b2 (by simp)
      obtain ⟨hz0, hz1, hz2, hnext⟩ := three_ok p3 p2 p1 _ _ _ hb
        ⟨ofNat_le_ofNat (by omega) h0, ofNat_le_ofNat (by omega) (by decide)⟩
        ⟨ofNat_le_ofNat hb1 h1, ofNat_le_ofNat hb1' (by decide)⟩
        (fun h => absurd (eq_of_ofNat_eq h h0 (by decide)) (by omega))
        (fun h => absurd (eq_of_ofNat_eq h h0 (by decide)) (by omega))
        ⟨ofNat_le_ofNat hb2 h2, ofNat_le_ofNat hb2' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest _ _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, hz2, ihz⟩, ihb⟩
    | @threeED b1 b2 hb1 hb1' hb2 hb2' =>
      have h1 : b1 < 256 := h256 b1 (by simp)
      have h2 : b2 < 256 := h256 b2 (by simp)
      obtain ⟨hz0, hz1, hz2, hnext⟩ := three_ok p3 p2 p1 (BitVec.ofNat 8 0xED) _ _ hb
        ⟨by decide, by decide⟩
        ⟨ofNat_le_ofNat hb1 h1, ofNat_le_ofNat (by omega) (by decide)⟩
        (fun h => absurd h (by decide)) (fun _ => ofNat_le_ofNat hb1' (by decide))
        ⟨ofNat_le_ofNat hb2 h2, ofNat_le_ofNat hb2' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest _ _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, hz2, ihz⟩, ihb⟩
    | @threeHigh b0 b1 b2 hb0 hb0' hb1 hb1' hb2 hb2' =>
      have h0 : b0 < 256 := h256 b0 (by simp)
      have h1 : b1 < 256 := h256 b1 (by simp)
      have h2 : b2 < 256 := h256 b2 (by simp)
      obtain ⟨hz0, hz1, hz2, hnext⟩ := three_ok p3 p2 p1 _ _ _ hb
        ⟨ofNat_le_ofNat (by omega) h0, ofNat_le_ofNat hb0' (by decide)⟩
        ⟨ofNat_le_ofNat hb1 h1, ofNat_le_ofNat hb1' (by decide)⟩
        (fun h => absurd (eq_of_ofNat_eq h h0 (by decide)) (by omega))
        (fun h => absurd (eq_of_ofNat_eq h h0 (by decide)) (by omega))
        ⟨ofNat_le_ofNat hb2 h2, ofNat_le_ofNat hb2' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest _ _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, hz2, ihz⟩, ihb⟩
    | @fourF0 b1 b2 b3 hb1 hb1' hb2 hb2' hb3 hb3' =>
      have h1 : b1 < 256 := h256 b1 (by simp)
      have h2 : b2 < 256 := h256 b2 (by simp)
      have h3 : b3 < 256 := h256 b3 (by simp)
      obtain ⟨hz0, hz1, hz2, hz3, hnext⟩ := four_ok p3 p2 p1 (BitVec.ofNat 8 0xF0) _ _ _ hb
        ⟨by decide, by decide⟩
        ⟨ofNat_le_ofNat (by omega) h1, ofNat_le_ofNat hb1' (by decide)⟩
        (fun _ => ofNat_le_ofNat hb1 h1) (fun h => absurd h (by decide))
        ⟨ofNat_le_ofNat hb2 h2, ofNat_le_ofNat hb2' (by decide)⟩
        ⟨ofNat_le_ofNat hb3 h3, ofNat_le_ofNat hb3' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest _ _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, hz2, hz3, ihz⟩, ihb⟩
    | @fourMid b0 b1 b2 b3 hb0 hb0' hb1 hb1' hb2 hb2' hb3 hb3' =>
      have h0 : b0 < 256 := h256 b0 (by simp)
      have h1 : b1 < 256 := h256 b1 (by simp)
      have h2 : b2 < 256 := h256 b2 (by simp)
      have h3 : b3 < 256 := h256 b3 (by simp)
      obtain ⟨hz0, hz1, hz2, hz3, hnext⟩ := four_ok p3 p2 p1 _ _ _ _ hb
        ⟨ofNat_le_ofNat (by omega) h0, ofNat_le_ofNat (by omega) (by decide)⟩
        ⟨ofNat_le_ofNat hb1 h1, ofNat_le_ofNat hb1' (by decide)⟩
        (fun h => absurd (eq_of_ofNat_eq h h0 (by decide)) (by omega))
        (fun h => absurd (eq_of_ofNat_eq h h0 (by decide)) (by omega))
        ⟨ofNat_le_ofNat hb2 h2, ofNat_le_ofNat hb2' (by decide)⟩
        ⟨ofNat_le_ofNat hb3 h3, ofNat_le_ofNat hb3' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest _ _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, hz2, hz3, ihz⟩, ihb⟩
    | @fourF4 b1 b2 b3 hb1 hb1' hb2 hb2' hb3 hb3' =>
      have h1 : b1 < 256 := h256 b1 (by simp)
      have h2 : b2 < 256 := h256 b2 (by simp)
      have h3 : b3 < 256 := h256 b3 (by simp)
      obtain ⟨hz0, hz1, hz2, hz3, hnext⟩ := four_ok p3 p2 p1 (BitVec.ofNat 8 0xF4) _ _ _ hb
        ⟨by decide, by decide⟩
        ⟨ofNat_le_ofNat hb1 h1, ofNat_le_ofNat (by omega) (by decide)⟩
        (fun h => absurd h (by decide)) (fun _ => ofNat_le_ofNat hb1' (by decide))
        ⟨ofNat_le_ofNat hb2 h2, ofNat_le_ofNat hb2' (by decide)⟩
        ⟨ofNat_le_ofNat hb3 h3, ofNat_le_ofNat hb3' (by decide)⟩
      obtain ⟨ihz, ihb⟩ := ih hrest _ _ _ hnext
      simp only [List.cons_append, List.nil_append, List.map_cons, scan, ctxAfter,
        List.forall_mem_cons]
      exact ⟨⟨hz0, hz1, hz2, hz3, ihz⟩, ihb⟩

/-! ## Zero scans are valid streams -/

/-- A byte list entered at a boundary whose lane errors are all zero and
which ends at a boundary is valid. Recursion over the list: the first byte
is ASCII, or a lead byte whose zero lanes force exactly the continuations
Table 3-7 requires (`*_next`); a continuation is a stray (`cont_stray`),
and a lead byte the list cuts short breaks the final boundary
(`cut_after_*`). -/
theorem valid_of_scan : ∀ (bs : List (BitVec 8)) (p3 p2 p1 : BitVec 8), Boundary p3 p2 p1 →
    (∀ e ∈ scan p3 p2 p1 bs, e = 0) → BoundaryCtx (ctxAfter p3 p2 p1 bs) →
      Valid (bs.map BitVec.toNat)
  | [], _, _, _, _, _, _ => Valid.nil
  | c :: rest, p3, p2, p1, hb, hz, hend => by
    have hz0 : laneError p3 p2 p1 c = 0 := hz _ (List.mem_cons_self ..)
    have hz' : ∀ e ∈ scan p2 p1 c rest, e = 0 := fun e he => hz e (List.mem_cons_of_mem _ he)
    have hend' : BoundaryCtx (ctxAfter p2 p1 c rest) := hend
    by_cases hA : c < 0x80#8
    · -- ASCII
      have ih := valid_of_scan rest p2 p1 c (ascii_ok p3 p2 p1 c hb hA).2 hz' hend'
      show Valid ([c.toNat] ++ rest.map BitVec.toNat)
      exact Valid.app (Seq.ascii (toNat_le (by bv_decide) (by decide))) ih
    by_cases hC : c ≤ 0xBF#8
    · exact absurd hz0 (cont_stray p3 p2 p1 c hb ⟨by bv_decide, hC⟩)
    by_cases hD : c ≤ 0xDF#8
    · -- two-byte lead
      match rest, hz', hend' with
      | [], _, hend' => exact absurd hend' (cut_after_lead p2 p1 c (by bv_decide))
      | c1 :: rest', hz', hend' =>
        have hz1 : laneError p2 p1 c c1 = 0 := hz' _ (List.mem_cons_self ..)
        obtain ⟨h0, h1, hnext⟩ := two_next p3 p2 p1 c c1 hb ⟨by bv_decide, hD⟩ hz1
        have ih := valid_of_scan rest' p1 c c1 hnext
          (fun e he => hz' e (List.mem_cons_of_mem _ he)) hend'
        show Valid ([c.toNat, c1.toNat] ++ rest'.map BitVec.toNat)
        exact Valid.app (Seq.two (toNat_ge h0.1 (by decide)) (toNat_le h0.2 (by decide))
          (toNat_ge h1.1 (by decide)) (toNat_le h1.2 (by decide))) ih
    by_cases hE : c ≤ 0xEF#8
    · -- three-byte lead
      match rest, hz', hend' with
      | [], _, hend' => exact absurd hend' (cut_after_lead p2 p1 c (by bv_decide))
      | [c1], _, hend' => exact absurd hend' (cut_after_two p1 c c1 (by bv_decide))
      | c1 :: c2 :: rest', hz', hend' =>
        have hz1 : laneError p2 p1 c c1 = 0 := hz' _ (List.mem_cons_self ..)
        have hz2 : laneError p1 c c1 c2 = 0 :=
          hz' _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        obtain ⟨h1, hE0, hED, h2, hnext⟩ := three_next p3 p2 p1 c c1 c2 hb ⟨by bv_decide, hE⟩ hz1 hz2
        have ih := valid_of_scan rest' c c1 c2 hnext
          (fun e he => hz' e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))) hend'
        show Valid ([c.toNat, c1.toNat, c2.toNat] ++ rest'.map BitVec.toNat)
        have c1lo := toNat_ge h1.1 (by decide)
        have c1hi := toNat_le h1.2 (by decide)
        have c2lo := toNat_ge h2.1 (by decide)
        have c2hi := toNat_le h2.2 (by decide)
        by_cases hE0' : c = 0xE0#8
        · subst hE0'
          exact Valid.app (Seq.threeE0 (toNat_ge (hE0 rfl) (by decide)) c1hi c2lo c2hi) ih
        by_cases hED' : c = 0xED#8
        · subst hED'
          exact Valid.app (Seq.threeED c1lo (toNat_le (hED rfl) (by decide)) c2lo c2hi) ih
        by_cases hMid : c ≤ 0xEC#8
        · exact Valid.app (Seq.threeMid (toNat_ge (by bv_decide) (by decide))
            (toNat_le hMid (by decide)) c1lo c1hi c2lo c2hi) ih
        · exact Valid.app (Seq.threeHigh (toNat_ge (by bv_decide) (by decide))
            (toNat_le hE (by decide)) c1lo c1hi c2lo c2hi) ih
    · -- four-byte lead (or an invalid lead F5..FF, which the lanes reject)
      match rest, hz', hend' with
      | [], _, hend' => exact absurd hend' (cut_after_lead p2 p1 c (by bv_decide))
      | [c1], _, hend' => exact absurd hend' (cut_after_two p1 c c1 (by bv_decide))
      | [c1, c2], _, hend' => exact absurd hend' (cut_after_three c c1 c2 (by bv_decide))
      | c1 :: c2 :: c3 :: rest', hz', hend' =>
        have hz1 : laneError p2 p1 c c1 = 0 := hz' _ (List.mem_cons_self ..)
        have hz2 : laneError p1 c c1 c2 = 0 :=
          hz' _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hz3 : laneError c c1 c2 c3 = 0 :=
          hz' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        obtain ⟨h0, h1, hF0, hF4, h2, h3, hnext⟩ :=
          four_next p3 p2 p1 c c1 c2 c3 hb (by bv_decide) hz1 hz2 hz3
        have ih := valid_of_scan rest' c1 c2 c3 hnext
          (fun e he => hz' e (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))) hend'
        show Valid ([c.toNat, c1.toNat, c2.toNat, c3.toNat] ++ rest'.map BitVec.toNat)
        have c1lo := toNat_ge h1.1 (by decide)
        have c1hi := toNat_le h1.2 (by decide)
        have c2lo := toNat_ge h2.1 (by decide)
        have c2hi := toNat_le h2.2 (by decide)
        have c3lo := toNat_ge h3.1 (by decide)
        have c3hi := toNat_le h3.2 (by decide)
        by_cases hF0' : c = 0xF0#8
        · subst hF0'
          exact Valid.app (Seq.fourF0 (toNat_ge (hF0 rfl) (by decide)) c1hi c2lo c2hi c3lo c3hi) ih
        by_cases hF4' : c = 0xF4#8
        · subst hF4'
          exact Valid.app (Seq.fourF4 c1lo (toNat_le (hF4 rfl) (by decide)) c2lo c2hi c3lo c3hi) ih
        · exact Valid.app (Seq.fourMid (toNat_ge (by bv_decide) (by decide))
            (toNat_le (by bv_decide) (by decide)) c1lo c1hi c2lo c2hi c3lo c3hi) ih
termination_by bs => bs.length

/-- Bytes round-trip through their natural values. -/
theorem map_ofNat_toNat (bs : List (BitVec 8)) :
    (bs.map BitVec.toNat).map (BitVec.ofNat 8) = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.map_cons, ih]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt]

/-- **The stream theorem.** From the zero context of the stream start, every
lane error is zero and the final context is a boundary exactly when the
bytes are valid UTF-8 (`Oak.Utf8Validity.Valid`, Unicode Table 3-7). -/
theorem scan_valid (bs : List (BitVec 8)) :
    ((∀ e ∈ scan 0 0 0 bs, e = 0) ∧ BoundaryCtx (ctxAfter 0 0 0 bs)) ↔
      Valid (bs.map BitVec.toNat) := by
  constructor
  · intro ⟨hz, hend⟩
    exact valid_of_scan bs 0 0 0 (by unfold Boundary; decide) hz hend
  · intro hv
    have h256 : ∀ n ∈ bs.map BitVec.toNat, n < 256 := by
      intro n hn
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hn
      exact b.isLt
    have := scan_of_valid _ hv h256 0 0 0 (by unfold Boundary; decide)
    rwa [map_ofNat_toNat] at this

end Oak.Utf8Stream
