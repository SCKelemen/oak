import Oak.Assembler

/-! # Compiler correspondence for the seam checker's region rules

`asm/check.go` admits memory through a *derived* base — an element of a
frame array, of a span of records, or of a constant table — by three
rules. `elementRegion` records what `xE = xB + wI·size` addresses under
the index guard on `wI`: a region of `size` bytes, or of `K·size` under a
slack guard. `regionAccess` admits `[xR, #off]` and `[xR, wJ, uxtw #t]`
inside such a region; `frameArrayAccess` admits `[xN, #off]` and
`[xN, wI, uxtw #s]` through a frame address. This module transliterates
the three decisions — the Go is maintained line for line with them
(`asm.elementRegionOf`, `asm.regionAdmits`, `asm.frameArrayAdmits`), and
`asm/checker_refinement_test.go` renders the Go decisions as the examples
stated at the end of this file — and proves them sound: every byte of an
access they admit lies inside the object the base addresses, the declared
frame interval, the span's `elem·len` bytes for every runtime length the
guard admits, or the parent region, as `Oak.Assembler` states for the
non-derived accesses (`inFrame_bytes`, `index_access_bytes`).

Integers model Go's `int64`. A register-held index is a runtime value
`i ≥ 0`. The guard fact on it (`idxFact`) means `i < bound` for an
immediate bound (`boundReg < 0`), `i < len` for a bound held in a register
that holds the span's length, and `i + bound ≤ len` for a slack guard
(`GuardMeans`). -/

namespace Oak.CheckerRefinement

open Oak.Assembler

/-- `asm.region`: a register addresses `size` bytes, writable or not. -/
structure Region where
  size : Int
  writable : Bool
  deriving Repr, DecidableEq

/-- `asm.idxFact`: the dominating guard on an index register — `boundReg`
    names the register compared against, `-1` for an immediate `bound`;
    `slack` marks the vector form `wI + bound ≤ len`. -/
structure IdxFact where
  boundReg : Int
  bound : Int
  slack : Bool
  /-- The minimum length under which a slack fact is exact: the `K` of the
      `sub wT, wL, #K` behind it, carried unchanged when an offset lowers
      `bound` (`Oak.Assembler.slack_guard` needs `K ≤ len`). -/
  need : Int
  deriving Repr, DecidableEq

/-- `asm.spanFact`: a span base's element size, writability, proven
    minimum length, and the registers holding its length. -/
structure SpanFact where
  elem : Int
  writable : Bool
  hasMin : Bool
  minLen : Int
  lenRegs : List Int
  deriving Repr, DecidableEq

def SpanFact.holdsLen (f : SpanFact) (n : Int) : Bool := f.lenRegs.contains n

/-- What the checker's fact maps say about the base register, consulted
    in `elementRegion`'s order: a frame address (`frameAddrs`), a span
    (`spans`), a bounded region (`regions`). -/
structure Base where
  frameAddr : Option Int
  span : Option SpanFact
  region : Option Region
  deriving Repr

/-! ## The transliterated decisions -/

/-- The frame branch of `elementRegion`: the `bound` elements of `size`
    bytes at `addr` must lie inside the declared frame, under an immediate
    guard. -/
def frameElement (frame addr : Int) (bound : IdxFact) (size : Int) : Option Region :=
  if bound.boundReg ≥ 0 ∨ bound.bound ≤ 0 ∨ addr < -frame ∨ addr + bound.bound * size > 0 then none
  else some ⟨size, true⟩

/-- The span branch: a slack guard against a register holding the length,
    under the proven minimum, yields `bound` elements; a register bound
    holding the length, or an immediate bound under the proven minimum,
    yields one element. -/
def spanElement (fact : SpanFact) (bound : IdxFact) (size : Int) : Option Region :=
  if bound.slack = true ∧ bound.boundReg ≥ 0 ∧ fact.holdsLen bound.boundReg = true ∧ fact.hasMin = true ∧ bound.need ≤ fact.minLen then
    some ⟨size * bound.bound, fact.writable⟩
  else if (bound.slack = false ∧ bound.boundReg ≥ 0 ∧ fact.holdsLen bound.boundReg = true) ∨ (bound.boundReg < 0 ∧ fact.hasMin = true ∧ bound.bound ≤ fact.minLen) then
    some ⟨size, fact.writable⟩
  else none

/-- The region branch (a constant table's address): the `bound` elements
    of `size` bytes must lie inside the region, under an immediate guard. -/
def regionElement (extent : Region) (bound : IdxFact) (size : Int) : Option Region :=
  if bound.boundReg < 0 ∧ bound.bound > 0 ∧ bound.bound * size ≤ extent.size then some ⟨size, extent.writable⟩
  else none

/-- `asm.checker.elementRegion`: the region `xE = xB + wI·size` addresses
    under the guard on `wI`, or none. A span whose element size is not
    `size` falls through to the region branch, as the Go does. -/
def elementRegion (frame : Int) (base : Base) (guard : Option IdxFact) (size : Int) : Option Region :=
  match guard with
  | none => none
  | some bound =>
    match base.frameAddr with
    | some addr => frameElement frame addr bound size
    | none =>
      match base.span with
      | some fact =>
        if fact.elem = size then spanElement fact bound size
        else match base.region with
          | some extent => regionElement extent bound size
          | none => none
      | none =>
        match base.region with
        | some extent => regionElement extent bound size
        | none => none

/-- `asm.checker.regionAccess`, its arithmetic: `[xR, #off]` (no index) or
    `[xR, wJ, uxtw]` under a constant guard `wJ < bound` (a register bound
    is refused) inside a region of `extent` bytes; a store needs a writable
    region. Operand shapes and alignment stay the seam's, in Go. -/
def regionAdmits (extent : Region) (isStore : Bool) (off size : Int) (index : Option IdxFact) : Bool :=
  if isStore = true ∧ extent.writable = false then false
  else
    match index with
    | some bound => decide (bound.boundReg < 0 ∧ bound.bound * size ≤ extent.size)
    | none => decide (0 ≤ off ∧ off + size ≤ extent.size)

/-- `asm.checker.frameArrayAccess`, its arithmetic: through the frame
    address `base` (entry-relative), `[xN, #off]` must lie inside the
    frame; `[xN, wI, uxtw]` under a constant guard `wI < bound` needs the
    `bound` elements inside it. -/
def frameArrayAdmits (frame base off size : Int) (index : Option IdxFact) : Bool :=
  match index with
  | some bound => decide (bound.boundReg < 0 ∧ -frame ≤ base ∧ base + bound.bound * size ≤ 0)
  | none => decide (-frame ≤ base + off ∧ base + off + size ≤ 0)

/-! ## What a guard means

A guard fact is sound only with a meaning for the register it bounds:
`i` is the runtime index in the guarded register, `len` the span's
runtime length where a span is concerned. -/

/-- The meaning of `bound` for the index `i` over a span of length `len`
    whose proven minimum (when `hasMin`) is below `len`: an immediate
    bound says `i < bound`; a register bound holding the length says
    `i < len`, or `i + bound ≤ len` for the slack form. -/
def GuardMeans (fact : SpanFact) (bound : IdxFact) (len i : Int) : Prop :=
  (fact.hasMin = true → fact.minLen ≤ len) ∧
  (bound.boundReg < 0 → i < bound.bound) ∧
  (bound.boundReg ≥ 0 → fact.holdsLen bound.boundReg = true →
    (bound.slack = false → i < len) ∧ (bound.slack = true → i + bound.bound ≤ len ∧ 1 ≤ bound.bound))

/-! ## Soundness -/

/-- A frame element: the region is one element, inside the frame. -/
theorem frameElement_sound (frame addr size : Int) (bound : IdxFact) (r : Region)
    (h : frameElement frame addr bound size = some r)
    (i : Int) (hi : 0 ≤ i) (hidx : i < bound.bound) (hsize : 0 ≤ size) :
    r.size = size ∧ InFrame frame (addr + i * size) size := by
  unfold frameElement at h
  split at h
  · simp at h
  · rename_i hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [not_or, Int.not_le, Int.not_lt] at hcond
    obtain ⟨_, _, hlo, hhi⟩ := hcond
    exact ⟨rfl, frame_element frame addr size bound.bound i (by omega) (by omega) hi hidx hsize⟩

/-- A frame element: an immediate guard is required. -/
theorem frameElement_register_bound_none (frame addr size : Int) (bound : IdxFact)
    (h : bound.boundReg ≥ 0) : frameElement frame addr bound size = none := by
  unfold frameElement
  simp [h]

/-- A span element: the region's bytes at element `i` lie inside the
    span's `size·len` for every length the guard admits. -/
theorem spanElement_sound (fact : SpanFact) (bound : IdxFact) (size len : Int) (r : Region)
    (h : spanElement fact bound size = some r)
    (i : Int) (hi : 0 ≤ i) (hsize : 0 ≤ size) (hg : GuardMeans fact bound len i) :
    i * size + r.size ≤ size * len := by
  obtain ⟨hmin, himm, hreg⟩ := hg
  unfold spanElement at h
  split at h
  · rename_i hslack
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hs, hge, hholds, _, _⟩ := hslack
    have hsum := ((hreg hge hholds).2 hs).1
    exact span_element_lanes size len i bound.bound hsize hsum
  · split at h
    · rename_i hin
      simp only [Option.some.injEq] at h
      subst h
      have hlt : i < len := by
        rcases hin with ⟨hs, hge, hholds⟩ | ⟨hneg, hhas, hle⟩
        · exact (hreg hge hholds).1 hs
        · exact Int.lt_of_lt_of_le (himm hneg) (Int.le_trans hle (hmin hhas))
      exact span_element size len i hi hsize hlt
    · simp at h

/-- A region derived from a span preserves exactly the span's writability
metadata; the slack form widens only its byte extent. -/
theorem spanElement_writable (fact : SpanFact) (bound : IdxFact) (size : Int)
    (r : Region) (h : spanElement fact bound size = some r) :
    r.writable = fact.writable := by
  unfold spanElement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst r
    rfl
  · split at h
    · simp only [Option.some.injEq] at h
      subst r
      rfl
    · simp at h

/-- A region element: the region is one element, inside the parent. -/
theorem regionElement_sound (extent : Region) (bound : IdxFact) (size : Int) (r : Region)
    (h : regionElement extent bound size = some r)
    (i : Int) (hi : 0 ≤ i) (hidx : i < bound.bound) (hsize : 0 ≤ size) :
    r.size = size ∧ i * size + size ≤ extent.size := by
  unfold regionElement at h
  split at h
  · rename_i hcond
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, region_element extent.size size bound.bound i hcond.2.2 hi hidx hsize⟩
  · simp at h

/-- Without a guard on the index nothing is derived. -/
theorem elementRegion_unguarded (frame : Int) (base : Base) (size : Int) :
    elementRegion frame base none size = none := rfl

/-- An access inside a region: its bytes lie inside the region's
    `extent`, and a store found the region writable. -/
theorem regionAdmits_offset_sound (extent : Region) (isStore : Bool) (off size : Int)
    (h : regionAdmits extent isStore off size none = true) :
    (0 ≤ off ∧ off + size ≤ extent.size) ∧ (isStore = true → extent.writable = true) := by
  unfold regionAdmits at h
  split at h
  · simp at h
  · rename_i hw
    simp only [decide_eq_true_eq] at h
    refine ⟨h, fun hs => ?_⟩
    cases hwr : extent.writable
    · exact absurd ⟨hs, hwr⟩ hw
    · rfl

/-- An indexed access inside a region: element `i` under the constant
    guard lies inside the region. -/
theorem regionAdmits_index_sound (extent : Region) (isStore : Bool) (off size : Int) (bound : IdxFact)
    (h : regionAdmits extent isStore off size (some bound) = true)
    (i : Int) (hi : 0 ≤ i) (hidx : i < bound.bound) (hsize : 0 ≤ size) :
    bound.boundReg < 0 ∧ i * size + size ≤ extent.size := by
  unfold regionAdmits at h
  split at h
  · simp at h
  · simp only [decide_eq_true_eq] at h
    exact ⟨h.1, region_element extent.size size bound.bound i h.2 hi hidx hsize⟩

/-- A store through a read-only region is refused. -/
theorem regionAdmits_store_readonly (extent : Region) (off size : Int) (index : Option IdxFact)
    (h : extent.writable = false) : regionAdmits extent true off size index = false := by
  unfold regionAdmits
  simp [h]

/-- An access through a frame address: inside the frame. -/
theorem frameArrayAdmits_offset_sound (frame base off size : Int)
    (h : frameArrayAdmits frame base off size none = true) :
    InFrame frame (base + off) size := by
  unfold frameArrayAdmits at h
  simp only [decide_eq_true_eq] at h
  exact h

/-- An indexed access through a frame address: element `i` under the
    constant guard lies inside the frame. -/
theorem frameArrayAdmits_index_sound (frame base off size : Int) (bound : IdxFact)
    (h : frameArrayAdmits frame base off size (some bound) = true)
    (i : Int) (hi : 0 ≤ i) (hidx : i < bound.bound) (hsize : 0 ≤ size) :
    InFrame frame (base + i * size) size := by
  unfold frameArrayAdmits at h
  simp only [decide_eq_true_eq] at h
  exact frame_element frame base size bound.bound i h.2.1 h.2.2 hi hidx hsize

/-! ## Composition: a derived region, then an access inside it -/

/-- A frame element region, then an offset access inside it: every byte
    lies inside the frame. -/
theorem frame_element_then_access (frame addr size : Int) (bound : IdxFact) (r : Region)
    (hr : frameElement frame addr bound size = some r)
    (i : Int) (hi : 0 ≤ i) (hidx : i < bound.bound) (hsize : 0 ≤ size)
    (off sz : Int) (ha : regionAdmits r false off sz none = true) :
    InFrame frame (addr + i * size + off) sz := by
  obtain ⟨hsz, hin⟩ := frameElement_sound frame addr size bound r hr i hi hidx hsize
  obtain ⟨⟨hlo, hhi⟩, _⟩ := regionAdmits_offset_sound r false off sz ha
  rw [hsz] at hhi
  unfold InFrame at hin ⊢
  constructor <;> omega

/-- A span element region, then an offset access inside it: every byte
    lies inside the span's `size·len`. -/
theorem span_element_then_access (fact : SpanFact) (bound : IdxFact) (size len : Int) (r : Region)
    (hr : spanElement fact bound size = some r)
    (i : Int) (hi : 0 ≤ i) (hsize : 0 ≤ size) (hg : GuardMeans fact bound len i)
    (off sz : Int) (ha : regionAdmits r false off sz none = true) :
    0 ≤ i * size + off ∧ i * size + off + sz ≤ size * len := by
  have hspan := spanElement_sound fact bound size len r hr i hi hsize hg
  obtain ⟨⟨hlo, hhi⟩, _⟩ := regionAdmits_offset_sound r false off sz ha
  have h0 : 0 ≤ i * size := Int.mul_nonneg hi hsize
  constructor <;> omega

/-- The exact arithmetic needed by an offset-form 64-bit pair store after a
slack-derived span element: a writable admitted 16-byte access covers two
adjacent u64 cells and remains inside the span.  This is a bounds/writability
fact only, not execution, atomicity, ordering, or publication authority. -/
theorem span_element_then_pair64_store (fact : SpanFact) (bound : IdxFact)
    (len : Int) (r : Region)
    (hr : spanElement fact bound fact.elem = some r) (helem : fact.elem = 8)
    (i d : Int) (hi : 0 ≤ i) (hg : GuardMeans fact bound len i)
    (ha : regionAdmits r true (8 * d) 16 none = true) :
    fact.writable = true ∧ 0 ≤ i + d ∧ i + d + 2 ≤ len := by
  rw [helem] at hr
  have hspan := spanElement_sound fact bound 8 len r hr i hi (by omega) hg
  have hwritable := spanElement_writable fact bound 8 r hr
  obtain ⟨⟨hoff, hend⟩, hstore⟩ :=
    regionAdmits_offset_sound r true (8 * d) 16 ha
  have hrw : r.writable = true := hstore rfl
  constructor
  · rw [← hwritable]
    exact hrw
  · constructor <;> omega


/-! ## The decisions rendered by the Go checker

Each line is one case of `asm/checker_refinement_test.go`, rendered by the
Go decision and checked here by `decide`; the test fails when a rendering
is missing, `lake build` when a rendering is wrong. -/

example : elementRegion 16 ⟨(some (-16)), none, none⟩ (some ⟨(-1), 4, false, 0⟩) 4 = some ⟨4, true⟩ := by decide
example : elementRegion 16 ⟨(some (-16)), none, none⟩ (some ⟨(-1), 5, false, 0⟩) 4 = none := by decide
example : elementRegion 16 ⟨(some (-16)), none, none⟩ (some ⟨1, 0, false, 0⟩) 4 = none := by decide
example : elementRegion 0 ⟨none, (some ⟨8, true, false, 0, [1]⟩), none⟩ (some ⟨1, 0, false, 0⟩) 8 = some ⟨8, true⟩ := by decide
example : elementRegion 0 ⟨none, (some ⟨8, false, true, 4, [1]⟩), none⟩ (some ⟨(-1), 4, false, 0⟩) 8 = some ⟨8, false⟩ := by decide
example : elementRegion 0 ⟨none, (some ⟨8, false, true, 4, [1]⟩), none⟩ (some ⟨(-1), 5, false, 0⟩) 8 = none := by decide
example : elementRegion 0 ⟨none, (some ⟨1, true, true, 16, [1]⟩), none⟩ (some ⟨1, 16, true, 0⟩) 1 = some ⟨16, true⟩ := by decide
example : elementRegion 0 ⟨none, (some ⟨8, true, true, 4, [1]⟩), none⟩ (some ⟨1, 4, true, 0⟩) 8 = some ⟨32, true⟩ := by decide
example : elementRegion 0 ⟨none, (some ⟨4, true, false, 0, [1]⟩), none⟩ (some ⟨1, 0, false, 0⟩) 8 = none := by decide
example : elementRegion 0 ⟨none, none, (some ⟨32, false⟩)⟩ (some ⟨(-1), 32, false, 0⟩) 1 = some ⟨1, false⟩ := by decide
example : elementRegion 0 ⟨none, none, (some ⟨32, false⟩)⟩ (some ⟨(-1), 33, false, 0⟩) 1 = none := by decide
example : regionAdmits ⟨12, true⟩ false 4 4 none = true := by decide
example : regionAdmits ⟨12, true⟩ false 12 4 none = false := by decide
example : regionAdmits ⟨12, false⟩ true 0 4 none = false := by decide
example : regionAdmits ⟨32, false⟩ false 0 1 (some ⟨(-1), 32, false, 0⟩) = true := by decide
example : regionAdmits ⟨12, true⟩ false 0 4 (some ⟨(-1), 4, false, 0⟩) = false := by decide
example : regionAdmits ⟨32, true⟩ true 0 16 none = true := by decide
example : regionAdmits ⟨32, true⟩ true 16 16 none = true := by decide
example : regionAdmits ⟨32, true⟩ true 24 16 none = false := by decide
example : regionAdmits ⟨32, false⟩ true 0 16 none = false := by decide
example : frameArrayAdmits 16 (-16) 4 4 none = true := by decide
example : frameArrayAdmits 16 (-16) 12 8 none = false := by decide
example : frameArrayAdmits 16 (-16) 0 4 (some ⟨(-1), 4, false, 0⟩) = true := by decide
example : frameArrayAdmits 16 (-16) 0 4 (some ⟨(-1), 5, false, 0⟩) = false := by decide
example : frameArrayAdmits 16 (-16) 0 4 (some ⟨1, 0, false, 0⟩) = false := by decide

end Oak.CheckerRefinement
