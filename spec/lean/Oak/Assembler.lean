/-!
# The typed assembler: seam laws

`docs/spec/94-assembler.md` §3–§4. The asm checker (`asm/check.go`) is
maintained as the transliteration of the laws here:

* **register aliasing** — `wN` and `xN` name one physical register, so a
  write through either width is a write of the same authority slot
  (`asm.checker.write` keys on the physical number);
* **alignment extents** — every AArch64 instruction is 4 bytes, so an
  aligned region of `k` instructions fits its `N`-byte stride exactly when
  `4k ≤ N`, and a table of `n` such regions occupies `n·N` bytes: sixteen
  128-byte entries are exactly a 2 KiB vector table
  (`asm.checker.closeRegion`);
* **frame bounds** — an access at `addr` (relative to the entry sp) of
  `size` bytes lies inside the declared frame `[-frame, 0)` exactly when
  `-frame ≤ addr` and `addr + size ≤ 0`, and a chain of such accesses never
  touches memory the frame does not own (`asm.checker.checkAccess`).
-/

namespace Oak.Assembler

/-- Register width views of the general-purpose file. -/
inductive Width where
  | x   -- 64-bit view
  | w   -- 32-bit view
  deriving DecidableEq, Repr

/-- A general register operand: a width view of a physical register. -/
structure Reg where
  width : Width
  num : Nat
  deriving DecidableEq, Repr

/-- The physical register an operand names: the view is erased. -/
def physical (r : Reg) : Nat := r.num

/-- Aliasing: the 32-bit and 64-bit views of register `n` are one
    authority slot. A clobber declaration or binding for either covers
    both, and a write through either is a write of the same register. -/
theorem alias_same_physical (n : Nat) :
    physical ⟨Width.w, n⟩ = physical ⟨Width.x, n⟩ := rfl

/-- Two operands touch the same register iff their numbers agree,
    whatever their widths. -/
theorem same_register_iff (a b : Reg) :
    physical a = physical b ↔ a.num = b.num := Iff.rfl

/-- AArch64 instructions are fixed-width. -/
def instructionBytes : Nat := 4

/-- The byte extent of a region of `k` instructions. -/
def regionBytes (k : Nat) : Nat := k * instructionBytes

/-- A region fits its alignment stride when its bytes do not exceed it. -/
def Fits (k stride : Nat) : Prop := regionBytes k ≤ stride

theorem fits_iff (k stride : Nat) : Fits k stride ↔ 4 * k ≤ stride := by
  unfold Fits regionBytes instructionBytes
  constructor <;> intro h <;> omega

/-- The transliterated extent check. -/
def fitsCheck (k stride : Nat) : Bool := decide (k * 4 ≤ stride)

theorem fitsCheck_sound (k stride : Nat) (h : fitsCheck k stride = true) :
    Fits k stride := by
  unfold fitsCheck at h
  unfold Fits regionBytes instructionBytes
  exact of_decide_eq_true h

theorem fitsCheck_complete (k stride : Nat) (h : Fits k stride) :
    fitsCheck k stride = true := by
  unfold Fits regionBytes instructionBytes at h
  unfold fitsCheck
  exact decide_eq_true h

/-- A table of `n` aligned entries at stride `N` occupies `n * N` bytes
    when every entry fits: the entries are laid end to end at exactly one
    stride each. -/
def tableBytes (entries stride : Nat) : Nat := entries * stride

/-- The exception vector table: sixteen 128-byte entries are exactly 2 KiB,
    so a table aligned to 2048 whose entries each fit 128 bytes has no
    padding between entries and its extent equals its alignment. -/
theorem vector_table_extent : tableBytes 16 128 = 2048 := rfl

/-- An entry of at most 32 instructions fits a 128-byte slot. -/
theorem vector_entry_fits (k : Nat) (h : k ≤ 32) : Fits k 128 := by
  rw [fits_iff]; omega

/-- Frame bounds: the declared frame is `[-frame, 0)` relative to the
    entry sp. Integers model signed byte addresses. -/
def InFrame (frame addr size : Int) : Prop :=
  -frame ≤ addr ∧ addr + size ≤ 0

/-- The transliterated access check. -/
def accessCheck (frame addr size : Int) : Bool :=
  decide (-frame ≤ addr ∧ addr + size ≤ 0)

theorem accessCheck_sound (frame addr size : Int)
    (h : accessCheck frame addr size = true) : InFrame frame addr size := by
  unfold accessCheck at h
  unfold InFrame
  exact of_decide_eq_true h

theorem accessCheck_complete (frame addr size : Int)
    (h : InFrame frame addr size) : accessCheck frame addr size = true := by
  unfold InFrame at h
  unfold accessCheck
  exact decide_eq_true h

/-- Every byte of an in-frame access lies inside the frame interval: the
    access cannot reach memory the frame does not own. -/
theorem inFrame_bytes (frame addr size b : Int) (h : InFrame frame addr size)
    (hb : addr ≤ b ∧ b < addr + size) : -frame ≤ b ∧ b < 0 := by
  obtain ⟨hlo, hhi⟩ := h
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> omega

/-- The static sp displacement stays inside `[0, frame]` under a move by
    `delta` exactly when the checker's bound holds — the invariant that
    makes `checkAccess`'s `-disp + offset` arithmetic meaningful. -/
def DispOk (frame disp : Int) : Prop := 0 ≤ disp ∧ disp ≤ frame

theorem disp_move (frame disp delta : Int) (h : DispOk frame (disp + delta)) :
    0 ≤ disp + delta ∧ disp + delta ≤ frame := h

/-- Typed pointer memory: a span of `len` elements of `elem` bytes owns
    bytes `[0, elem*len)`. A dominating guard establishes `minLen ≤ len`;
    the checker admits an access `[off, off+size)` when
    `off + size ≤ elem * minLen` — which places every accessed byte inside
    the span for every runtime length the guard admits
    (`asm.checker.spanAccess`). -/
def SpanAccessOk (elem minLen off size : Nat) : Prop :=
  off + size ≤ elem * minLen

theorem span_access (elem minLen len off size : Nat)
    (hguard : minLen ≤ len) (hacc : SpanAccessOk elem minLen off size) :
    off + size ≤ elem * len := by
  unfold SpanAccessOk at hacc
  calc off + size ≤ elem * minLen := hacc
    _ ≤ elem * len := Nat.mul_le_mul_left elem hguard

/-- Every byte of an admitted span access lies inside the span. -/
theorem span_access_bytes (elem minLen len off size b : Nat)
    (hguard : minLen ≤ len) (hacc : SpanAccessOk elem minLen off size)
    (hb : off ≤ b ∧ b < off + size) : b < elem * len := by
  have h := span_access elem minLen len off size hguard hacc
  omega

/-- The transliterated check. -/
def spanAccessCheck (elem minLen off size : Nat) : Bool :=
  decide (off + size ≤ elem * minLen)

theorem spanAccessCheck_sound (elem minLen off size : Nat)
    (h : spanAccessCheck elem minLen off size = true) :
    SpanAccessOk elem minLen off size := by
  unfold spanAccessCheck at h
  unfold SpanAccessOk
  exact of_decide_eq_true h

/-- **Indexed span access**: an element access `[base, wI, uxtw #s]` with
    `1 << s = elem` touches bytes `[i*elem, (i+1)*elem)`; under the index
    guard `i < len` every one of them lies inside the span's `elem * len`
    bytes. The constant-bound form composes this with the length guard:
    `i < K` and `K ≤ len` give `i < len`. -/
theorem index_access (elem len i : Nat) (hguard : i < len) :
    (i + 1) * elem ≤ elem * len := by
  have h : i + 1 ≤ len := hguard
  calc (i + 1) * elem = elem * (i + 1) := Nat.mul_comm _ _
    _ ≤ elem * len := Nat.mul_le_mul_left elem h

theorem index_access_const (elem len i K : Nat) (hidx : i < K) (hlen : K ≤ len) :
    (i + 1) * elem ≤ elem * len :=
  index_access elem len i (Nat.lt_of_lt_of_le hidx hlen)

/-- **Vector access**: a `K`-lane access at element index `i` touches bytes
    `[i*elem, (i+K)*elem)`; under the slack guard `i + K ≤ len` (the
    checker's `sub wT, wL, #K; cmp wI, wT; b.hi trap`, with `len ≥ K` so
    the subtraction did not wrap) every one of them lies inside the span's
    `elem * len` bytes. `K = 1` is `index_access`. -/
theorem index_access_lanes (elem len i K : Nat) (hguard : i + K ≤ len) :
    (i + K) * elem ≤ elem * len := by
  calc (i + K) * elem = elem * (i + K) := Nat.mul_comm _ _
    _ ≤ elem * len := Nat.mul_le_mul_left elem hguard

/-- The slack guard is what the checker reads off the two compares: with
    `len ≥ K`, `wT = len - K` is exact and `i ≤ wT` is `i + K ≤ len`. -/
theorem slack_guard (len i K : Nat) (hmin : K ≤ len) (hle : i ≤ len - K) : i + K ≤ len := by
  omega

/-- **Guard facts across a merge.** A label holds the meet of its
    predecessors' facts: for proven minimum lengths, the smaller of the
    two — which is a valid minimum whichever predecessor control came
    from — and for index bounds, only a fact both sides carry. -/
theorem meet_sound_left (a b len : Nat) (h : a ≤ len) : min a b ≤ len :=
  Nat.le_trans (Nat.min_le_left a b) h

theorem meet_sound_right (a b len : Nat) (h : b ≤ len) : min a b ≤ len :=
  Nat.le_trans (Nat.min_le_right a b) h

/-- The merged minimum is a lower bound on the length however the label was
    reached: from a predecessor proving `a ≤ len` or one proving `b ≤ len`. -/
theorem meet_sound (a b len : Nat) (h : a ≤ len ∨ b ≤ len) : min a b ≤ len := by
  rcases h with h | h
  · exact meet_sound_left a b len h
  · exact meet_sound_right a b len h

/-- Every byte of an admitted indexed access lies inside the span. -/
theorem index_access_bytes (elem len i b : Nat) (hguard : i < len)
    (hb : i * elem ≤ b ∧ b < (i + 1) * elem) : b < elem * len := by
  have h := index_access elem len i hguard
  omega

/-! ## Derived element regions (the seam checker's `elementRegion`,
`frameArrayAccess`, `regionAccess`; refined in `Oak.CheckerRefinement`)

Integers model signed byte addresses and Go's `int64`. An element index
`i` read from a register is non-negative. -/

/-- A frame array's element: with the `K` elements of `size` bytes at
    `addr` inside the frame (`-frame ≤ addr`, `addr + K·size ≤ 0`), the
    element `i < K` lies inside it. -/
theorem frame_element (frame addr size K i : Int)
    (hlo : -frame ≤ addr) (hhi : addr + K * size ≤ 0)
    (hi : 0 ≤ i) (hidx : i < K) (hsize : 0 ≤ size) :
    InFrame frame (addr + i * size) size := by
  have h1 : (i + 1) * size ≤ K * size := Int.mul_le_mul_of_nonneg_right (by omega) hsize
  rw [Int.add_mul, Int.one_mul] at h1
  have h2 : 0 ≤ i * size := Int.mul_nonneg hi hsize
  unfold InFrame
  constructor <;> omega

/-- A span element under `i < len`: its `size` bytes at `i·size` lie inside
    the span's `size·len` (the `Int` twin of `index_access`). -/
theorem span_element (size len i : Int) (hi : 0 ≤ i) (hsize : 0 ≤ size) (hlt : i < len) :
    i * size + size ≤ size * len := by
  have h1 : (i + 1) * size ≤ len * size := Int.mul_le_mul_of_nonneg_right (by omega) hsize
  rw [Int.add_mul, Int.one_mul, Int.mul_comm len size] at h1
  exact h1

/-- `K` elements from `i` under the slack guard `i + K ≤ len`: their
    `K·size` bytes lie inside the span (the `Int` twin of
    `index_access_lanes`). -/
theorem span_element_lanes (size len i K : Int) (hsize : 0 ≤ size) (hsum : i + K ≤ len) :
    i * size + size * K ≤ size * len := by
  have h1 : (i + K) * size ≤ len * size := Int.mul_le_mul_of_nonneg_right hsum hsize
  rw [Int.add_mul, Int.mul_comm K size, Int.mul_comm len size] at h1
  exact h1

/-- An element of a bounded region: with `K` elements of `size` bytes
    inside `extent` bytes, the element `i < K` lies inside it. -/
theorem region_element (extent size K i : Int) (hfit : K * size ≤ extent)
    (hi : 0 ≤ i) (hidx : i < K) (hsize : 0 ≤ size) :
    i * size + size ≤ extent := by
  have h1 : (i + 1) * size ≤ K * size := Int.mul_le_mul_of_nonneg_right (by omega) hsize
  rw [Int.add_mul, Int.one_mul] at h1
  omega

/-- Every byte of an access `[off, off+size)` admitted inside `extent`
    bytes lies inside them. -/
theorem region_offset_bytes (extent off size b : Int) (hlo : 0 ≤ off) (hhi : off + size ≤ extent)
    (hb : off ≤ b ∧ b < off + size) : 0 ≤ b ∧ b < extent := by
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> omega

/-! ## Entry padding

`asm/object.go` (`textLayout.pad`) fills the gap before an entry with the
lane's no-ops. AArch64 gaps are whole words. An RV64 function under RVC
(docs/spec/94-assembler.md, "Compressed encodings") ends on a half word
when it holds an odd number of two-byte instructions, so its gap is
filled in words and closed by one two-byte `c.nop`. -/

/-- The bytes needed to reach the next multiple of `align` from `len`. -/
def gap (len align : Nat) : Nat := (align - len % align) % align

/-- Reaching the boundary: `len + gap` is a multiple of the alignment. -/
theorem gap_reaches (len align : Nat) (h : 0 < align) :
    (len + gap len align) % align = 0 := by
  unfold gap
  rcases Nat.eq_zero_or_pos (len % align) with hz | hp
  · rw [hz, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    exact hz
  · have hlt := Nat.mod_lt len h
    rw [Nat.mod_eq_of_lt (Nat.sub_lt h hp)]
    have hdiv := Nat.div_add_mod len align
    have hsum : len + (align - len % align) = align * (len / align + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [hsum, Nat.mul_mod_right]

/-- Filling in halfwords: an even gap is `w` words and at most one
    halfword, so the RV64 fill (words, then a `c.nop` when two bytes remain)
    produces exactly the gap. -/
theorem pad_halfwords_reaches (g : Nat) (h : g % 2 = 0) :
    4 * (g / 4) + (if g % 4 = 2 then 2 else 0) = g := by
  split <;> omega

/-- Filling in words alone misses: when the gap is not a multiple of four,
    no number of four-byte no-ops equals it — the fixed word pad of the
    earlier layout would never reach the boundary. -/
theorem pad_words_misses (g : Nat) (h : g % 4 ≠ 0) : ∀ w : Nat, 4 * w ≠ g := by
  intro w hw
  apply h
  omega

/-- A compressed RV64 entry ends on a half word exactly when it holds an
    odd number of two-byte instructions among its words. -/
theorem rvc_entry_half_word (words halves : Nat) :
    (4 * words + 2 * halves) % 4 = 2 ↔ halves % 2 = 1 := by
  constructor <;> intro h <;> omega

end Oak.Assembler
