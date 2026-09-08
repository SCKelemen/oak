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

end Oak.Assembler
