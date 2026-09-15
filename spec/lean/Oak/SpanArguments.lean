import Std.Tactic.BVDecide

/-!
# Span arguments over the caller's owned arrays

Model for docs/spec/94-assembler.md §8 (span arguments over owned arrays,
the call summary). A caller passes `span(&buf)` over its own frame array:
the array's frame address and its constant length. The summary binds the
callee's span parameter to the array's contents, one leaf per element read
from the frame slot `[addr + i*elem, addr + (i+1)*elem)`, and after the
body stores a writable span's final leaves back, leaf `i` into slot `i`.
The theorems: the element slots are pairwise disjoint, so the write-back
of one leaf disturbs no other element; a leaf written back is read back
from its slot; and the slots of an array of `n` elements lie inside the
array's `n * elem` bytes.
-/

namespace Oak.SpanArguments

/-- The byte range of element `i`: `[addr + i*elem, addr + (i+1)*elem)`. -/
def Slot (addr i elem b : Nat) : Prop :=
  addr + i * elem ≤ b ∧ b < addr + (i + 1) * elem

/-- **Disjoint slots**: distinct elements share no byte. -/
theorem slots_disjoint (addr i j elem b : Nat) (hij : i ≠ j)
    (hi : Slot addr i elem b) (hj : Slot addr j elem b) : False := by
  unfold Slot at hi hj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · -- i < j: element i ends at or before element j begins.
    have : (i + 1) * elem ≤ j * elem := Nat.mul_le_mul_right elem h
    omega
  · have : (j + 1) * elem ≤ i * elem := Nat.mul_le_mul_right elem h
    omega

/-- **Inside the array**: every byte of element `i < n` lies in the array's
    `[addr, addr + n*elem)`. -/
theorem slot_in_array (addr n i elem b : Nat) (hi : i < n) (hb : Slot addr i elem b) :
    addr ≤ b ∧ b < addr + n * elem := by
  unfold Slot at hb
  have : (i + 1) * elem ≤ n * elem := Nat.mul_le_mul_right elem hi
  constructor
  · have : addr ≤ addr + i * elem := Nat.le_add_right _ _
    omega
  · omega

/-- The frame as a byte-indexed memory; a store of `elem` bytes of a value
    at the element's slot, little-endian, byte by byte. -/
def storeBytes (mem : Nat → BitVec 8) (base : Nat) (w : Nat) (v : BitVec (8 * w)) : Nat → BitVec 8 :=
  fun b => if base ≤ b ∧ b < base + w then (v >>> (8 * (b - base))).truncate 8 else mem b

/-- **Write-back lands in its slot**: a byte outside the element's slot is
    unchanged by the store of that element. -/
theorem store_outside_unchanged (mem : Nat → BitVec 8) (base w : Nat) (v : BitVec (8 * w)) (b : Nat)
    (h : ¬ (base ≤ b ∧ b < base + w)) : storeBytes mem base w v b = mem b := by
  unfold storeBytes
  simp [h]

/-- **Read-back**: the stored value's byte `k` is read back from byte
    `base + k` of the slot. -/
theorem store_read_back (mem : Nat → BitVec 8) (base w : Nat) (v : BitVec (8 * w)) (k : Nat) (hk : k < w) :
    storeBytes mem base w v (base + k) = (v >>> (8 * k)).truncate 8 := by
  unfold storeBytes
  have : base ≤ base + k ∧ base + k < base + w := ⟨Nat.le_add_right _ _, by omega⟩
  simp [this]

/-- Two elements written back in sequence: the first's bytes survive the
    second's store, since the slots are disjoint (`i ≠ j`). -/
theorem two_writes_commute_on_first (mem : Nat → BitVec 8) (addr i j elem : Nat)
    (vi vj : BitVec (8 * elem)) (hij : i ≠ j) (k : Nat) (hk : k < elem) :
    storeBytes (storeBytes mem (addr + i * elem) elem vi) (addr + j * elem) elem vj (addr + i * elem + k)
      = (vi >>> (8 * k)).truncate 8 := by
  have hout : ¬ (addr + j * elem ≤ addr + i * elem + k ∧ addr + i * elem + k < addr + j * elem + elem) := by
    intro h
    exact slots_disjoint addr i j elem (addr + i * elem + k) hij
      ⟨Nat.le_add_right _ _, by rw [Nat.succ_mul]; omega⟩
      ⟨h.1, by rw [Nat.succ_mul]; omega⟩
  rw [store_outside_unchanged _ _ _ _ _ hout]
  exact store_read_back mem (addr + i * elem) elem vi k hk

end Oak.SpanArguments

namespace Oak.SpanArguments

/-- **A record copy's chunks**: the 8-byte chunks of a record copied into
    the frame are disjoint slots (the element law at `elem = 8`), so the
    summary reading chunk `k` from slot `k` reads the record's bytes
    `[8k, 8k + 8)` and no other chunk's. -/
theorem record_chunks_disjoint (addr k j b : Nat) (hkj : k ≠ j)
    (hk : Slot addr k 8 b) (hj : Slot addr j 8 b) : False :=
  slots_disjoint addr k j 8 b hkj hk hj

end Oak.SpanArguments
