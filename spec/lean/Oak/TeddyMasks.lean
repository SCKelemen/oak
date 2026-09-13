import Oak.Teddy
/-!
# Teddy: the byte-level masks

`Oak.Teddy` proves the prefilter sound at the level of table *predicates*.
The compiler and `stdlib/literals.oak` `build` store those predicates as
`u8` bucket masks — bit `b` of table `k` at nibble `n` is set when some
literal of bucket `b` has that nibble at byte `k` — and the kernel ANDs
six looked-up masks. This file closes that gap: the mask built by ORing
the bucket bits of the literals whose nibble matches has bit `b` set
exactly when the predicate holds, and the AND of masks has bit `b` set
exactly when each operand has, so the kernel's `(mask & bit) != 0` test
is the predicate `cand`.
-/

namespace Oak.Teddy.Masks

open Oak.Teddy

/-- Bit `b` of a mask: the kernel's `(m & bucket_bit(j)) != 0`. -/
def bit (m : UInt8) (b : Fin 8) : Bool := m.toNat.testBit b.val

/-- The bucket bit of `b`: `1 <<< b`. -/
def bucketBit (b : Fin 8) : UInt8 := (1 : UInt8) <<< (UInt8.ofNat b.val)

/-- The OR of the bucket bits of a list of buckets, as `build`'s loop
computes an entry. -/
def maskOf (bs : List (Fin 8)) : UInt8 := bs.foldl (fun m b => m ||| bucketBit b) 0

theorem bit_and (x y : UInt8) (b : Fin 8) : bit (x &&& y) b = (bit x b && bit y b) := by
  simp [bit, UInt8.toNat_and, Nat.testBit_and]

theorem bit_or (x y : UInt8) (b : Fin 8) : bit (x ||| y) b = (bit x b || bit y b) := by
  simp [bit, UInt8.toNat_or, Nat.testBit_or]

theorem bit_zero (b : Fin 8) : bit 0 b = false := by
  simp [bit]

theorem bit_bucketBit (b c : Fin 8) : bit (bucketBit c) b = decide (b = c) := by
  revert b c; decide

/-- Bit `b` of the OR-fold is set exactly when `b` is one of the buckets. -/
theorem bit_maskOf (bs : List (Fin 8)) (b : Fin 8) : bit (maskOf bs) b = decide (b ∈ bs) := by
  suffices h : ∀ (m : UInt8), bit (bs.foldl (fun m b => m ||| bucketBit b) m) b = (bit m b || decide (b ∈ bs)) by
    have := h 0
    simpa [maskOf, bit_zero] using this
  induction bs with
  | nil => intro m; simp
  | cons c bs ih =>
    intro m
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, bit_or, bit_bucketBit, Bool.or_assoc]
    by_cases h1 : b = c <;> by_cases h2 : b ∈ bs <;> simp [h1, h2]

/-! ## The stored tables are the predicates -/

variable {L : Nat}

/-- The entry `build` stores in table `k` at low nibble `n`: the bucket
bits of the literals whose byte `k` has that low nibble. -/
def loEntry (s : LitSet L) (k : Nat) (n : UInt8) : UInt8 :=
  maskOf (((List.finRange L).filter fun i => lowNib (byteAt (s.lit i) k) == n).map s.bkt)

/-- The entry at high nibble `n`. -/
def hiEntry (s : LitSet L) (k : Nat) (n : UInt8) : UInt8 :=
  maskOf (((List.finRange L).filter fun i => highNib (byteAt (s.lit i) k) == n).map s.bkt)

theorem bit_loEntry (s : LitSet L) (k : Nat) (n : UInt8) (b : Fin 8) :
    bit (loEntry s k n) b = true ↔ lo s k n b := by
  rw [loEntry, bit_maskOf]
  simp only [decide_eq_true_eq, List.mem_map, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq, lo]
  constructor
  · intro ⟨i, hn, hb⟩; exact ⟨i, hb, hn⟩
  · intro ⟨i, hb, hn⟩; exact ⟨i, hn, hb⟩

theorem bit_hiEntry (s : LitSet L) (k : Nat) (n : UInt8) (b : Fin 8) :
    bit (hiEntry s k n) b = true ↔ hi s k n b := by
  rw [hiEntry, bit_maskOf]
  simp only [decide_eq_true_eq, List.mem_map, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq, hi]
  constructor
  · intro ⟨i, hn, hb⟩; exact ⟨i, hb, hn⟩
  · intro ⟨i, hb, hn⟩; exact ⟨i, hn, hb⟩

/-- One byte's looked-up mask: the kernel's `tbl(lo, c & 15) & tbl(hi, c >> 4)`. -/
def lookupMask (s : LitSet L) (k : Nat) (c : UInt8) : UInt8 :=
  loEntry s k (lowNib c) &&& hiEntry s k (highNib c)

theorem bit_lookupMask (s : LitSet L) (k : Nat) (c : UInt8) (b : Fin 8) :
    bit (lookupMask s k c) b = true ↔ lookup s k c b := by
  rw [lookupMask, bit_and, Bool.and_eq_true, bit_loEntry, bit_hiEntry]
  rfl

/-- The kernel's candidate mask at `p`: the AND of the three lookups over
the bytes at `p`, `p + 1`, `p + 2`. -/
def candMask (s : LitSet L) (t : List UInt8) (p : Nat) : UInt8 :=
  lookupMask s 0 (byteAt t p) &&& lookupMask s 1 (byteAt t (p + 1)) &&& lookupMask s 2 (byteAt t (p + 2))

/-- **The bridge**: the kernel's test `(cand & bucket_bit(j)) != 0` on the
stored masks is exactly the predicate `Oak.Teddy.cand`, so `Oak.Teddy.sound`
and `exact` speak about the emitted bytes. -/
theorem bit_candMask (s : LitSet L) (t : List UInt8) (p : Nat) (b : Fin 8) :
    bit (candMask s t p) b = true ↔ cand s t p b := by
  rw [candMask, bit_and, bit_and, Bool.and_eq_true, Bool.and_eq_true, bit_lookupMask, bit_lookupMask, bit_lookupMask]
  unfold cand
  constructor
  · intro ⟨⟨h0, h1⟩, h2⟩; exact ⟨h0, h1, h2⟩
  · intro ⟨h0, h1, h2⟩; exact ⟨⟨h0, h1⟩, h2⟩

/-- Soundness restated on the stored masks: a literal at `p` sets its
bucket's bit in the kernel's candidate mask there. -/
theorem sound_mask (s : LitSet L) (t : List UInt8) (p : Nat) (i : Fin L)
    (h : occursAt (s.lit i) t p) : bit (candMask s t p) (s.bkt i) = true :=
  (bit_candMask s t p (s.bkt i)).2 (sound s t p i h)

end Oak.Teddy.Masks
