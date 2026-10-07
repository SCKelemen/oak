import Std

/-!
# Bounded index disjointness

Arithmetic obligations for asm/index_bounds.go. Bounds describe actual unsigned
word values, not assumed allocation sizes. Known-bit bounds come from the existing
known-bit analysis (Oak.KnownBits). Addition and subtraction refine bounds only
when every value avoids wraparound. Width adaptation retains an interval only
when its upper endpoint fits; otherwise the implementation falls back to known
bits. These laws are not a refinement of the Go recursive analyzer; exhaustive
mixed-width evaluation tests separately exercise that implementation.
-/
namespace Oak.IndexBounds

structure Interval where
  lo : Nat
  hi : Nat

def Contains (b : Interval) (x : Nat) : Prop := b.lo ≤ x ∧ x ≤ b.hi

def Disjoint (a b : Interval) : Prop := a.hi < b.lo ∨ b.hi < a.lo

theorem disjoint_ne {a b : Interval} {x y : Nat}
    (hx : Contains a x) (hy : Contains b y) (h : Disjoint a b) : x ≠ y := by
  unfold Contains Disjoint at *
  omega

theorem add_no_wrap {a b : Interval} {x y modulus : Nat}
    (hx : Contains a x) (hy : Contains b y) (h : a.hi + b.hi < modulus) :
    Contains ⟨a.lo + b.lo, a.hi + b.hi⟩ ((x + y) % modulus) := by
  have fit : x + y < modulus := by unfold Contains at *; omega
  rw [Nat.mod_eq_of_lt fit]
  unfold Contains at *
  simp only
  omega

theorem sub_no_wrap {a b : Interval} {x y modulus : Nat}
    (hx : Contains a x) (hy : Contains b y) (h : b.hi ≤ a.lo)
    (fit : a.hi < modulus) :
    Contains ⟨a.lo - b.hi, a.hi - b.lo⟩ ((x - y) % modulus) := by
  have below : x - y < modulus := by unfold Contains at *; omega
  rw [Nat.mod_eq_of_lt below]
  unfold Contains at *
  simp only
  omega

theorem adapt_no_wrap {a : Interval} {x modulus : Nat}
    (hx : Contains a x) (fit : a.hi < modulus) : Contains a (x % modulus) := by
  rw [Nat.mod_eq_of_lt (show x < modulus by unfold Contains at hx; omega)]
  exact hx

theorem join_contains {a b : Interval} {x : Nat}
    (hx : Contains a x ∨ Contains b x) :
    Contains ⟨min a.lo b.lo, max a.hi b.hi⟩ x := by
  unfold Contains at *
  simp only
  omega

theorem intersect_contains {a b : Interval} {x : Nat}
    (ha : Contains a x) (hb : Contains b x) :
    Contains ⟨max a.lo b.lo, min a.hi b.hi⟩ x := by
  unfold Contains at *
  simp only
  omega

/-- Removing a disjoint write preserves the read even when the write is guarded. -/
theorem skip_disjoint_write {α : Type} {a b : Interval} {read write : Nat}
    (hr : Contains a read) (hw : Contains b write) (hd : Disjoint a b)
    (guard : Bool) (new old : α) :
    (if guard && decide (read = write) then new else old) = old := by
  simp [disjoint_ne hr hw hd]

end Oak.IndexBounds
