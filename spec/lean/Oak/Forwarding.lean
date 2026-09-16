/-!
# Frame-slot forwarding

The native lane's frame-slot forwarding (docs/spec/94-assembler.md §9
"Slot forwarding"): a load of a frame slot that a register was just stored
to, or loaded from, with the register unwritten since, is the register's
value — the generator emits a `mov` or nothing. The model is a frame as a
map from slot offsets to words; the register file changes only through the
writes the generator tracks, so the value it recorded is the value the load
would read. The second rule turns `cset` followed by `cbz`/`cbnz` into the
one conditional branch: the materialized Bool is zero exactly when the
condition is false.
-/

namespace Oak.Forwarding

/-- A frame: words by slot offset. -/
def Frame := Nat → Nat

/-- The frame after a store of `v` at `off`. -/
def store (f : Frame) (off v : Nat) : Frame := fun o => if o = off then v else f o

/-- A load reads the stored value back. -/
theorem load_store (f : Frame) (off v : Nat) : store f off v off = v := by
  simp [store]

/-- A store leaves the other slots alone. -/
theorem load_store_other (f : Frame) (off off' v : Nat) (h : off' ≠ off) :
    store f off v off' = f off' := by
  simp [store, h]

/-- The forwarding rule: after `str r, [slot]` — the slot holds the
register's value — a load of the slot is the register's value, so long as
neither the register nor the slot was written in between (the generator
drops the record at any write of either, at labels, calls, and stores
through other bases). -/
theorem forward (regs : Nat → Nat) (f : Frame) (r off : Nat) :
    store f off (regs r) off = regs r :=
  load_store f off (regs r)

/-- A store that does not touch a held slot (its bytes lie apart) leaves
the held value in place: the generator forgets only the slots a store's
extent overlaps. -/
theorem held_survives (f : Frame) (off other v w : Nat) (h : other ≠ off) :
    store (store f off v) other w off = v := by
  simp [store, Ne.symm h]

/-- `cset wD, cond` materializes a condition as 0 or 1. -/
def cset (c : Bool) : Nat := if c then 1 else 0

/-- `cbz` of the materialized Bool jumps exactly when the condition is
false: `cmp; cset; cbz` is `cmp; b.!cond`. -/
theorem cbz_cset (c : Bool) : (cset c = 0) = (c = false) := by
  cases c <;> simp [cset]

/-- `cbnz` of the materialized Bool jumps exactly when the condition holds:
`cmp; cset; cbnz` is `cmp; b.cond`. -/
theorem cbnz_cset (c : Bool) : (cset c ≠ 0) = (c = true) := by
  cases c <;> simp [cset]

/-- For an unsigned value, the branch condition `x < 1` is exactly a zero
test; its complement `x ≥ 1` is therefore exactly a nonzero test. -/
theorem unsigned_lt_one_is_zero (x : Nat) : x < 1 ↔ x = 0 := by
  constructor
  · intro h
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
  · intro h
    simp [h]

/-! ## Zero-index scalar store cleanup

This is the deliberately small equality used by AArch64 late cleanup. It
models only the address and value observed at the store boundary. It is not a
memory model, an alignment proof, or an instruction-execution semantics. -/

/-- The scalar indexed-address shape, in bytes: A64's register index is
zero-extended and shifted by the access-size log2. -/
def indexedAddress (base index shift : Nat) : Nat := base + index * 2 ^ shift

/-- Materializing a zero index cannot change the store address. -/
theorem indexedAddress_zero (base shift : Nat) :
    indexedAddress base 0 shift = base := by
  simp [indexedAddress]

/-- The address/value observation of an indexed scalar store. -/
def storeObservation (base index shift value : Nat) : Nat × Nat :=
  (indexedAddress base index shift, value)

/-- Forwarding the source value and erasing a materialized zero index preserves
the local store address/value observation. -/
theorem zero_index_store (base shift value : Nat) :
    storeObservation base 0 shift value = (base, value) := by
  simp [storeObservation, indexedAddress]

end Oak.Forwarding
