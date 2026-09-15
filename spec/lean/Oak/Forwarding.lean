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

end Oak.Forwarding
