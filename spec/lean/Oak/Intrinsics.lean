namespace Oak.Intrinsics

/-! # Abstract assembly intrinsics

Model for `docs/spec/92-ffi.md` §3: the v1 AArch64 instruction functions
`rev` (byte reverse), `rbit` (bit reverse), and `clz` (count leading
zeros). The model works over the value's digits — bytes for `rev`, bits
for `rbit` — as lists of fixed width, which is exactly the register-lane
view the instructions are specified over in the ARM ARM. Laws proven:

- `rev` and `rbit` are width-preserving involutions;
- `clz` is total, bounded by the width, hits the width exactly on the
  zero word, and is zero exactly when the leading bit is set — the ARM
  `CLZ` semantics, including the `CLZ(0) = width` case that C's
  `__builtin_clz` leaves undefined (the backend's guard supplies it).
-/

/-- Register-lane view: a word is its list of digits (bits or bytes),
    most significant first, of exactly the register width. -/
def Word (α : Type) (width : Nat) := { digits : List α // digits.length = width }

/-- `REV`/`RBIT`: reverse the digit lanes. -/
def reverse {α : Type} {width : Nat} (w : Word α width) : Word α width :=
  ⟨w.val.reverse, by rw [List.length_reverse]; exact w.property⟩

/-- **Width preservation**: the reversed word is a word of the same width
    (definitional, stated for the record). -/
theorem reverse_width {α : Type} {width : Nat} (w : Word α width) :
    (reverse w).val.length = width := (reverse w).property

/-- **Involution**: `rev (rev x) = x` and `rbit (rbit x) = x`. -/
theorem reverse_involutive {α : Type} {width : Nat} (w : Word α width) :
    reverse (reverse w) = w := by
  apply Subtype.ext
  simp [reverse]

/-- **Nothing is invented or dropped**: reversal is a permutation of the
    original lanes. -/
theorem reverse_perm {α : Type} {width : Nat} (w : Word α width) :
    (reverse w).val.Perm w.val := List.reverse_perm w.val

/-- `CLZ` over the most-significant-first bit view: count the leading
    `false` lanes. Total by construction. -/
def clz : List Bool → Nat
  | [] => 0
  | true :: _ => 0
  | false :: rest => clz rest + 1

/-- **Bounded by the width**: `clz x ≤ width`, so narrowing the result
    into the operand's own type is lossless. -/
theorem clz_le_width (bits : List Bool) : clz bits ≤ bits.length := by
  induction bits with
  | nil => simp [clz]
  | cons b rest ih =>
    cases b with
    | true => simp [clz]
    | false =>
      show clz rest + 1 ≤ rest.length + 1
      exact Nat.succ_le_succ ih

/-- **The zero word saturates**: `clz 0 = width` — the ARM semantics the
    portable lowering's guard supplies. -/
theorem clz_zero (width : Nat) :
    clz (List.replicate width false) = width := by
  induction width with
  | zero => simp [clz]
  | succ n ih => simp [List.replicate, clz, ih]

/-- **A set leading bit means zero leading zeros.** -/
theorem clz_leading_one (rest : List Bool) : clz (true :: rest) = 0 := rfl

/-- **Exactness**: only the zero word saturates — any `true` lane keeps
    `clz` strictly below the width. -/
theorem clz_lt_of_mem_true (bits : List Bool) (h : true ∈ bits) :
    clz bits < bits.length := by
  induction bits with
  | nil => cases h
  | cons b rest ih =>
    cases b with
    | true =>
      show 0 < rest.length + 1
      exact Nat.succ_pos rest.length
    | false =>
      have hrest : true ∈ rest := by
        cases List.mem_cons.mp h with
        | inl heq => exact absurd heq (by decide)
        | inr hmem => exact hmem
      have := ih hrest
      show clz rest + 1 < rest.length + 1
      exact Nat.succ_lt_succ this

end Oak.Intrinsics
