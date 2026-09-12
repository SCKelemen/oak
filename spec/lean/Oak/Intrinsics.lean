namespace Oak.Intrinsics

/-! # Abstract assembly intrinsics

Model for `docs/spec/92-ffi.md` §3: the v1 AArch64 instruction functions
`rev` (byte reverse), `rbit` (bit reverse), `clz` (count leading
zeros), and `cnt` (population count). The model works over the value's digits — bytes for `rev`, bits
for `rbit` — as lists of fixed width, which is exactly the register-lane
view the instructions are specified over in the ARM ARM. Laws proven:

- `rev` and `rbit` are width-preserving involutions;
- `clz` is total, bounded by the width, hits the width exactly on the
  zero word, and is zero exactly when the leading bit is set — the ARM
  `CLZ` semantics, including the `CLZ(0) = width` case that C's
  `__builtin_clz` leaves undefined (the backend's guard supplies it);
- `popcount` is total, bounded by the width, zero exactly on the zero
  word, the width on the all-ones word, and complementary under bitwise
  not — the law an allocator's free-bit count over `cnt(~word)` rests on.
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

/-! ## Mask scalars (docs/spec/93-simd.md §1.2)

`ctz` counts trailing zeros — the leading zeros of the reversed word, so
every `clz` law transfers. Total: `ctz` of the zero word is the width, as
`RBIT` then `CLZ` gives. `popcount` below is shared with `arm64.cnt32` /
`arm64.cnt64` (`92-ffi.md` §3.2); `simd.popcount_u32/u64` is its portable
spelling. -/

/-- Trailing zeros of a word written most-significant bit first. -/
def ctz (bits : List Bool) : Nat := clz bits.reverse

theorem ctz_le_width (bits : List Bool) : ctz bits ≤ bits.length := by
  unfold ctz
  have h := clz_le_width bits.reverse
  simpa [List.length_reverse] using h

/-- **The zero word saturates**: `ctz 0 = width`. -/
theorem ctz_zero (width : Nat) : ctz (List.replicate width false) = width := by
  unfold ctz
  rw [List.reverse_replicate]
  exact clz_zero width

/-- A set bit somewhere keeps `ctz` strictly below the width, so the
mask-iteration loop `m &= m - 1` makes progress. -/
theorem ctz_lt_of_mem_true (bits : List Bool) (h : true ∈ bits) : ctz bits < bits.length := by
  unfold ctz
  have h' : true ∈ bits.reverse := List.mem_reverse.mpr h
  have := clz_lt_of_mem_true bits.reverse h'
  simpa [List.length_reverse] using this

/-- `CNT` (summed over the lanes by `ADDV`): the number of `true` bits.
    Total by construction. -/
def popcount : List Bool → Nat
  | [] => 0
  | true :: rest => popcount rest + 1
  | false :: rest => popcount rest

/-- **Bounded by the width**: `popcount x ≤ width`, so the result fits the
    operand's own type. -/
theorem popcount_le_width (bits : List Bool) : popcount bits ≤ bits.length := by
  induction bits with
  | nil => simp [popcount]
  | cons b rest ih =>
    cases b with
    | true =>
      show popcount rest + 1 ≤ rest.length + 1
      exact Nat.succ_le_succ ih
    | false =>
      show popcount rest ≤ rest.length + 1
      exact Nat.le_succ_of_le ih

/-- **The zero word counts zero.** -/
theorem popcount_zero (width : Nat) :
    popcount (List.replicate width false) = 0 := by
  induction width with
  | zero => simp [popcount]
  | succ n ih => simp [List.replicate, popcount, ih]

/-- **The all-ones word counts the width.** -/
theorem popcount_ones (width : Nat) :
    popcount (List.replicate width true) = width := by
  induction width with
  | zero => simp [popcount]
  | succ n ih => simp [List.replicate, popcount, ih]

/-- **Complement**: the set bits of `~w` and of `w` partition the width —
    a free-bit count is `cnt(~word)`, and it equals `width - cnt(word)`. -/
theorem popcount_not (bits : List Bool) :
    popcount (bits.map not) + popcount bits = bits.length := by
  induction bits with
  | nil => simp [popcount]
  | cons b rest ih =>
    cases b with
    | true =>
      show popcount (rest.map not) + (popcount rest + 1) = rest.length + 1
      omega
    | false =>
      show popcount (rest.map not) + 1 + popcount rest = rest.length + 1
      omega

/-- **Zero iff no bit is set** — the mask loop's termination test,
`popcount m = 0 ↔ m = 0`. -/
theorem popcount_eq_zero_iff (bits : List Bool) : popcount bits = 0 ↔ true ∉ bits := by
  induction bits with
  | nil => simp [popcount]
  | cons b rest ih =>
    cases b with
    | true => simp [popcount]
    | false => simp [popcount, ih]

end Oak.Intrinsics
