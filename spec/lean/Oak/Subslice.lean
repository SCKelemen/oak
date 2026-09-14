/-!
# The derived span

Model for docs/spec/94-assembler.md §9 (subslice on the rv64 lane; the
AArch64 checker's derived-span idiom). `subslice(v, start, n)` is admitted
under two guards — `start ≤ len` and `n ≤ len - start` — and derives the
span at `base + start·elem` of length `n`. The checker's later element
guards compare an index against `n`; the theorem: every such index names an
element of the original span, so the derived span's accesses stay inside
the memory the original owns. The registers hold zero-extended `u32`
values, so the arithmetic is exact in `Nat`; and a count the second guard
admits is at most `len - start`, hence below `2^32` — the reason the count
register is its own normalized length.
-/

namespace Oak.Subslice

/-- **Derived index in bounds**: under the two guards, `start + i < len`
    for every `i < n`. -/
theorem derived_index_in_bounds (len start n i : Nat)
    (hstart : start ≤ len) (hn : n ≤ len - start) (hi : i < n) : start + i < len := by
  omega

/-- The derived element's bytes lie inside the original span's bytes:
    `(start + i) * elem + elem ≤ len * elem`. -/
theorem derived_element_bytes (len start n i elem : Nat)
    (hstart : start ≤ len) (hn : n ≤ len - start) (hi : i < n) :
    (start + i) * elem + elem ≤ len * elem := by
  have h : start + i + 1 ≤ len := derived_index_in_bounds len start n i hstart hn hi
  have : (start + i + 1) * elem ≤ len * elem := Nat.mul_le_mul_right elem h
  have e : (start + i + 1) * elem = (start + i) * elem + elem := Nat.succ_mul _ _
  omega

/-- **The count is normalized**: a count the guard admits is at most the
    normalized length, itself below `2^32`. -/
theorem count_below_width (len start n : Nat) (hlen : len < 2 ^ 32)
    (hstart : start ≤ len) (hn : n ≤ len - start) : n < 2 ^ 32 := by
  omega

/-- A re-slice of a derived span is a slice of the original: the guards
    compose. -/
theorem reslice_in_bounds (len start n start' n' i : Nat)
    (h1 : start ≤ len) (h2 : n ≤ len - start)
    (h3 : start' ≤ n) (h4 : n' ≤ n - start') (hi : i < n') :
    start + (start' + i) < len := by
  omega

end Oak.Subslice

namespace Oak.Subslice

/-- **Alias translation composes**: a re-slice's offset into the root is
    the outer start plus the inner, so the translated index of a re-sliced
    alias is `(start + start') + i`, the root's element for the inner
    alias's `start' + i` (the verifier's spanIndex applied twice). -/
theorem alias_offset_assoc (start start' i : Nat) :
    (start + start') + i = start + (start' + i) := by
  omega

/-- **The translated length**: an alias's `len` is its count, not the
    root's length, and every count the guards admit fits the root:
    `start + n ≤ len`. -/
theorem alias_len_fits (len start n : Nat) (hstart : start ≤ len) (hn : n ≤ len - start) :
    start + n ≤ len := by
  omega

end Oak.Subslice
