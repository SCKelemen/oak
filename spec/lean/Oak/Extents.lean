/-!
# Extent facts: the discharge laws of bounds-check elision

`typechecker/extents.go` (roadmap milestone 8, first increment). A runtime
check the program performs establishes a fact for the scope it dominates;
an element access inside that scope is proven in range by one of three
laws, and the backend emits it unchecked. Everything else stays checked.
The laws are stated over the runtime length `len`, which the fact
constrains but never fixes.
-/

namespace Oak.Extents

/-- A constant index below a min-length bound is in range for every
    length the fact admits: from `K ≤ len` and `c < K`, `c < len`
    (`recordIndexProof`, factMinLen). -/
theorem constant_under_min_length (c K len : Nat) (hfact : K ≤ len) (hc : c < K) :
    c < len := Nat.lt_of_lt_of_le hc hfact

/-- An index bound transfers across a same-length fact: from `i < len a` and
    `len a = len b`, `i < len b` (factIndexBound with factSameLen). -/
theorem bound_transfers (i lenA lenB : Nat) (hbound : i < lenA) (hsame : lenA = lenB) :
    i < lenB := hsame ▸ hbound

/-- A constant index below a static extent is in range: an owned array
    `[N]T` has exactly `N` elements (`recordIndexProof`, static case). -/
theorem static_extent (c N : Nat) (hc : c < N) : c < N := hc

/-- The loop law: the condition `i < len v` is re-established on every
    iteration, and a body that changes `i` only as its final statement sees
    the bound at every access before it — stated as the invariant the
    checker's syntactic restriction (`assignsAny` with the trailing
    increment excepted) guarantees: every access in the body executes under
    the most recent evaluation of the condition. -/
theorem loop_invariant (i len : Nat) (hcond : i < len) : i < len := hcond

/-- Facts never widen: adding a fact to the scope stack cannot un-prove an
    access; popping restores exactly the enclosing facts (list prefix). -/
theorem facts_monotone {α : Type} (stack extra : List α) :
    (stack ++ extra).take stack.length = stack := by
  simp

/-- An offset bound covers every smaller offset: from `i + K < len` and
    `j ≤ K`, `i + j < len` (`recordIndexProof` with `offsetIndex`). -/
theorem offset_under_bound (i K j len : Nat) (hbound : i + K < len) (hj : j ≤ K) :
    i + j < len := by omega

/-- The wrap-free offset guard: with `K ≤ len` known, `i < len - K` is exactly
    `i + K < len`, so the guard establishes an offset bound of `K`
    (`factsFromCondition`, `i < len(v) - K`). The subtraction cannot wrap
    because `K ≤ len`; the checker never derives an offset bound from
    `i + K < len`, whose fixed-width sum may have wrapped. -/
theorem guard_without_wrap (i K len : Nat) (hK : K ≤ len) (h : i < len - K) :
    i + K < len := by omega

/-- The inclusive spelling: with `1 ≤ K ≤ len`, `i ≤ len - K` establishes an
    offset bound of `K - 1` (`factsFromCondition`, `i <= len(v) - K`). -/
theorem inclusive_guard_without_wrap (i K len : Nat) (hK : K ≤ len) (hpos : 1 ≤ K)
    (h : i ≤ len - K) : i + (K - 1) < len := by omega

/-- Flow-sensitive kill: a fact established before an assignment says nothing
    about the assigned binding afterwards, and stating the proof obligation
    for an access as `index value at the access < len` makes the kill the
    conservative choice — the law an unkilled fact would need, `i' = i`, is
    exactly what the assignment breaks. -/
theorem kill_is_conservative (i i' len : Nat) (hfact : i < len) (hsame : i' = i) :
    i' < len := hsame ▸ hfact

/-- Bounds compose through a binding: from `i < n` and `n ≤ len`, `i < len`
    (`resolveIndexPairs`, factUpperBound with an `i < n` guard). -/
theorem bound_through_upper (i n len : Nat) (hi : i < n) (hn : n ≤ len) : i < len :=
  Nat.lt_of_lt_of_le hi hn

/-- A Bool binding stands for the condition assigned to it: if `valid` is
    `true` and `valid` was assigned `c`, then `c` held when it was assigned
    (`boolBindingFacts`); strengthening `valid = valid && c'` keeps `c` and
    adds `c'`. -/
theorem bool_binding_condition (valid c : Prop) (hassign : valid ↔ c) (h : valid) : c :=
  hassign.mp h

theorem bool_binding_strengthens (old c : Prop) (h : old ∧ c) : old ∧ c := h

/-- `subslice(v, start, n)` has exactly `n` elements once its bounds-checked
    construction succeeds (`start + n ≤ len`), so a constant below `n`
    addresses an element of the parent as well; the slice form `v[lo:hi]`
    is the instance `start = lo`, `n = hi - lo`. -/
theorem subslice_extent (start n len c : Nat) (hfits : start + n ≤ len)
    (hc : c < n) : start + c < len := by omega

/-- The construction check never overflows: `start ≤ len ∧ n ≤ len - start`
    is exactly `start + n ≤ len` (the helper compares without adding). -/
theorem subslice_check_iff (start n len : Nat) :
    (start ≤ len ∧ n ≤ len - start) ↔ start + n ≤ len := by omega


/-- A literal upper bound composes with a known length: from `i < K` and
    `K ≤ len`, `i < len`; with an offset, from `i < K` and `K + j ≤ len`,
    `i + j < len` (`recordIndexProof`, factIndexLit). -/
theorem literal_bound_under_length (i K j len : Nat) (hi : i < K) (hlen : K + j ≤ len) :
    i + j < len := by omega

/-- Subtracting a literal under a lower and an upper bound: from `L ≤ i`,
    `K ≤ L`, `i < U`, and `U - K ≤ len`, `i - K < len`, and the subtraction
    does not wrap because `K ≤ i` (`recordIndexProof`, `minusIndex` with
    factLowerLit and factIndexLit). -/
theorem subtraction_under_bounds (i K L U len : Nat) (hL : L ≤ i) (hK : K ≤ L) (hU : i < U)
    (hlen : U - K ≤ len) : i - K < len := by omega

/-- The same with the upper bound a length: from `K ≤ i` and `i < len`,
    `i - K < len`. -/
theorem subtraction_under_length (i K len : Nat) (hK : K ≤ i) (hi : i < len) : i - K < len := by
  omega

/-- A scaled index under a literal bound: from `i < U` (so `1 ≤ U`) and
    `(U - 1) * K + j < len`, `i * K + j < len` (`recordIndexProof`,
    `scaledIndex`). The product cannot wrap when the length fits the machine
    word, because it is bounded by the length. -/
theorem scaled_under_bound (i K j U len : Nat) (hi : i < U) (hlen : (U - 1) * K + j < len) :
    i * K + j < len := by
  have hle : i ≤ U - 1 := by omega
  have := Nat.mul_le_mul_right K hle
  omega

/-- A masked index is below every length above the mask: from `M < len`,
    `x &&& M < len`, for any `x` (`recordIndexProof`, `maskedIndex`). -/
theorem masked_under_length (x M len : Nat) (hM : M < len) : x &&& M < len :=
  Nat.lt_of_le_of_lt (Nat.and_le_right) hM

/-- The mask survives an unsigned truncation: `(x &&& M) % 2^w ≤ x &&& M`
    (`valuePreservingBound`, `u32_trunc_u64(e & M)`). -/
theorem masked_trunc_under_length (x M w len : Nat) (hM : M < len) :
    (x &&& M) % 2 ^ w < len :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mod_le _ _) Nat.and_le_right) hM

/-- And an unsigned saturation: `min (x &&& M) B ≤ x &&& M`
    (`valuePreservingBound`, `u32_saturating_u64(e & M)`). -/
theorem masked_saturating_under_length (x M B len : Nat) (hM : M < len) :
    min (x &&& M) B < len :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.min_le_left _ _) Nat.and_le_right) hM

/-- Leaving a loop `while i < K` normally means `K ≤ i`
    (`checkWhileStatement`, the exit fact; a body with `break` gets none). -/
theorem loop_exit_lower_bound (i K : Nat) (h : ¬ i < K) : K ≤ i := Nat.le_of_not_lt h

/-- A lower bound survives the canonical increment when an upper bound
    keeps the sum below the word: from `K0 ≤ i`, `K0 ≤ i + c`; and with
    `i < U` and `U + c ≤ 2^w` the fixed-width sum is the natural one
    (`checkWhileStatement`, the exception that keeps factLowerLit alive
    through a loop whose only write to `i` is the trailing increment). -/
theorem increment_keeps_lower_bound (i c K0 : Nat) (h : K0 ≤ i) : K0 ≤ i + c := by omega

/-- A vector access covers `L` lanes from its index. Under a min-length
    fact `K ≤ len`, a constant index `c` with `c + L ≤ K` keeps every lane
    `c + k`, `k < L`, in range (`recordVectorAccessProof`, constant index). -/
theorem vector_under_min_length (c L k K len : Nat) (hfact : K ≤ len) (hc : c + L ≤ K)
    (hk : k < L) : c + k < len := by omega

/-- Under an offset bound `i + K < len`, the lanes `i + j + k`, `k < L`, are
    in range whenever `j + L - 1 ≤ K` — the sixty-four-byte step of
    `utf8.valid`, four loads at `off`, `off + 16`, `off + 32`, `off + 48`
    under `off <= len(bytes) - 64` (`recordVectorAccessProof`, offset index). -/
theorem vector_under_offset_bound (i K j L k len : Nat) (hbound : i + K < len)
    (hL : 1 ≤ L) (hj : j + L - 1 ≤ K) (hk : k < L) : i + j + k < len := by omega

/-- Under a literal bound `i < U` and a length of at least `U - 1 + j + L`,
    the lanes `i + j + k`, `k < L`, are in range
    (`recordVectorAccessProof`, literal bound). -/
theorem vector_under_literal_bound (i U j L k len : Nat) (hi : i < U)
    (hlen : U - 1 + j + L ≤ len) (hk : k < L) : i + j + k < len := by omega

theorem increment_without_wrap (i c U w : Nat) (hi : i < U) (hU : U + c ≤ 2 ^ w) :
    i + c < 2 ^ w := by omega

/-- **Midpoint**: under `a < b`, `a + (b - a) / k` is below `b` for every
    `k ≥ 2` — and the subtraction and the sum are the natural ones, since
    `a < b` keeps both inside the word (`declarationFacts`, the midpoint
    rule of a binary search; `k = 2` is `lo + (hi - lo) / 2`). -/
theorem midpoint_under_bound (a b k : Nat) (hab : a < b) (hk : 2 ≤ k) :
    a + (b - a) / k < b := by
  have h : (b - a) / k < b - a := Nat.div_lt_self (by omega) (by omega)
  omega

/-- **Through the midpoint to a length**: with `b ≤ len` besides,
    `a + (b - a) / k < len` — the composition the declaration's fact
    records directly (`factIndexBound` through `b`). -/
theorem midpoint_under_length (a b k len : Nat) (hab : a < b) (hk : 2 ≤ k) (hlen : b ≤ len) :
    a + (b - a) / k < len :=
  Nat.lt_of_lt_of_le (midpoint_under_bound a b k hab hk) hlen

/-- **A decreasing write keeps an upper bound**: from `m < x` and `x ≤ n`,
    the new value `m` is still at most `n`; and below a literal `B`
    likewise (`checkWhileStatement`, upperBoundsSurviving: a loop whose
    only writes to `x` are `x = m` with `m` the midpoint under `a < x`). -/
theorem decreasing_keeps_upper_bound (m x n : Nat) (hm : m < x) (hx : x ≤ n) : m ≤ n := by omega

theorem decreasing_keeps_literal_bound (m x B : Nat) (hm : m < x) (hx : x < B) : m < B := by omega

/-- **Quotient bound, scaled**: under `i < n / K` (the page count of a
    view of `n` keys, `K` keys per page), `i * K + j < n` for every
    `j < K` — the fence key of page `i` and every key of the page
    (`declarationFacts`, `pages = len(v) / K`; `indexUnder`, factDivIndex). -/
theorem div_bound_scaled (i j n K : Nat) (hi : i < n / K) (hj : j < K) :
    i * K + j < n := by
  have hK : 0 < K := by omega
  have h : (i + 1) * K ≤ n := (Nat.le_div_iff_mul_le hK).mp hi
  rw [Nat.succ_mul] at h
  omega

/-- **Quotient bound, plain**: the same premise puts `i + j` below `n`
    as well, since `i ≤ i * K`. -/
theorem div_bound_under_length (i j n K : Nat) (hi : i < n / K) (hj : j < K) :
    i + j < n := by
  have h := div_bound_scaled i j n K hi hj
  have hK : 0 < K := by omega
  have : i ≤ i * K := Nat.le_mul_of_pos_right i hK
  omega

end Oak.Extents
