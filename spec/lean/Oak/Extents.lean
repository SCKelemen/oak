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

end Oak.Extents
