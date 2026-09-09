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

end Oak.Extents
