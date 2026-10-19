import Oak.CNFTypedNode

/-!
# Exact vector replay from individually checked bits

The supplied index list must equal the complete range. Each member carries
the original scalar replay equation, and the root length is checked exactly.
This theorem composes those facts into the existing Boolean checker result.
-/

set_option autoImplicit false

namespace Oak.CNFTypedNode

theorem checkVector_of_bitList
    {snapshot : Snapshot} {maxInt width : Nat}
    {circuits : Oak.CNFTypedCircuit.Bits} {roots bits : List Nat}
    (length : roots.length = width)
    (coverage : bits = List.range width)
    (replayed : ∀ bit, bit ∈ bits →
      Oak.CNFTypedCircuit.replayCircuit snapshot maxInt (circuits bit) =
        some (roots.getD bit 0)) :
    checkVector snapshot maxInt width circuits roots = true := by
  rw [coverage] at replayed
  simp only [checkVector, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨length, replayed⟩

end Oak.CNFTypedNode

#print axioms Oak.CNFTypedNode.checkVector_of_bitList
