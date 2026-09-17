import Oak.BlockedFill

/-!
# Pair-store write-log effects

This module connects the verifier's prospective logical expansion of one
64-bit register-pair store to the total word-memory model used by
`Oak.PairCopies` and `Oak.BlockedFill`. A pair contributes exactly two
32-bit-modular logical write-log entries in operand/address order; under an
explicit no-wrap premise, applying those entries has the same final memory as
`storePair`, and two adjacent zero pairs have the same final memory as four
scalar stores.

This is final-state algebra only. It does not prove that an architectural
request occurs, architectural or observer order between pair components,
atomicity, non-tearing, byte-address conversion or wrap freedom, bounds,
32-bit verifier-index wrap freedom, alignment, traps or faults, translation,
endianness, memory type, Arm ASL
`Mem` execution, CAT events, visibility, completion, or publication.
-/

namespace Oak.PairStoreEffects

open Oak.PairCopies Oak.BlockedFill

/-- One unguarded logical word write. Addresses count eight-byte words. -/
structure WordWrite where
  index : Nat
  value : Nat
  deriving Repr, DecidableEq

/-- Apply a verifier-style append-order log to total word memory. -/
def applyWrites : Mem → List WordWrite → Mem
  | m, [] => m
  | m, write :: rest => applyWrites (store m write.index write.value) rest

/-- The verifier's span indices are 32-bit terms. -/
def indexModulus : Nat := 2 ^ 32

/-- The two logical entries staged for `STP Xfirst, Xsecond, [base]`, with
the verifier's exact 32-bit modular index arithmetic. -/
def pair64Writes (dst first second : Nat) : List WordWrite :=
  [⟨dst % indexModulus, first⟩, ⟨(dst + 1) % indexModulus, second⟩]

/-- Two adjacent pairs covering one four-word blocked-fill iteration. -/
def block4Writes (dst value : Nat) : List WordWrite :=
  pair64Writes dst value value ++ pair64Writes (dst + 2) value value

/-- Applying the two logical entries is exactly the abstract pair store when
the second 32-bit element index does not wrap. -/
theorem apply_pair64_writes_eq_storePair (m : Mem) (dst first second : Nat)
    (h : dst + 1 < indexModulus) :
    applyWrites m (pair64Writes dst first second) =
      storePair m dst first second := by
  have hdst : dst < indexModulus := by omega
  simp [pair64Writes, applyWrites, Nat.mod_eq_of_lt hdst,
    Nat.mod_eq_of_lt h, storePair]

/-- Applying two adjacent pair logs is exactly one abstract four-word block
when all four 32-bit element indices do not wrap. -/
theorem apply_block4_writes_eq_fillBlock4 (m : Mem) (dst value : Nat)
    (h : dst + 3 < indexModulus) :
    applyWrites m (block4Writes dst value) = fillBlock4 m dst value := by
  have h0 : dst < indexModulus := by omega
  have h1 : dst + 1 < indexModulus := by omega
  have h2 : dst + 2 < indexModulus := by omega
  simp [block4Writes, pair64Writes, applyWrites, Nat.mod_eq_of_lt h0,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h,
    fillBlock4, storePair]

/-- The staged four-entry log has the same final memory as four scalar stores,
under the same no-wrap premise. -/
theorem apply_block4_writes_eq_fillWords_four (m : Mem) (dst value : Nat)
    (h : dst + 3 < indexModulus) :
    applyWrites m (block4Writes dst value) = fillWords m dst value 4 := by
  rw [apply_block4_writes_eq_fillBlock4 m dst value h,
    fillBlock4_eq_fillWords]

/-! Exact examples synchronized from the staged Go helper. -/

example : pair64Writes 7 11 13 = [⟨7, 11⟩, ⟨8, 13⟩] := by decide
example : pair64Writes 4294967295 11 13 = [⟨4294967295, 11⟩, ⟨0, 13⟩] := by decide
example : block4Writes 7 0 = [⟨7, 0⟩, ⟨8, 0⟩, ⟨9, 0⟩, ⟨10, 0⟩] := by decide

end Oak.PairStoreEffects
