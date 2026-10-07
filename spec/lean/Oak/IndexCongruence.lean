import Std

/-!
# Word-level index disjointness

The alias shortcut cancels common linear coefficients modulo 2^width.
Every remaining coefficient is a multiple of 2^shift. If the residual
constant is not divisible by 2^shift, the residual cannot be zero, even
when the word arithmetic wraps. These are arithmetic laws; the Go linear
normalizer and trailing-zero calculation are additionally regression-tested,
not claimed to be implementation-refined by this module.
-/
namespace Oak.IndexCongruence

def evalTerms : List (Nat × Nat) → Nat
  | [] => 0
  | (coefficient, value) :: rest => coefficient * value + evalTerms rest

theorem terms_mod_zero (d : Nat) (terms : List (Nat × Nat))
    (h : ∀ term ∈ terms, term.1 % d = 0) : evalTerms terms % d = 0 := by
  induction terms with
  | nil => simp [evalTerms]
  | cons head tail ih =>
    have hh : head.1 % d = 0 := h head (by simp)
    have ht : evalTerms tail % d = 0 := ih (by
      intro term member
      exact h term (by simp [member]))
    simp [evalTerms, Nat.add_mod, Nat.mul_mod, hh, ht]

/-- Taking a machine word modulo 2^width preserves every lower residue. -/
theorem wrapped_residue (d modulus constant : Nat) (terms : List (Nat × Nat))
    (divides : d ∣ modulus) (h : ∀ term ∈ terms, term.1 % d = 0) :
    ((evalTerms terms + constant) % modulus) % d = constant % d := by
  rw [Nat.mod_mod_of_dvd _ divides, Nat.add_mod, terms_mod_zero d terms h]
  simp

/-- A nonzero residual residue rules out aliasing under wrapped arithmetic. -/
theorem residual_nonzero (d modulus constant : Nat) (terms : List (Nat × Nat))
    (divides : d ∣ modulus) (h : ∀ term ∈ terms, term.1 % d = 0)
    (different : constant % d ≠ 0) :
    (evalTerms terms + constant) % modulus ≠ 0 := by
  intro zero
  have residue := wrapped_residue d modulus constant terms divides h
  rw [zero] at residue
  exact different residue.symm

end Oak.IndexCongruence
