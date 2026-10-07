import Oak.Stdlib.TimeComponentLaws
/-! # Arithmetic invariants of the ISO numeric scanners
All arithmetic and byte-range facts in this module are kernel checked.
These are scanner safety contracts; exact text-value correspondence and
sufficient-fuel termination are separate obligations.
-/
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000
private theorem parsed_digit_bound (b : UInt8) (fuel : Nat)
    (h : is_digit b fuel = some true) : (b-48).toUInt64.toNat ≤ 9 := by
  simp only [is_digit, pure, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [UInt8.toNat_toUInt64, UInt8.toNat_sub_of_le b 48 h.1]
  have hb := UInt8.le_iff_toNat_le.mp h.2
  change b.toNat ≤ 57 at hb
  change b.toNat-48 ≤ 9
  omega

/-- The fraction scanner reserves ten times the remaining decimal scale;
    every accepted digit keeps the partial fraction strictly below one second. -/
def iso_fraction_bounds (fraction scale : UInt64) : Prop :=
  fraction.toNat < 1000000000 ∧ fraction.toNat + scale.toNat*10 ≤ 1000000000

theorem iso_fraction_step_exact (fraction scale digit : UInt64)
    (h : iso_fraction_bounds fraction scale) (hd : digit.toNat ≤ 9) :
    (fraction+digit*scale).toNat = fraction.toNat+digit.toNat*scale.toNat ∧
    iso_fraction_bounds (fraction+digit*scale) (scale/10) := by
  have hp := Nat.mul_le_mul_right scale.toNat hd
  have hs := Nat.mod_add_div scale.toNat 10
  have hf : fraction.toNat+digit.toNat*scale.toNat ≤ (1000000000 : UInt64).toNat := by
    change fraction.toNat+digit.toNat*scale.toNat ≤ 1000000000
    dsimp [iso_fraction_bounds] at h
    omega
  have he := component_sum_exact fraction digit scale 0 1000000000 (by simpa using hf)
  simp only [UInt64.add_zero, UInt64.toNat_zero, Nat.add_zero] at he
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    dsimp [iso_fraction_bounds] at h
    by_cases hz : scale.toNat = 0
    · simp only [hz, Nat.mul_zero, Nat.add_zero]
      exact h.1
    · omega
  · rw [he, UInt64.toNat_div]
    change fraction.toNat+digit.toNat*scale.toNat + scale.toNat/10*10 ≤ 1000000000
    dsimp [iso_fraction_bounds] at h
    omega

theorem parse_iso_fraction_loop_bounds (src : Array UInt8) (n : UInt32) (fuel : Nat) :
    ∀ (at_ : UInt32) (fraction : UInt64) (digits : UInt32) (scale : UInt64)
      (out : UInt32 × UInt64 × UInt32 × UInt64),
      iso_fraction_bounds fraction scale → digits ≤ 9 →
      parse_iso_components.loop3 src n at_ fraction digits scale fuel = some out →
      iso_fraction_bounds out.2.1 out.2.2.2 ∧ out.2.2.1 ≤ 9 := by
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro at_ fraction digits scale out hb hd h
    unfold parse_iso_components.loop3 at h
    simp only [bind, Option.bind_eq_some_iff] at h
    rcases h with ⟨digit, hg, h⟩
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hdb := parsed_digit_bound (src.getD at_.toNat 0) fuel (by simpa [hc.1.2] using hg)
      have hnext : digits+1 ≤ (9 : UInt32) := by
        have hlt := UInt32.lt_iff_toNat_lt.mp hc.2
        change digits.toNat < 9 at hlt
        rw [UInt32.le_iff_toNat_le, UInt32.toNat_add]
        change (digits.toNat+1)%4294967296 ≤ 9
        omega
      exact ih (at_+1) _ _ _ out (iso_fraction_step_exact fraction scale _ hb hdb).2 hnext h
    · simp only [pure, Option.some.injEq] at h
      subst out
      exact ⟨hb, hd⟩

/-- The actual initial fraction state satisfies the invariant; every returning
scan therefore yields at most nine digits and a fraction below one second. -/
theorem parse_iso_fraction_bounded (src : Array UInt8) (n at_ : UInt32) (fuel : Nat)
    (out : UInt32 × UInt64 × UInt32 × UInt64)
    (h : parse_iso_components.loop3 src n at_ 0 0 100000000 fuel = some out) :
    out.2.1.toNat < 1000000000 ∧ out.2.2.1 ≤ 9 := by
  have hb := parse_iso_fraction_loop_bounds src n fuel at_ 0 0 100000000 out
    (by constructor <;> decide) (by decide) h
  exact ⟨hb.1.1, hb.2⟩
/-- The actual integer scanner never decreases its accumulator. Each accepted
base-ten extension uses exact arithmetic, and an overflow flag remains set. -/
theorem parse_iso_integer_loop_monotone (src : Array UInt8) (n : UInt32) (fuel : Nat) :
    ∀ (at_ : UInt32) (overflow : Bool) (value : UInt64) (out : UInt32 × Bool × UInt64),
      parse_iso_components.loop2 src n at_ overflow value fuel = some out →
      value.toNat ≤ out.2.2.toNat ∧ (overflow = true → out.2.1 = true) := by
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro at_ overflow value out h
    unfold parse_iso_components.loop2 at h
    simp only [bind, Option.bind_eq_some_iff] at h
    rcases h with ⟨digit, _, h⟩
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      simp only [Option.bind_eq_some_iff] at h
      rcases h with ⟨over, hg, next, hn, h⟩
      cases over with
      | false =>
        simp only [Bool.not_false, ite_true, pure, Option.some.injEq] at hn
        subst next
        have hb := ih (at_+1) false _ out h
        have he := iso_decimal_accept_exact value _ fuel hg
        refine ⟨?_, ?_⟩
        · rw [he] at hb
          omega
        · simp [hc.2]
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, pure, Option.some.injEq] at hn
        subst next
        have hb := ih (at_+1) true value out h
        exact ⟨hb.1, fun _ => hb.2 rfl⟩
    · simp only [pure, Option.some.injEq] at h
      subst out
      exact ⟨Nat.le_refl _, fun h => h⟩
end Oak.Stdlib.Time
