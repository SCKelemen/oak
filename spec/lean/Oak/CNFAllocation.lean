import Oak.CNFLayout

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Oak.CNFAllocation
open Oak.CNFEmission Oak.CNFLayout

def requestedWords (cap terms u : UInt32) : Nat :=
  3*cap.toNat+5*u.toNat+16*(stackSlots cap).toNat+
    64*(terms.toNat+1)+3120+6144*terms.toNat+65536

-- The widened production arithmetic is exact for every u32 input.
theorem words_exact (cap terms u : UInt32) (fuel : Nat) :
    ∃ w, cnf_allocation_words cap terms u fuel = some w ∧
      w.toNat = requestedWords cap terms u := by
  simp only [cnf_allocation_words, Option.pure_def]
  refine ⟨_,rfl,?_⟩
  change (((cap.toUInt64*3+u.toUInt64*5+(stackSlots cap).toUInt64*16+
    (terms.toUInt64+1)*64+3120+terms.toUInt64*6144)+65536).toNat = _)
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hc := cap.toNat_lt
  have ht := terms.toNat_lt
  have hu := u.toNat_lt
  have hs := (stackSlots cap).toNat_lt
  unfold requestedWords
  change (((((((cap.toNat*3)%18446744073709551616+(u.toNat*5)%18446744073709551616)%18446744073709551616+
    ((stackSlots cap).toNat*16)%18446744073709551616)%18446744073709551616+
    (((terms.toNat+1)%18446744073709551616)*64)%18446744073709551616)%18446744073709551616+
    3120)%18446744073709551616+(terms.toNat*6144)%18446744073709551616)%18446744073709551616+
    65536)%18446744073709551616 = _
  omega

theorem refuses_large_cap (cap terms : UInt32) (fuel : Nat)
    (large : 1073741824 < cap.toNat) : cnf_allocation_fits cap terms fuel = some false := by
  have h : cap > (1073741824 : UInt32) := by change (1073741824 : UInt32) < cap; rw [UInt32.lt_iff_toNat_lt]; exact large
  simp [cnf_allocation_fits, h]

-- A successful guard exposes a terminating power-of-two computation and a byte-safe budget.
theorem admitted (cap terms : UInt32) (fuel : Nat)
    (ok : cnf_allocation_fits cap terms fuel = some true) :
    cap.toNat ≤ 1073741824 ∧ ∃ u, next_pow2 (cap*2) fuel = some u ∧
      requestedWords cap terms u ≤ 1073741823 := by
  by_cases large : 1073741824 < cap.toNat
  · rw [refuses_large_cap cap terms fuel large] at ok; contradiction
  · have small : cap.toNat ≤ 1073741824 := by omega
    have h : ¬ cap > (1073741824 : UInt32) := by change ¬ (1073741824 : UInt32) < cap; rw [UInt32.lt_iff_toNat_lt]; exact large
    cases pow : next_pow2 (cap*2) fuel with
    | none => simp [cnf_allocation_fits, h, pow] at ok
    | some u =>
      obtain ⟨w,run,exact_⟩ := words_exact cap terms u fuel
      simp only [cnf_allocation_fits, h, decide_false, Bool.false_eq_true, if_false,
        pow, run, Bind.bind, Option.bind, Option.pure_def, Option.some.injEq, decide_eq_true_eq] at ok
      refine ⟨small,u,rfl,?_⟩
      rw [UInt64.le_iff_toNat_le] at ok
      change w.toNat ≤ 1073741823 at ok
      rwa [exact_] at ok

-- Every guard input terminates, including values refused before the doubling loop.
theorem guard_terminates (cap terms : UInt32) : ∃ b, cnf_allocation_fits cap terms 32 = some b := by
  by_cases large : 1073741824 < cap.toNat
  · exact ⟨false, refuses_large_cap cap terms 32 large⟩
  · obtain ⟨u,l,pow,_,_,_,_⟩ := constructor_terminates cap terms 0 (by omega)
    obtain ⟨w,run,_⟩ := words_exact cap terms u 32
    have h : ¬ cap > (1073741824 : UInt32) := by change ¬ (1073741824 : UInt32) < cap; rw [UInt32.lt_iff_toNat_lt]; exact large
    simp [cnf_allocation_fits, h, pow, run]

-- Admission justifies both narrow caller expressions and the earlier layout budget.
theorem admitted_budget (cap terms : UInt32) (fuel : Nat)
    (ok : cnf_allocation_fits cap terms fuel = some true) :
    ∃ u, next_pow2 (cap*2) fuel = some u ∧
      (terms+1).toNat = terms.toNat+1 ∧
      (terms*6144+65536).toNat = terms.toNat*6144+65536 ∧
      footprint cap (terms+1) (terms*6144+65536) u ≤ 1073741823 := by
  obtain ⟨_,u,pow,budget⟩ := admitted cap terms fuel ok
  unfold requestedWords at budget
  have t : (terms+1).toNat = terms.toNat+1 := by
    change (terms.toNat+1)%4294967296 = _; omega
  have c : (terms*6144+65536).toNat = terms.toNat*6144+65536 := by
    change ((terms.toNat*6144)%4294967296+65536)%4294967296 = _; omega
  refine ⟨u,pow,t,c,?_⟩
  unfold footprint
  rw [t,c]
  simpa only [Nat.mul_comm, Nat.add_assoc] using budget

-- The actual constructor result has a safe word total AND a safe malloc byte count.
theorem allocation_safe (cap terms : UInt32) (fuel : Nat) (l : Layout)
    (ok : cnf_allocation_fits cap terms fuel = some true)
    (run : layout_for_clauses cap (terms+1) (terms*6144+65536) fuel = some l) :
    l.total.toNat ≤ 1073741823 ∧ (l.total*4).toNat = l.total.toNat*4 ∧
      l.bits_at.toNat+(terms+1).toNat*64+3104+16+(terms*6144+65536).toNat < 4294967296 := by
  obtain ⟨u,pow,_,_,budget⟩ := admitted_budget cap terms fuel ok
  have regions := complete_regions cap (terms+1) (terms*6144+65536) u fuel l pow run (by omega)
  have suffix := suffix_budget cap (terms+1) (terms*6144+65536) u fuel l pow run (by omega)
  have total := regions.2.2.2.2.2.2.2.2.2.2
  refine ⟨by omega,?_,suffix⟩
  change (l.total.toNat*4)%4294967296 = _
  omega

end Oak.CNFAllocation
