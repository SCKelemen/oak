import Oak.CNFAllocation

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Oak.SolverAllocation
open Oak.CNFEmission Oak.CNFLayout

def bddWords (cap terms u variants : UInt32) : Nat :=
  3*cap.toNat+5*u.toNat+16*(stackSlots cap).toNat+64*terms.toNat+3120+
    (if variants > 1 then 32768 else 0)

def satWords (vars clauses store record : UInt32) : Nat :=
  23*(vars.toNat+1)+10*clauses.toNat+3*store.toNat+record.toNat+50

theorem bdd_words_exact (cap terms u variants : UInt32) (fuel : Nat) :
    ∃ w, bdd_allocation_words cap terms u variants fuel = some w ∧ w.toNat = bddWords cap terms u variants := by
  simp only [bdd_allocation_words, Option.pure_def]
  refine ⟨_,rfl,?_⟩
  have hc := cap.toNat_lt
  have ht := terms.toNat_lt
  have hu := u.toNat_lt
  have hs := (stackSlots cap).toNat_lt
  change (cap.toUInt64*3+u.toUInt64*5+(stackSlots cap).toUInt64*16+terms.toUInt64*64+3120+
    (if decide (variants > 1) then (32768 : UInt32) else 0).toUInt64).toNat = _
  unfold bddWords
  split <;> simp_all only [if_false, decide_eq_true_eq,
    if_pos, UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64]
  all_goals simp only [UInt32.toNat_ofNat, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
  all_goals omega

theorem sat_words_exact (vars clauses store record : UInt32) (fuel : Nat) :
    ∃ w, sat_allocation_words vars clauses store record fuel = some w ∧ w.toNat = satWords vars clauses store record := by
  simp only [sat_allocation_words, Option.pure_def]
  refine ⟨_,rfl,?_⟩
  have hv := vars.toNat_lt
  have hc := clauses.toNat_lt
  have hs := store.toNat_lt
  have hr := record.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64]
  unfold satWords
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem sat_admitted (vars clauses store record : UInt32) (fuel : Nat) :
    sat_allocation_fits vars clauses store record fuel = some true ↔ satWords vars clauses store record ≤ 1073741823 := by
  obtain ⟨w,run,exact_⟩ := sat_words_exact vars clauses store record fuel
  simp only [sat_allocation_fits, run, Bind.bind, Option.bind, Option.pure_def,
    Option.some.injEq, decide_eq_true_eq, UInt64.le_iff_toNat_le, exact_]
  rfl

theorem capacity_admitted (clauses literals : UInt32) (fuel : Nat)
    (ok : sat_capacity_fits clauses literals fuel = some true) :
    (8*clauses+65536).toNat = 8*clauses.toNat+65536 ∧
      (64*literals+1048576).toNat = 64*literals.toNat+1048576 ∧
      (8+literals).toNat = 8+literals.toNat := by
  have hc := clauses.toNat_lt
  have hl := literals.toNat_lt
  simp only [sat_capacity_fits, Option.pure_def, Option.some.injEq, Bool.and_eq_true,
    decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mul,
    UInt32.toNat_toUInt64] at ok
  simp only [UInt32.toNat_add, UInt32.toNat_mul]
  simp only [UInt32.toNat_ofNat, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
  omega

theorem bdd_admitted (cap terms variants : UInt32) (fuel : Nat)
    (ok : bdd_allocation_fits cap terms variants fuel = some true) :
    cap.toNat ≤ 1073741824 ∧ 1 ≤ variants.toNat ∧ variants.toNat ≤ 3 ∧
      ∃ u, next_pow2 (cap*2) fuel = some u ∧ bddWords cap terms u variants ≤ 1073741823 := by
  unfold bdd_allocation_fits at ok
  split at ok
  · simp at ok
  · rename_i bounds
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at bounds
    have capBound : cap.toNat ≤ 1073741824 := by
      have h := bounds.1.1; change ¬ (1073741824 : UInt32) < cap at h
      rw [UInt32.lt_iff_toNat_lt] at h; change ¬ 1073741824 < cap.toNat at h; omega
    have vBound : 1 ≤ variants.toNat ∧ variants.toNat ≤ 3 := by
      have lo := bounds.1.2; have hi := bounds.2
      change ¬ (3 : UInt32) < variants at hi
      rw [UInt32.lt_iff_toNat_lt] at lo hi; change ¬ variants.toNat < 1 at lo; change ¬ 3 < variants.toNat at hi; omega
    cases pow : next_pow2 (cap*2) fuel with
    | none => simp [pow] at ok
    | some u =>
      obtain ⟨w,run,exact_⟩ := bdd_words_exact cap terms u variants fuel
      simp only [pow, run, Bind.bind, Option.bind, Option.pure_def, Option.some.injEq,
        decide_eq_true_eq, UInt64.le_iff_toNat_le, exact_] at ok
      exact ⟨capBound,vBound.1,vBound.2,u,rfl,ok⟩

theorem sat_layout_total (vars clauses store record : UInt32) (fuel : Nat) (l : SatLayout)
    (ok : sat_allocation_fits vars clauses store record fuel = some true)
    (run : sat_layout vars clauses store record fuel = some l) :
    l.total.toNat = satWords vars clauses store record := by
  have budget := (sat_admitted vars clauses store record fuel).mp ok
  unfold satWords at budget ⊢
  simp only [sat_layout, Option.pure_def, Option.some.injEq] at run
  subst l
  simp only [ST_WORDS, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem sat_bytes_safe (vars clauses store record : UInt32) (fuel : Nat) (l : SatLayout)
    (ok : sat_allocation_fits vars clauses store record fuel = some true)
    (run : sat_layout vars clauses store record fuel = some l) :
    l.total.toNat ≤ 1073741823 ∧ (l.total*4).toNat = l.total.toNat*4 := by
  have total := sat_layout_total vars clauses store record fuel l ok run
  have budget := (sat_admitted vars clauses store record fuel).mp ok
  refine ⟨by omega,?_⟩
  change (l.total.toNat*4)%4294967296 = _; omega

theorem bdd_bytes_safe (cap terms variants : UInt32) (fuel : Nat) (l : Layout)
    (ok : bdd_allocation_fits cap terms variants fuel = some true)
    (run : layout_for cap terms fuel = some l) :
    let extra : UInt32 := if variants > 1 then 32768 else 0
    (l.total+extra).toNat = l.total.toNat+extra.toNat ∧
      (l.total+extra).toNat ≤ 1073741823 ∧
      ((l.total+extra)*4).toNat = (l.total.toNat+extra.toNat)*4 := by
  obtain ⟨_,_,_,u,pow,budget⟩ := bdd_admitted cap terms variants fuel ok
  have full : footprint cap terms 0 u < 4294967296 := by
    unfold bddWords at budget
    unfold footprint
    change 3*cap.toNat+5*u.toNat+16*(stackSlots cap).toNat+64*terms.toNat+3120+0 < _
    omega
  have cl : ∃ cl, layout_for_clauses cap terms 0 fuel = some cl ∧ cl.total = l.total := by
    simp only [layout_for_clauses, run, Bind.bind, Option.bind, Option.pure_def]
    exact ⟨_,rfl,UInt32.add_zero _⟩
  obtain ⟨cl,clRun,same⟩ := cl
  have total := (complete_regions cap terms 0 u fuel cl pow clRun full).2.2.2.2.2.2.2.2.2.2
  rw [same] at total
  unfold footprint at total
  unfold bddWords at budget
  clear full pow ok run clRun same
  let extra : UInt32 := if variants > 1 then 32768 else 0
  have limit : l.total.toNat+extra.toNat ≤ 1073741823 := by
    by_cases h : variants > 1
    · simp only [extra, h, if_pos] at budget ⊢
      change l.total.toNat+32768 ≤ _
      change l.total.toNat = 3*cap.toNat+5*u.toNat+16*(stackSlots cap).toNat+64*terms.toNat+3120+0 at total
      omega
    · simp only [extra, h, if_false] at budget ⊢
      change l.total.toNat+0 ≤ _
      change l.total.toNat = 3*cap.toNat+5*u.toNat+16*(stackSlots cap).toNat+64*terms.toNat+3120+0 at total
      omega
  have addr : (l.total+extra).toNat = l.total.toNat+extra.toNat := by
    rw [UInt32.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  change (l.total+extra).toNat = _ ∧ (l.total+extra).toNat ≤ _ ∧ _
  refine ⟨addr,by rw [addr]; exact limit,?_⟩
  rw [UInt32.toNat_mul, addr]
  change ((l.total.toNat+extra.toNat)*4)%4294967296 = _
  exact Nat.mod_eq_of_lt (by omega)

end Oak.SolverAllocation
