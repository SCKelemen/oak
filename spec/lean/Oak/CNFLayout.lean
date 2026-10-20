import Oak.CNFRoots

set_option autoImplicit false
namespace Oak.CNFLayout
open Oak.CNFEmission

-- The extracted doubling loop terminates before its arithmetic can wrap.
theorem pow2_loop (n p : UInt32) (k : Nat)
    (positive : 0 < p.toNat)
    (enough : n.toNat ≤ p.toNat * 2^k)
    (bound : p.toNat * 2^k < 4294967296) :
    ∃ q, next_pow2.loop1 n p (k+1) = some q ∧
      n.toNat ≤ q.toNat ∧ 0 < q.toNat ∧ q.toNat ≤ p.toNat * 2^k := by
  induction k generalizing p with
  | zero =>
    have stop : ¬ p < n := by simp only [UInt32.lt_iff_toNat_lt]; simpa using enough
    refine ⟨p, ?_, ?_, positive, ?_⟩
    · simp [next_pow2.loop1, stop]
    · simpa using enough
    · simp
  | succ k ih =>
    by_cases stop : ¬ p < n
    · refine ⟨p, ?_, ?_, positive, ?_⟩
      · simp only [next_pow2.loop1, stop, decide_false, Bool.false_eq_true, if_false, Option.pure_def]
      · simp only [UInt32.lt_iff_toNat_lt] at stop; omega
      · have h : 1 ≤ 2^(k+1) := Nat.one_le_pow k.succ 2 (by decide)
        exact Nat.le_mul_of_pos_right _ h
    · have active : p < n := by exact Classical.byContradiction stop
      have power : p.toNat * 2^(k+1) = (p.toNat*2)*2^k := by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have factor : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
      have doubleBound : p.toNat*2 < 4294967296 := by
        have lower := Nat.le_mul_of_pos_right (p.toNat*2) factor
        rw [power] at bound; omega
      have exactDouble : (p*2).toNat = p.toNat*2 := by
        change (p.toNat*2) % 4294967296 = p.toNat*2
        exact Nat.mod_eq_of_lt doubleBound
      obtain ⟨q,run,lower,pos,upper⟩ := ih (p*2) (by rw [exactDouble]; omega)
        (by rw [exactDouble, ← power]; exact enough) (by rw [exactDouble, ← power]; exact bound)
      refine ⟨q, ?_,lower,pos,?_⟩
      · simpa only [next_pow2.loop1, active, decide_true, if_true, Option.pure_def, Bind.bind, Option.bind] using run
      · rwa [exactDouble, ← power] at upper

theorem next_pow2_terminates (n : UInt32) (small : n.toNat ≤ 2147483648) :
    ∃ q, next_pow2 n 32 = some q ∧ n.toNat ≤ q.toNat ∧ 0 < q.toNat ∧ q.toNat ≤ 2147483648 := by
  obtain ⟨q,run,lower,pos,upper⟩ := pow2_loop n 1 31 (by decide) small (by decide)
  refine ⟨q, ?_,lower,pos,upper⟩
  simp only [next_pow2, run]

def stackSlots (cap : UInt32) : UInt32 :=
  if decide (cap < 32768) then (if cap == 0 then 1 else cap) else 32768

def footprint (cap terms capacity u : UInt32) : Nat :=
  3*cap.toNat + 5*u.toNat + 16*(stackSlots cap).toNat + 64*terms.toNat + 3120 + capacity.toNat

-- Exact prefix equations of the extracted constructor, with the loop result exposed.
theorem prefix_shape (cap terms capacity u : UInt32) (fuel : Nat) (l : Layout)
    (pow : next_pow2 (cap*2) fuel = some u)
    (run : layout_for_clauses cap terms capacity fuel = some l) :
    l.var_at = 0 ∧ l.low_at = cap ∧ l.high_at = cap*2 ∧ l.unique_at = cap*3 ∧
      l.cache_at = l.unique_at+u ∧ l.stack_at = l.cache_at+u*4 ∧
      l.stack_cap = stackSlots cap ∧ l.bits_at = l.stack_at+stackSlots cap*16 := by
  simp only [layout_for_clauses, layout_for, pow, Option.pure_def, Bind.bind, Option.bind,
    Option.some.injEq] at run
  subst l
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

-- The budget is in natural numbers, so it cannot itself wrap.
theorem prefix_regions (cap terms capacity u : UInt32) (fuel : Nat) (l : Layout)
    (pow : next_pow2 (cap*2) fuel = some u)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : footprint cap terms capacity u < 4294967296) :
    l.var_at.toNat = 0 ∧ l.low_at.toNat = cap.toNat ∧
      l.high_at.toNat = 2*cap.toNat ∧ l.unique_at.toNat = 3*cap.toNat ∧
      l.cache_at.toNat = 3*cap.toNat+u.toNat ∧
      l.stack_at.toNat = 3*cap.toNat+5*u.toNat ∧
      l.bits_at.toNat = 3*cap.toNat+5*u.toNat+16*(stackSlots cap).toNat := by
  obtain ⟨v,lo,hi,un,ca,st,sc,bi⟩ := prefix_shape cap terms capacity u fuel l pow run
  unfold footprint at budget
  have h : l.high_at.toNat = 2*cap.toNat := by
    rw [hi]; change (cap.toNat*2)%4294967296 = _; omega
  have a : l.unique_at.toNat = 3*cap.toNat := by
    rw [un]; change (cap.toNat*3)%4294967296 = _; omega
  have b : l.cache_at.toNat = 3*cap.toNat+u.toNat := by
    rw [ca, UInt32.toNat_add, a]; omega
  have c : l.stack_at.toNat = 3*cap.toNat+5*u.toNat := by
    rw [st, UInt32.toNat_add, b, UInt32.toNat_mul]
    change (_+(u.toNat*4)%4294967296)%4294967296 = _; omega
  have d : l.bits_at.toNat = 3*cap.toNat+5*u.toNat+16*(stackSlots cap).toNat := by
    rw [bi, UInt32.toNat_add, c, UInt32.toNat_mul]
    change (_+((stackSlots cap).toNat*16)%4294967296)%4294967296 = _; omega
  exact ⟨by rw [v]; rfl, by rw [lo], h,a,b,c,d⟩

theorem complete_regions (cap terms capacity u : UInt32) (fuel : Nat) (l : Layout)
    (pow : next_pow2 (cap*2) fuel = some u)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : footprint cap terms capacity u < 4294967296) :
    l.var_at.toNat+cap.toNat = l.low_at.toNat ∧
      l.low_at.toNat+cap.toNat = l.high_at.toNat ∧
      l.high_at.toNat+cap.toNat = l.unique_at.toNat ∧
      l.unique_at.toNat+u.toNat = l.cache_at.toNat ∧
      l.cache_at.toNat+4*u.toNat = l.stack_at.toNat ∧
      l.stack_at.toNat+16*(stackSlots cap).toNat = l.bits_at.toNat ∧
      l.bits_at.toNat+64*terms.toNat = l.selects_at.toNat ∧
      l.selects_at.toNat+3104 = l.state_at.toNat ∧
      l.state_at.toNat+16 = l.clauses_at.toNat ∧
      l.clauses_at.toNat+capacity.toNat = l.total.toNat ∧
      l.total.toNat = footprint cap terms capacity u := by
  have pre := prefix_regions cap terms capacity u fuel l pow run budget
  obtain ⟨sel,sta,cla,capac,tot⟩ := Oak.CNFRoots.layout_shape cap terms capacity fuel l run
  unfold footprint at budget ⊢
  have b := pre.2.2.2.2.2.2
  have s : l.selects_at.toNat = l.bits_at.toNat+64*terms.toNat := by
    rw [sel, UInt32.toNat_add, UInt32.toNat_mul]
    change (_+(terms.toNat*64)%4294967296)%4294967296 = _; omega
  have t : l.state_at.toNat = l.selects_at.toNat+3104 := by
    rw [sta, UInt32.toNat_add]; change (_+3104)%4294967296 = _; omega
  have c : l.clauses_at.toNat = l.state_at.toNat+16 := by
    rw [cla, UInt32.toNat_add]; change (_+16)%4294967296 = _; omega
  have e : l.total.toNat = l.clauses_at.toNat+capacity.toNat := by
    rw [tot, UInt32.toNat_add]; omega
  rcases pre with ⟨v,lo,hi,un,ca,st,bi⟩
  omega

-- This establishes existence, rather than assuming the constructor returns.
theorem constructor_terminates (cap terms capacity : UInt32)
    (small : cap.toNat ≤ 1073741824) :
    ∃ u l, next_pow2 (cap*2) 32 = some u ∧ layout_for_clauses cap terms capacity 32 = some l ∧
      2*cap.toNat ≤ u.toNat ∧ 0 < u.toNat ∧ u.toNat ≤ 2147483648 := by
  have double : (cap*2).toNat = 2*cap.toNat := by
    change (cap.toNat*2)%4294967296 = _; omega
  obtain ⟨u,pow,lower,pos,upper⟩ := next_pow2_terminates (cap*2) (by rw [double]; omega)
  cases run : layout_for_clauses cap terms capacity 32 with
  | none => simp [layout_for_clauses, layout_for, pow] at run
  | some l => exact ⟨u,l,pow,rfl,by rwa [double] at lower,pos,upper⟩

-- Discharges the natural budget premise used by the existing root-trace bridge.
theorem suffix_budget (cap terms capacity u : UInt32) (fuel : Nat) (l : Layout)
    (pow : next_pow2 (cap*2) fuel = some u)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : footprint cap terms capacity u < 4294967296) :
    l.bits_at.toNat+terms.toNat*64+3104+16+capacity.toNat < 4294967296 := by
  have bits := (prefix_regions cap terms capacity u fuel l pow run budget).2.2.2.2.2.2
  unfold footprint at budget
  omega

end Oak.CNFLayout
