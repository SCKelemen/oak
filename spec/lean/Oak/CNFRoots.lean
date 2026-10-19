import Oak.CNFObligationStore

set_option autoImplicit false
namespace Oak.CNFRoots
open Oak.CNFEmission Oak.CNFObligation

def rootCell (l : Layout) (p : Array UInt32) (r : UInt32) : Nat :=
  (l.bits_at + p.getD (rootStart p+r).toNat 0 * 64).toNat

-- This list reads only the initial memory, independently of the emitter.
def initialLiterals (l : Layout) (initial p : Array UInt32) (roots r : UInt32) : Nat → List UInt32
  | 0 => []
  | count+1 => readLiteral l initial p r roots :: initialLiterals l initial p roots (r+1) count

theorem initial_length (l : Layout) (initial p : Array UInt32) (roots r : UInt32) (count : Nat) :
    (initialLiterals l initial p roots r count).length = count := by
  induction count generalizing r with
  | zero => rfl
  | succ count ih => simp [initialLiterals, ih]

theorem step_preserves_read (l : Layout) (mem p : Array UInt32) (at_ n lit q roots : UInt32)
    (always : Bool) (before : rootCell l p q < at_.toNat)
    (bound : at_.toNat+1+n.toNat < 4294967296) :
    readLiteral l (step mem at_ n always lit).1 p q roots = readLiteral l mem p q roots := by
  have first : (at_+1).toNat = at_.toNat+1 := by
    change (at_.toNat+1) % 4294967296 = at_.toNat+1; omega
  have addr : (at_+1+n).toNat = at_.toNat+1+n.toNat := by
    rw [UInt32.toNat_add, first, Nat.mod_eq_of_lt (by omega)]
  unfold step
  split
  · rfl
  · split
    · rfl
    · unfold readLiteral
      rw [Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ (by change (at_+1+n).toNat ≠ rootCell l p q; rw [addr]; omega)]

-- The induction constructs the trace, rather than requiring it as a premise.
theorem initial_trace (l : Layout) (initial mem p : Array UInt32) (roots at_ n r : UInt32)
    (always : Bool) (count : Nat)
    (remaining : r.toNat+count = roots.toNat)
    (bound : at_.toNat+1+n.toNat+count < 4294967296)
    (before : ∀ q : UInt32, q < roots → rootCell l p q < at_.toNat)
    (same : ∀ q : UInt32, q < roots → readLiteral l mem p q roots = readLiteral l initial p q roots) :
    Trace l p roots at_ mem n always r (initialLiterals l initial p roots r count) := by
  induction count generalizing mem n r always with
  | zero =>
    apply Trace.done
    simp only [UInt32.lt_iff_toNat_lt]
    omega
  | succ count ih =>
    have inside : r < roots := by rw [UInt32.lt_iff_toNat_lt]; omega
    have inc : (r+1).toNat = r.toNat+1 := by
      have := roots.toNat_lt
      change (r.toNat+1) % 4294967296 = r.toNat+1
      omega
    apply Trace.next mem n r _ always _ inside (same r inside)
    dsimp only
    apply ih
    · rw [inc]; omega
    · unfold step
      split
      · simpa using (show at_.toNat+1+n.toNat+count < 4294967296 by omega)
      · split
        · simpa using (show at_.toNat+1+n.toNat+count < 4294967296 by omega)
        · have next : (n+1).toNat = n.toNat+1 := by
            change (n.toNat+1) % 4294967296 = n.toNat+1; omega
          simp only [next]; omega
    · intro q hq
      rw [step_preserves_read l mem p at_ n _ q roots always (before q hq) (by omega)]
      exact same q hq

theorem production_initial (l : Layout) (mem p : Array UInt32) (used : UInt32) (fuel : Nat)
    (counter : mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0 = used)
    (admit : cnf_obligation_fits used (p.getD 2 0) l.clauses_cap (fuel+(p.getD 2 0).toNat+1) = some true)
    (bound : (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+1+(p.getD 2 0).toNat < 4294967296)
    (before : ∀ q : UInt32, q < p.getD 2 0 → rootCell l p q < (l.clauses_at+LRAT_HEADER_WORDS+used).toNat) :
    cnf_obligation l mem p (fuel+(p.getD 2 0).toNat+1) =
      let s := consume mem (l.clauses_at+LRAT_HEADER_WORDS+used) 0 false
        (initialLiterals l mem p (p.getD 2 0) 0 (p.getD 2 0).toNat)
      cnf_obligation_finish l s.1 (l.clauses_at+LRAT_HEADER_WORDS+used) used s.2.1 s.2.2 true
        (fuel+(p.getD 2 0).toNat+1) := by
  have trace := initial_trace l mem mem p (p.getD 2 0) (l.clauses_at+LRAT_HEADER_WORDS+used)
    0 0 false (p.getD 2 0).toNat (by simp) (by simpa using bound) before (by intros; rfl)
  have run := production_trace l mem p used _ fuel counter (by simpa [initial_length] using admit) trace
  simpa only [initial_length] using run

-- A root index within the bit-storage region yields the separation premise.
theorem root_before_clauses (l : Layout) (p : Array UInt32) (q : UInt32) (terms : Nat)
    (index : (p.getD (rootStart p+q).toNat 0).toNat < terms)
    (bits : l.bits_at.toNat+terms*64 ≤ l.clauses_at.toNat) :
    rootCell l p q < l.clauses_at.toNat := by
  have cap := l.clauses_at.toNat_lt
  unfold rootCell
  rw [UInt32.toNat_add, UInt32.toNat_mul]
  change (l.bits_at.toNat + ((p.getD (rootStart p+q).toNat 0).toNat * 64) % 4294967296) % 4294967296 < _
  omega

-- Extracted constructor equations, before any no-wrap reasoning.
theorem layout_shape (cap terms capacity : UInt32) (fuel : Nat) (l : Layout)
    (run : layout_for_clauses cap terms capacity fuel = some l) :
    l.selects_at = l.bits_at+terms*64 ∧ l.state_at = l.selects_at+3104 ∧
      l.clauses_at = l.state_at+16 ∧ l.clauses_cap = capacity ∧ l.total = l.clauses_at+capacity := by
  cases h : next_pow2 (cap*2) fuel with
  | none => simp [layout_for_clauses, layout_for, h] at run
  | some u =>
    simp only [layout_for_clauses, layout_for, h, Option.pure_def, Bind.bind, Option.bind,
      Option.some.injEq] at run
    subst l
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

-- This proves the bit/select/state/clause suffix of the constructed layout.
-- Prefix allocation and next_pow2 termination are not hidden in this bound.
theorem constructed_regions (cap terms capacity : UInt32) (fuel : Nat) (l : Layout)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : l.bits_at.toNat+terms.toNat*64+3104+16+capacity.toNat < 4294967296) :
    l.bits_at.toNat+terms.toNat*64 ≤ l.clauses_at.toNat ∧
      l.state_at.toNat+5 < l.clauses_at.toNat ∧
      l.clauses_at.toNat+l.clauses_cap.toNat = l.total.toNat ∧
      l.clauses_at.toNat+l.clauses_cap.toNat < 4294967296 := by
  obtain ⟨selects,state,clauses,capacityEq,total⟩ := layout_shape cap terms capacity fuel l run
  have mul : (terms*64).toNat = terms.toNat*64 := by
    change (terms.toNat*64) % 4294967296 = terms.toNat*64; omega
  have s : l.selects_at.toNat = l.bits_at.toNat+terms.toNat*64 := by
    rw [selects, UInt32.toNat_add, mul, Nat.mod_eq_of_lt (by omega)]
  have t : l.state_at.toNat = l.bits_at.toNat+terms.toNat*64+3104 := by
    rw [state, UInt32.toNat_add, s]
    change (_+3104) % 4294967296 = _; omega
  have c : l.clauses_at.toNat = l.bits_at.toNat+terms.toNat*64+3104+16 := by
    rw [clauses, UInt32.toNat_add, t]
    change (_+16) % 4294967296 = _; omega
  have end_ : l.total.toNat = l.clauses_at.toNat+capacity.toNat := by
    rw [total, UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [capacityEq]
  omega

-- Derive both trace premises from production construction and valid root IDs.
theorem constructed_trace (cap terms capacity used : UInt32) (l : Layout)
    (mem p : Array UInt32) (fuel : Nat)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : l.bits_at.toNat+terms.toNat*64+3104+16+capacity.toNat < 4294967296)
    (admit : cnf_obligation_fits used (p.getD 2 0) l.clauses_cap fuel = some true)
    (indices : ∀ q : UInt32, q < p.getD 2 0 → (p.getD (rootStart p+q).toNat 0).toNat < terms.toNat) :
    Trace l p (p.getD 2 0) (l.clauses_at+LRAT_HEADER_WORDS+used) mem 0 false 0
      (initialLiterals l mem p (p.getD 2 0) 0 (p.getD 2 0).toNat) := by
  have regions := constructed_regions cap terms capacity fuel l run budget
  have addr := Oak.CNFObligationStore.layout_bounds l.clauses_at used (p.getD 2 0) l.clauses_cap fuel admit regions.2.2.2
  apply initial_trace l mem mem p _ _ 0 0 false _ (by simp)
  · change (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+1+0+(p.getD 2 0).toNat < 4294967296
    omega
  · intro q hq
    have root := root_before_clauses l p q terms.toNat (indices q hq) regions.1
    rw [addr.1]; omega
  · intros; rfl

theorem constructed_production (cap terms capacity used : UInt32) (l : Layout)
    (mem p : Array UInt32) (fuel : Nat)
    (run : layout_for_clauses cap terms capacity (fuel+(p.getD 2 0).toNat+1) = some l)
    (budget : l.bits_at.toNat+terms.toNat*64+3104+16+capacity.toNat < 4294967296)
    (counter : mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0 = used)
    (admit : cnf_obligation_fits used (p.getD 2 0) l.clauses_cap (fuel+(p.getD 2 0).toNat+1) = some true)
    (indices : ∀ q : UInt32, q < p.getD 2 0 → (p.getD (rootStart p+q).toNat 0).toNat < terms.toNat) :
    cnf_obligation l mem p (fuel+(p.getD 2 0).toNat+1) =
      let s := consume mem (l.clauses_at+LRAT_HEADER_WORDS+used) 0 false
        (initialLiterals l mem p (p.getD 2 0) 0 (p.getD 2 0).toNat)
      cnf_obligation_finish l s.1 (l.clauses_at+LRAT_HEADER_WORDS+used) used s.2.1 s.2.2 true
        (fuel+(p.getD 2 0).toNat+1) := by
  have trace := constructed_trace cap terms capacity used l mem p _ run budget admit indices
  have execution := production_trace l mem p used _ fuel counter (by simpa [initial_length] using admit) trace
  simpa only [initial_length] using execution

end Oak.CNFRoots
