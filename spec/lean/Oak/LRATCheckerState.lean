import Oak.LRATCheckerExtracted
import Oak.LRATRUPSoundness

/-!
State invariants for the complete production checker extraction, pinned by
`TestLRATKernelCheckerExtract`. These lemmas establish the assignment reset
and deletion behavior needed to compose production RUP soundness. They do not
yet prove the initial-clause decoder or the complete record-processing loop.
-/

namespace Oak.LRATChecker

/-- The separately generated recursive functions have distinct Lean names;
induction identifies their bodies and recursive calls at every fuel. -/
theorem undo_loop_extraction_eq : lrat_undo.loop1 = LRATRUP.lrat_undo.loop1 := by
  funext assign trail used i fuel
  induction fuel generalizing assign i with
  | zero => rfl
  | succ fuel ih =>
    simp only [lrat_undo.loop1, LRATRUP.lrat_undo.loop1,
      LRAT_UNASSIGNED, LRATRUP.LRAT_UNASSIGNED, ih]

theorem undo_extraction_eq : lrat_undo = LRATRUP.lrat_undo := by
  funext assign trail used fuel
  simp only [lrat_undo, LRATRUP.lrat_undo, undo_loop_extraction_eq]

theorem target_loop_extraction_eq : lrat_rup.loop1 = LRATRUP.lrat_rup.loop1 := by
  funext words at_ n assign trail variables status settled used i fuel
  induction fuel generalizing assign trail status settled used i with
  | zero => rfl
  | succ fuel ih =>
    simp only [lrat_rup.loop1, LRATRUP.lrat_rup.loop1,
      lrat_false_value, LRATRUP.lrat_false_value,
      LRAT_UNASSIGNED, LRATRUP.LRAT_UNASSIGNED, LRAT_ACCEPTED, LRATRUP.LRAT_ACCEPTED,
      LRAT_MALFORMED, LRATRUP.LRAT_MALFORMED, ih]
    rfl

theorem scan_loop_extraction_eq : lrat_rup.loop3 = LRATRUP.lrat_rup.loop3 := by
  funext store assign status start count remaining unit j fuel
  induction fuel generalizing status remaining unit j with
  | zero => rfl
  | succ fuel ih =>
    simp only [lrat_rup.loop3, LRATRUP.lrat_rup.loop3,
      lrat_true_value, LRATRUP.lrat_true_value,
      LRAT_UNASSIGNED, LRATRUP.LRAT_UNASSIGNED, LRAT_ACCEPTED, LRATRUP.LRAT_ACCEPTED,
      LRAT_SATISFIED, LRATRUP.LRAT_SATISFIED, ih]
    rfl

theorem hints_loop_extraction_eq : lrat_rup.loop2 = LRATRUP.lrat_rup.loop2 := by
  funext words at_ n starts lengths alive store assign trail max_id status settled used h fuel
  induction fuel generalizing assign trail status settled used h with
  | zero => rfl
  | succ fuel ih =>
    simp only [lrat_rup.loop2, LRATRUP.lrat_rup.loop2,
      lrat_true_value, LRATRUP.lrat_true_value, scan_loop_extraction_eq,
      LRAT_ACCEPTED, LRATRUP.LRAT_ACCEPTED, LRAT_MALFORMED, LRATRUP.LRAT_MALFORMED,
      LRAT_NOT_LIVE, LRATRUP.LRAT_NOT_LIVE, LRAT_NOT_UNIT, LRATRUP.LRAT_NOT_UNIT, ih]
    rfl

/-- The RUP function reached by the full-checker extraction is extensionally
the same implementation whose propagation soundness has been proved. -/
theorem rup_extraction_eq : lrat_rup = LRATRUP.lrat_rup := by
  funext words target_at target_n hints_at hints_n starts lengths alive store assign trail variables max_id fuel
  simp only [lrat_rup, LRATRUP.lrat_rup, target_loop_extraction_eq, hints_loop_extraction_eq,
    undo_extraction_eq, LRAT_ACCEPTED, LRATRUP.LRAT_ACCEPTED, LRAT_NO_CONFLICT, LRATRUP.LRAT_NO_CONFLICT]
  rfl

/-- The actual assignment initializer clears the declared range. -/
theorem assignment_loop_spec (fuel : Nat) (assign : Array UInt8) (variables i : UInt32)
    (hi : i ≤ variables) (hf : variables.toNat - i.toNat < fuel) :
    lrat_check.loop2 assign true variables i fuel =
      some (LRATRUP.clearList assign (List.range' i.toNat (variables.toNat - i.toNat)), variables) := by
  induction fuel generalizing assign i with
  | zero => omega
  | succ fuel ih =>
    rw [lrat_check.loop2]
    by_cases h : i < variables
    · simp only [decide_eq_true h, Bool.and_self, ite_true]
      have hs := LRATRUP.counter_succ i variables h
      have hn := UInt32.lt_iff_toNat_lt.mp h
      have he : variables.toNat - i.toNat = (variables.toNat - (i + 1).toNat) + 1 := by omega
      rw [ih _ (i + 1) (by rw [UInt32.le_iff_toNat_le, hs]; omega) (by omega), he]
      simp only [List.range'_succ, LRATRUP.clearList, List.foldl_cons, LRAT_UNASSIGNED, hs]
    · have he : i = variables := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.le_iff_toNat_le] at hi
        rw [UInt32.lt_iff_toNat_lt] at h
        omega
      subst i
      simp [LRATRUP.clearList]

/-- Sufficient fuel produces zero scratch exactly where the RUP soundness
theorem requires it; the unused suffix keeps its original contents. -/
theorem assignment_init_spec (assign : Array UInt8) (variables : UInt32) (fuel : Nat)
    (capacity : variables.toNat ≤ assign.size) (hf : variables.toNat < fuel) :
    ∃ result, lrat_check.loop2 assign true variables 0 fuel = some (result, variables) ∧
      result.size = assign.size ∧
      (∀ v, v < variables.toNat → result.getD v 0 = 0) ∧
      (∀ v, variables.toNat ≤ v → v < assign.size → result.getD v 0 = assign.getD v 0) := by
  refine ⟨LRATRUP.clearList assign (List.range' 0 variables.toNat), ?_, LRATRUP.clearList_size _ _, ?_, ?_⟩
  · simpa using assignment_loop_spec fuel assign variables 0 (by simp) (by simpa using hf)
  · intro v hv
    rw [LRATRUP.clearList_getD assign _ v (by omega)]
    simp [hv]
  · intro v hv bound
    rw [LRATRUP.clearList_getD assign _ v bound]
    simp [Nat.not_lt.mpr hv]

/-- The inclusive live-table reset is the same range reset, provided its
endpoint has a successor. The entry capacity guard supplies that fact. -/
theorem live_loop_as_assignment (fuel : Nat) (alive : Array UInt8) (max_id i : UInt32)
    (bound : max_id < 4294967295) :
    lrat_check.loop1 alive true max_id i fuel =
      lrat_check.loop2 alive true (max_id + 1) i fuel := by
  induction fuel generalizing alive i with
  | zero => rfl
  | succ fuel ih =>
    have hs := LRATRUP.counter_succ max_id 4294967295 bound
    have guard : (i ≤ max_id) = (i < max_id + 1) := by
      apply propext
      rw [UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, hs]
      omega
    simp only [lrat_check.loop1, lrat_check.loop2, guard, LRAT_UNASSIGNED, ih]

theorem live_init_spec (alive : Array UInt8) (max_id : UInt32) (fuel : Nat)
    (capacity : max_id < alive.size.toUInt32) (hf : max_id.toNat + 1 < fuel) :
    ∃ result, lrat_check.loop1 alive true max_id 0 fuel = some (result, max_id + 1) ∧
      result.size = alive.size ∧ ∀ id, id ≤ max_id.toNat → result.getD id 0 = 0 := by
  have smaller : max_id < 4294967295 := by
    have := alive.size.toUInt32.toNat_lt
    rw [UInt32.lt_iff_toNat_lt] at capacity ⊢
    change max_id.toNat < 4294967295
    omega
  have hs := LRATRUP.counter_succ max_id 4294967295 smaller
  have sizeBound : (max_id + 1).toNat ≤ alive.size := by
    have wrapBound : alive.size.toUInt32.toNat ≤ alive.size := Nat.mod_le _ _
    rw [UInt32.lt_iff_toNat_lt] at capacity
    omega
  obtain ⟨result, run, size, zero, rest⟩ := assignment_init_spec alive (max_id + 1) fuel sizeBound (by omega)
  refine ⟨result, ?_, size, ?_⟩
  · rw [live_loop_as_assignment fuel alive max_id 0 smaller]
    exact run
  · intro id hid
    exact zero id (by omega)

/-- Immediately after live-table initialization there are no live clauses,
independently of the old starts, lengths, store, or unused alive suffix. -/
theorem initialized_database_empty (starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (max_id : UInt32)
    (zero : ∀ id, id ≤ max_id.toNat → alive.getD id 0 = 0) :
    LRATRUP.wordDatabase starts lengths alive store max_id = fun _ => none := by
  funext id
  unfold LRATRUP.wordDatabase
  split
  · rename_i guard
    exact False.elim (guard.2.2 (zero id guard.2.1))
  · rfl

/-- Clearing a live byte cannot introduce a new live slot, even outside the
array's bounds in the extracted getD/setIfInBounds semantics. -/
def LiveSubset (before after : Array UInt8) : Prop :=
  ∀ id, after.getD id 0 ≠ 0 → before.getD id 0 ≠ 0

theorem clear_getD (alive : Array UInt8) (at_ id : Nat) :
    (alive.setIfInBounds at_ 0).getD id 0 = if at_ = id then 0 else alive.getD id 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : at_ = id
  · subst at_
    by_cases bound : id < alive.size <;> simp [bound]
  · simp [h]

theorem clear_live_subset (alive : Array UInt8) (at_ : Nat) :
    LiveSubset alive (alive.setIfInBounds at_ 0) := by
  intro id live
  rw [clear_getD] at live
  by_cases eq : at_ = id
  · simp [eq] at live
  · simpa only [if_neg eq] using live

theorem live_subset_trans {first middle last : Array UInt8}
    (h1 : LiveSubset first middle) (h2 : LiveSubset middle last) : LiveSubset first last := by
  intro id live
  exact h1 id (h2 id live)

/-- The production deletion loop only removes live clauses. This holds even
on refusal: partial deletion before a bad id cannot introduce a clause. -/
theorem deletion_loop_subset (fuel : Nat) (words : Array UInt32) (alive : Array UInt8)
    (status max_id at_ k d : UInt32) (alive' : Array UInt8) (status' d' : UInt32)
    (run : lrat_check.loop6 words alive status max_id at_ k d fuel = some (alive', status', d')) :
    alive'.size = alive.size ∧ LiveSubset alive alive' := by
  induction fuel generalizing alive status d alive' status' d' with
  | zero => simp [lrat_check.loop6] at run
  | succ fuel ih =>
    by_cases enter : d < k ∧ status = LRAT_ACCEPTED
    · obtain ⟨hd, hs⟩ := enter
      subst status
      generalize hcid : words.getD (at_ + 3 + d).toNat 0 = cid at *
      by_cases live : cid ≤ max_id ∧ 0 < cid ∧ alive.getD cid.toNat 0 ≠ 0
      · have guard : ((decide (cid ≤ max_id) && decide (cid > 0)) &&
            (alive.getD cid.toNat 0 != 0)) = true := by simpa [and_assoc] using live
        simp only [lrat_check.loop6, hd, decide_true, beq_self_eq_true, Bool.and_self,
          ite_true, hcid, guard, bind, Option.bind, Option.pure_def] at run
        obtain ⟨size, subset⟩ := ih _ LRAT_ACCEPTED (d + 1) _ _ _ run
        exact ⟨size.trans Array.size_setIfInBounds, live_subset_trans (clear_live_subset alive _) subset⟩
      · have guard : ((decide (cid ≤ max_id) && decide (cid > 0)) &&
            (alive.getD cid.toNat 0 != 0)) = false := by simpa [and_assoc] using live
        simp only [lrat_check.loop6, hd, decide_true, beq_self_eq_true, Bool.and_self,
          ite_true, hcid, guard, Bool.false_eq_true, ite_false, bind, Option.bind, Option.pure_def] at run
        exact ih alive LRAT_NOT_LIVE (d + 1) _ _ _ run
    · have guard : (decide (d < k) && (status == LRAT_ACCEPTED)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        by_cases hd : d < k
        · exact Or.inr (fun hs => enter ⟨hd, hs⟩)
        · exact Or.inl hd
      simp only [lrat_check.loop6, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, fun _ h => h⟩

theorem live_subset_models (starts lengths : Array UInt32) (before after : Array UInt8)
    (store : Array UInt32) (max_id : UInt32) (subset : LiveSubset before after)
    (a : RupCheck.Assignment) (models : RupCheck.Models a (LRATRUP.wordDatabase starts lengths before store max_id)) :
    RupCheck.Models a (LRATRUP.wordDatabase starts lengths after store max_id) := by
  intro id clause lookup
  unfold LRATRUP.wordDatabase at lookup
  split at lookup
  · rename_i guard
    apply models id clause
    rw [LRATRUP.wordDatabase, if_pos ⟨guard.1, guard.2.1, subset id guard.2.2⟩]
    exact lookup
  · contradiction

theorem deletion_preserves_models (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (status max_id at_ k d : UInt32)
    (alive' : Array UInt8) (status' d' : UInt32)
    (run : lrat_check.loop6 words alive status max_id at_ k d fuel = some (alive', status', d'))
    (a : RupCheck.Assignment) (models : RupCheck.Models a (LRATRUP.wordDatabase starts lengths alive store max_id)) :
    RupCheck.Models a (LRATRUP.wordDatabase starts lengths alive' store max_id) :=
  live_subset_models starts lengths alive alive' store max_id
    (deletion_loop_subset fuel words alive status max_id at_ k d alive' status' d' run).2 a models

theorem deletion_preserves_variables (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (status variables max_id at_ k d : UInt32)
    (alive' : Array UInt8) (status' d' : UInt32)
    (run : lrat_check.loop6 words alive status max_id at_ k d fuel = some (alive', status', d'))
    (valid : LRATRUP.LiveVariables starts lengths alive store variables max_id) :
    LRATRUP.LiveVariables starts lengths alive' store variables max_id := by
  intro id upper lower live j hj
  exact valid id upper lower
    ((deletion_loop_subset fuel words alive status max_id at_ k d alive' status' d' run).2 id.toNat live) j hj

end Oak.LRATChecker
