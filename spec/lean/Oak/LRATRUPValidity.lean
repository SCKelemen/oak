import Oak.LRATRUPSoundness

/-!
The production RUP target scan validates every literal, including the suffix
after a tautology settles the semantic check. These theorems derive variable
validity from acceptance; it is not a precondition on the incoming target.
-/

namespace Oak.LRATRUP

theorem target_valid (fuel : Nat) (words : Array UInt32)
    (target_at target_n variables : UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (status : UInt32) (settled : Bool) (used i : UInt32)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (status' : UInt32) (settled' : Bool) (used' i' : UInt32)
    (run : lrat_rup.loop1 words target_at target_n assign trail variables
      status settled used i fuel = some (assign', trail', status', settled', used', i'))
    (accepted : status' = LRAT_ACCEPTED) :
    status = LRAT_ACCEPTED ∧ ∀ k : UInt32, i ≤ k → k < target_n →
      words.getD (target_at + k).toNat 0 / 2 < variables := by
  induction fuel generalizing assign trail status settled used i assign' trail' status' settled' used' i' with
  | zero => simp [lrat_rup.loop1] at run
  | succ fuel ih =>
    by_cases enter : i < target_n ∧ status = LRAT_ACCEPTED
    · obtain ⟨hi, hs⟩ := enter
      subst status
      by_cases invalid : words.getD (target_at + i).toNat 0 / 2 ≥ variables
      · simp only [lrat_rup.loop1, hi, decide_true, Bool.and_self,
          ite_true, invalid, LRAT_MALFORMED, LRAT_ACCEPTED, BEq.beq,
          bind, Option.bind, Option.pure_def] at run
        have impossible := (ih _ _ 1 settled used (i + 1) _ _ _ _ _ _ run accepted).1
        contradiction
      · have current : words.getD (target_at + i).toNat 0 / 2 < variables := by
          rw [ge_iff_le, UInt32.le_iff_toNat_le] at invalid
          rw [UInt32.lt_iff_toNat_lt]
          omega
        have next : ∀ (a : Array UInt8) (t : Array UInt32) (q : Bool) (u : UInt32),
            lrat_rup.loop1 words target_at target_n a t variables LRAT_ACCEPTED q u (i + 1) fuel =
              some (assign', trail', status', settled', used', i') →
            ∀ k : UInt32, i ≤ k → k < target_n → words.getD (target_at + k).toNat 0 / 2 < variables := by
          intro a t q u recur k lower upper
          by_cases same : k = i
          · simpa only [same] using current
          · apply (ih a t LRAT_ACCEPTED q u (i + 1) _ _ _ _ _ _ recur accepted).2 k _ upper
            rw [UInt32.le_iff_toNat_le, counter_succ i target_n hi]
            have := UInt32.le_iff_toNat_le.mp lower
            have unequal : k.toNat ≠ i.toNat := fun h => same (UInt32.toNat_inj.mp h)
            omega
        refine ⟨rfl, ?_⟩
        cases settled with
        | true =>
          simp only [lrat_rup.loop1, hi, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, invalid, decide_false, Bool.false_eq_true, ite_false, Bool.not_true,
            Bool.and_false, bind, Option.bind, Option.pure_def] at run
          exact next _ _ _ _ run
        | false =>
          simp only [lrat_rup.loop1, hi, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, invalid, decide_false, Bool.false_eq_true, ite_false, Bool.not_false,
            Bool.and_true, false_value_spec, bind, Option.bind, Option.pure_def] at run
          by_cases fresh : assign.getD (words.getD (target_at + i).toNat 0 / 2).toNat 0 = LRAT_UNASSIGNED
          · simp only [beq_iff_eq, fresh, ite_true] at run
            exact next _ _ _ _ run
          · simp only [beq_iff_eq, fresh, ite_false] at run
            exact next _ _ _ _ run
    · have guard : (decide (i < target_n) && (status == LRAT_ACCEPTED)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        by_cases hi : i < target_n
        · exact Or.inr (fun hs => enter ⟨hi, hs⟩)
        · exact Or.inl hi
      simp only [lrat_rup.loop1, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨accepted, ?_⟩
      intro k lower upper
      have done : ¬i < target_n := fun hi => enter ⟨hi, accepted⟩
      rw [UInt32.lt_iff_toNat_lt] at done
      have := UInt32.le_iff_toNat_le.mp lower
      have := UInt32.lt_iff_toNat_lt.mp upper
      omega

/-- Acceptance of the complete production RUP call implies that every target
literal names a declared variable, even for an already-settled tautology. -/
theorem production_target_valid (fuel : Nat) (words : Array UInt32)
    (target_at target_n hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id : UInt32) (starts' lengths' : Array UInt32) (alive' : Array UInt8)
    (store' : Array UInt32) (assign' : Array UInt8) (trail' : Array UInt32)
    (run : lrat_rup words target_at target_n hints_at hints_n starts lengths alive store assign trail variables max_id fuel =
      some (LRAT_ACCEPTED, starts', lengths', alive', store', assign', trail')) :
    ∀ k : UInt32, k < target_n → words.getD (target_at + k).toNat 0 / 2 < variables := by
  unfold lrat_rup at run
  cases targetRun : lrat_rup.loop1 words target_at target_n assign trail variables LRAT_ACCEPTED false 0 0 fuel with
  | none => simp [targetRun] at run
  | some state =>
    rcases state with ⟨a1, t1, s1, q1, u1, i1⟩
    simp only [targetRun, bind, Option.bind, Option.pure_def] at run
    have targetAccepted : s1 = LRAT_ACCEPTED := by
      by_cases good : s1 = LRAT_ACCEPTED
      · exact good
      · have rejected : (s1 == LRAT_ACCEPTED) = false := beq_eq_false_iff_ne.mpr good
        cases fuel with
        | zero => simp [lrat_rup.loop2] at run
        | succ fuel =>
          simp only [lrat_rup.loop2, rejected, Bool.and_false, Bool.false_and,
            Bool.false_eq_true, ite_false, bind, Option.bind, Option.pure_def] at run
          cases undoRun : lrat_undo a1 t1 u1 (fuel + 1) with
          | none => simp [undoRun] at run
          | some state =>
            rcases state with ⟨unused, a2, t2⟩
            simp only [undoRun, Option.some.injEq, Prod.mk.injEq] at run
            exact False.elim (good run.1)
    intro k hk
    exact (target_valid fuel words target_at target_n variables assign trail LRAT_ACCEPTED false 0 0
      a1 t1 s1 q1 u1 i1 targetRun targetAccepted).2 k (by simp) hk

end Oak.LRATRUP
