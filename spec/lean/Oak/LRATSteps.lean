import Oak.LRATRecord

/-! Model preservation through the production outer proof-step parser. -/
set_option autoImplicit false
namespace Oak.LRATChecker

/-- The database part of the parser invariant. All bounds are mathematical
bounds on arrays, rather than truncating their lengths to machine words. -/
structure StoreModel (starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (variables max_id store_words used : UInt32)
    (a : RupCheck.Assignment) : Prop where
  startsCapacity : max_id.toNat < starts.size
  lengthsCapacity : max_id.toNat < lengths.size
  aliveCapacity : max_id.toNat < alive.size
  storeCapacity : store_words.toNat ≤ store.size
  usedCapacity : used.toNat ≤ store_words.toNat
  stored : StoredBefore starts lengths alive used max_id
  valid : LRATRUP.LiveVariables starts lengths alive store variables max_id
  models : RupCheck.Models a (LRATRUP.wordDatabase starts lengths alive store max_id)

theorem fits_spec (at_ n limit : UInt32) (fuel : Nat) :
    lrat_fits at_ n limit fuel = some (decide (at_.toNat + n.toNat ≤ limit.toNat)) := by
  cases h : lrat_fits at_ n limit fuel with
  | none => simp [lrat_fits] at h
  | some b =>
    have iff := fits_iff at_ n limit fuel
    rw [h, Option.some.injEq] at iff
    congr 1
    exact Bool.eq_iff_iff.mpr (by simpa using iff)

structure StepModel (starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id store_words used : UInt32) (a : RupCheck.Assignment) : Prop where
  database : StoreModel starts lengths alive store variables max_id store_words used a
  assignCapacity : variables.toNat ≤ assign.size
  trailCapacity : variables.toNat ≤ trail.size
  zero : ∀ v, v < variables.toNat → assign.getD v 0 = 0

theorem deletion_step_model (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id store_words used at_ k : UInt32) (a : RupCheck.Assignment)
    (state : StepModel starts lengths alive store assign trail variables max_id store_words used a)
    (alive' : Array UInt8) (status' d' : UInt32)
    (run : lrat_check.loop6 words alive LRAT_ACCEPTED max_id at_ k 0 fuel = some (alive', status', d')) :
    StepModel starts lengths alive' store assign trail variables max_id store_words used a := by
  obtain ⟨size, subset⟩ := deletion_loop_subset fuel words alive LRAT_ACCEPTED max_id at_ k 0 alive' status' d' run
  refine ⟨⟨state.database.startsCapacity, state.database.lengthsCapacity, by rw [size]; exact state.database.aliveCapacity,
    state.database.storeCapacity, state.database.usedCapacity, ?_, ?_, ?_⟩,
    state.assignCapacity, state.trailCapacity, state.zero⟩
  · intro id lower upper live
    exact state.database.stored id lower upper (subset id live)
  · exact deletion_preserves_variables fuel words starts lengths alive store LRAT_ACCEPTED variables max_id at_ k 0
      alive' status' d' run state.database.valid
  · exact live_subset_models starts lengths alive alive' store max_id subset a state.database.models

theorem addition_step_model (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id store_words used id lits_at n hints_at hints_n : UInt32) (a : RupCheck.Assignment)
    (state : StepModel starts lengths alive store assign trail variables max_id store_words used a)
    (positive : 0 < id) (upper : id ≤ max_id)
    (dest : used.toNat + n.toNat ≤ store_words.toNat)
    (source : lits_at.toNat + n.toNat ≤ words.size) (source32 : lits_at.toNat + n.toNat < 4294967296)
    (rs rl : Array UInt32) (ra : Array UInt8) (rt : Array UInt32) (rx : Array UInt8) (ry : Array UInt32)
    (rup : lrat_rup words lits_at n hints_at hints_n starts lengths alive store assign trail variables max_id fuel =
      some (LRAT_ACCEPTED, rs, rl, ra, rt, rx, ry))
    (store' : Array UInt32) (j' : UInt32)
    (copy : lrat_check.loop7 words rt used n lits_at 0 fuel = some (store', j')) :
    StepModel (rs.setIfInBounds id.toNat used) (rl.setIfInBounds id.toNat n) (ra.setIfInBounds id.toNat 1)
      store' rx ry variables max_id store_words (used + n) a ∧ n ≠ 0 := by
  have un := UInt32.le_iff_toNat_le.mp upper
  have sc : id.toNat < starts.size := by have := state.database.startsCapacity; omega
  have lc : id.toNat < lengths.size := by have := state.database.lengthsCapacity; omega
  have ac : id.toNat < alive.size := by have := state.database.aliveCapacity; omega
  have dn := Nat.le_trans dest state.database.storeCapacity
  have d32 := Nat.lt_of_le_of_lt dest store_words.toNat_lt
  obtain ⟨stored, valid, size, asize, tsize, zero⟩ := production_addition_state fuel words store starts lengths alive assign trail
    variables max_id id used n lits_at hints_at hints_n rs rl ra rt rx ry store' j'
    state.assignCapacity state.trailCapacity state.zero state.database.stored state.database.valid sc lc dn d32 source source32 rup copy
  have models := production_addition_preserves_models fuel words store starts lengths alive assign trail
    variables max_id id used n lits_at hints_at hints_n rs rl ra rt rx ry store' j'
    state.database.stored state.database.valid state.assignCapacity state.zero positive upper sc lc ac dn d32 source source32 rup copy a state.database.models
  obtain ⟨rseq, rleq, raeq, _⟩ := rup_database_unchanged fuel words lits_at n hints_at hints_n starts lengths alive store assign trail
    variables max_id LRAT_ACCEPTED rs rl ra rt rx ry rup
  refine ⟨⟨⟨by simpa [rseq] using state.database.startsCapacity, by simpa [rleq] using state.database.lengthsCapacity,
    by simpa [raeq] using state.database.aliveCapacity, by rw [size]; exact state.database.storeCapacity,
    by rw [add_exact used n d32]; exact dest, stored, valid, models⟩,
    by rw [asize]; exact state.assignCapacity, by rw [tsize]; exact state.trailCapacity, zero⟩, ?_⟩
  rw [rup_extraction_eq] at rup
  have entailed := LRATRUP.production_rup_entails fuel words lits_at n hints_at hints_n starts lengths alive store assign trail variables max_id
    state.assignCapacity state.zero state.database.valid rs rl ra rt rx ry rup a state.database.models
  intro nz
  simp [nz, LRATRUP.wordClause, RupCheck.SatisfiesClause] at entailed

/-- A model cannot survive an accepted outer step traversal that observes an
empty clause. This invariant includes restored scratch at every recursion. -/
theorem steps_loop_models (fuel : Nat) (words : Array UInt32)
    (variables max_id store_words end_ : UInt32) (a : RupCheck.Assignment)
    (wordCapacity : end_.toNat ≤ words.size)
    (starts lengths : Array UInt32) (alive : Array UInt8) (store : Array UInt32)
    (assign : Array UInt8) (trail : Array UInt32) (additions deletions at_ used : UInt32) (empty : Bool) (last : UInt32)
    (state : StepModel starts lengths alive store assign trail variables max_id store_words used a)
    (notEmpty : empty = false)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y : Array UInt32)
    (adds dels at' used' : UInt32) (empty' : Bool) (last' : UInt32)
    (run : lrat_check.loop5 words starts lengths alive store assign trail LRAT_ACCEPTED additions deletions variables max_id store_words at_ end_ used empty last fuel =
      some (s, l, v, t, x, y, LRAT_ACCEPTED, adds, dels, at', used', empty', last')) :
    StepModel s l v t x y variables max_id store_words used' a ∧ empty' = false := by
  induction fuel generalizing starts lengths alive store assign trail additions deletions at_ used empty last s l v t x y adds dels at' used' empty' last' with
  | zero => simp [lrat_check.loop5] at run
  | succ fuel ih =>
    by_cases enter : at_ < end_
    · simp only [lrat_check.loop5, enter, decide_true, beq_self_eq_true, Bool.and_self, ite_true,
        fits_spec, bind, Option.bind, Option.pure_def, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at run
      by_cases deletion : words.getD at_.toNat 0 = 1
      · simp only [deletion, ite_true] at run
        by_cases header : at_.toNat + 3 ≤ end_.toNat
        · simp only [show (3 : UInt32).toNat = 3 from rfl, header, ite_true] at run
          by_cases shape : ((at_ + 3).toNat + (words.getD (at_ + 2).toNat 0).toNat ≤ end_.toNat ∧
              words.getD (at_ + 1).toNat 0 > 0) ∧ words.getD (at_ + 1).toNat 0 ≥ last
          · simp only [shape, ite_true, and_self] at run
            cases scan : lrat_check.loop6 words alive LRAT_ACCEPTED max_id at_ (words.getD (at_ + 2).toNat 0) 0 fuel with
            | none => simp only [scan, reduceCtorEq] at run
            | some result =>
              rcases result with ⟨nextAlive, nextStatus, nextD⟩
              simp only [scan] at run
              have accepted := record_input_accepted (run := run)
              subst nextStatus
              exact ih (state := deletion_step_model fuel words starts lengths alive store assign trail variables max_id store_words used at_
                (words.getD (at_ + 2).toNat 0) a state nextAlive LRAT_ACCEPTED nextD scan) (notEmpty := notEmpty) (run := run)
          · simp only [shape, ite_false] at run
            have impossible := record_input_accepted (run := run)
            split at impossible <;> contradiction
        · simp only [show (3 : UInt32).toNat = 3 from rfl, header, ite_false] at run
          have impossible := record_input_accepted (run := run)
          contradiction
      · simp only [deletion, ite_false] at run
        by_cases addition : words.getD at_.toNat 0 = 0
        · simp only [addition, ite_true] at run
          by_cases header : at_.toNat + 3 ≤ end_.toNat
          · simp only [show (3 : UInt32).toNat = 3 from rfl, header, ite_true] at run
            by_cases literals : (at_ + 3).toNat + (words.getD (at_ + 2).toNat 0).toNat ≤ end_.toNat ∧
                at_ + 3 + words.getD (at_ + 2).toNat 0 < end_
            · simp only [literals, ite_true, true_and, and_self] at run
              by_cases hints : (at_ + 3 + words.getD (at_ + 2).toNat 0 + 1).toNat +
                  (words.getD (at_ + 3 + words.getD (at_ + 2).toNat 0).toNat 0).toNat ≤ end_.toNat
              · simp only [hints, ite_true] at run
                by_cases ordered : words.getD (at_ + 1).toNat 0 > last ∧ words.getD (at_ + 1).toNat 0 ≤ max_id
                · simp only [ordered, ite_true, and_self] at run
                  cases rup : lrat_rup words (at_ + 3) (words.getD (at_ + 2).toNat 0)
                      (at_ + 3 + words.getD (at_ + 2).toNat 0 + 1)
                      (words.getD (at_ + 3 + words.getD (at_ + 2).toNat 0).toNat 0)
                      starts lengths alive store assign trail variables max_id fuel with
                  | none => simp only [rup, reduceCtorEq] at run
                  | some result =>
                    rcases result with ⟨nextStatus, rs, rl, ra, rt, rx, ry⟩
                    simp only [rup] at run
                    by_cases accepted : nextStatus = LRAT_ACCEPTED
                    · subst nextStatus
                      simp only [ite_true] at run
                      by_cases room : used.toNat + (words.getD (at_ + 2).toNat 0).toNat ≤ store_words.toNat
                      · simp only [room, ite_true] at run
                        cases copy : lrat_check.loop7 words rt used (words.getD (at_ + 2).toNat 0) (at_ + 3) 0 fuel with
                        | none => simp only [copy, reduceCtorEq] at run
                        | some result =>
                          rcases result with ⟨nextStore, nextJ⟩
                          simp only [copy] at run
                          have positive : 0 < words.getD (at_ + 1).toNat 0 := by
                            have h := UInt32.lt_iff_toNat_lt.mp ordered.1
                            rw [UInt32.lt_iff_toNat_lt]; simp only [UInt32.toNat_zero]; omega
                          obtain ⟨nextState, nonempty⟩ := addition_step_model fuel words starts lengths alive store assign trail
                            variables max_id store_words used (words.getD (at_ + 1).toNat 0) (at_ + 3)
                            (words.getD (at_ + 2).toNat 0) _ _ a state positive ordered.2 room
                            (Nat.le_trans literals.1 wordCapacity) (Nat.lt_of_le_of_lt literals.1 end_.toNat_lt)
                            rs rl ra rt rx ry rup nextStore nextJ copy
                          exact ih (state := nextState) (notEmpty := by simp only [notEmpty, Bool.false_or, beq_eq_false_iff_ne]; exact nonempty) (run := run)
                      · simp only [room, ite_false] at run
                        have impossible := record_input_accepted (run := run)
                        contradiction
                    · simp only [accepted, ite_false] at run
                      exact False.elim (accepted (record_input_accepted (run := run)))
                · simp only [ordered, ite_false] at run
                  have impossible := record_input_accepted (run := run)
                  contradiction
              · simp only [hints, ite_false] at run
                have impossible := record_input_accepted (run := run)
                contradiction
            · simp only [literals, ite_false, false_and, false_and] at run
              have impossible := record_input_accepted (run := run)
              contradiction
          · simp only [show (3 : UInt32).toNat = 3 from rfl, header, ite_false] at run
            have impossible := record_input_accepted (run := run)
            contradiction
        · simp only [addition, ite_false] at run
          have impossible := record_input_accepted (run := run)
          contradiction
    · simp only [lrat_check.loop5, enter, decide_false, Bool.false_and, Bool.false_eq_true,
        ite_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq, true_and] at run
      rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨state, notEmpty⟩

end Oak.LRATChecker
