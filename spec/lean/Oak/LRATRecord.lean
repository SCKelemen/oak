import Oak.LRATInitial

/-!
Production proof-record transition invariants. The actual framing predicates
supply non-wrapping cursors and copy ranges. Deletion and accepted RUP/copy
transitions preserve every current model, live-store validity, capacities,
and zero scratch. The outer record-loop induction remains separate.
-/

set_option autoImplicit false
namespace Oak.LRATChecker

private theorem three_nat : (3 : UInt32).toNat = 3 := by decide

/-- The fixed header and variable deletion body advance within the endpoint,
including an empty deletion body. Neither machine addition can wrap. -/
theorem deletion_record_bounds (fuel : Nat) (at_ k end_ : UInt32)
    (header : lrat_fits at_ 3 end_ fuel = some true)
    (body : lrat_fits (at_ + 3) k end_ fuel = some true) :
    (at_ + 3 + k).toNat = at_.toNat + 3 + k.toNat ∧
      at_ < at_ + 3 + k ∧ at_ + 3 + k ≤ end_ := by
  have head := (fits_iff at_ 3 end_ fuel).mp header
  have tail := (fits_iff (at_ + 3) k end_ fuel).mp body
  have limit := end_.toNat_lt
  simp only [three_nat] at head
  have start : (at_ + 3).toNat = at_.toNat + 3 := by
    simpa only [three_nat] using add_exact at_ 3 (by simp only [three_nat]; omega)
  have finish := add_exact (at_ + 3) k (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [UInt32.lt_iff_toNat_lt]; omega
  · rw [UInt32.le_iff_toNat_le]; omega

structure AdditionBounds (words store : Array UInt32) (at_ n m used store_words end_ : UInt32) : Prop where
  source : (at_ + 3).toNat + n.toNat ≤ words.size
  source32 : (at_ + 3).toNat + n.toNat < 4294967296
  dest : used.toNat + n.toNat ≤ store.size
  dest32 : used.toNat + n.toNat < 4294967296
  cursorExact : (at_ + 3 + n + 1 + m).toNat = at_.toNat + 3 + n.toNat + 1 + m.toNat
  advance : at_ < at_ + 3 + n + 1 + m
  cursorBound : at_ + 3 + n + 1 + m ≤ end_
  usedBound : used + n ≤ store_words

/-- All ranges consumed by an accepted addition come from the production
header, literal-body, hint-count-word, hint-body, and store checks. -/
theorem addition_record_bounds (fuel : Nat) (words store : Array UInt32)
    (at_ n m used store_words end_ : UInt32)
    (wordCapacity : end_.toNat ≤ words.size) (storeCapacity : store_words.toNat ≤ store.size)
    (header : lrat_fits at_ 3 end_ fuel = some true)
    (literals : lrat_fits (at_ + 3) n end_ fuel = some true)
    (countWord : at_ + 3 + n < end_)
    (hints : lrat_fits (at_ + 3 + n + 1) m end_ fuel = some true)
    (space : lrat_fits used n store_words fuel = some true) :
    AdditionBounds words store at_ n m used store_words end_ := by
  have head := (fits_iff at_ 3 end_ fuel).mp header
  have lits := (fits_iff (at_ + 3) n end_ fuel).mp literals
  have tail := (fits_iff (at_ + 3 + n + 1) m end_ fuel).mp hints
  have capacity := (fits_iff used n store_words fuel).mp space
  have limit := end_.toNat_lt
  have storeLimit := store_words.toNat_lt
  simp only [three_nat] at head
  have start : (at_ + 3).toNat = at_.toNat + 3 := by
    simpa only [three_nat] using add_exact at_ 3 (by simp only [three_nat]; omega)
  have litEnd := add_exact (at_ + 3) n (by omega)
  have hn := UInt32.lt_iff_toNat_lt.mp countWord
  have hintStart := LRATRUP.counter_succ (at_ + 3 + n) end_ countWord
  have finish := add_exact (at_ + 3 + n + 1) m (by omega)
  have nextUsed := add_exact used n (by omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rw [UInt32.lt_iff_toNat_lt]; omega
  · rw [UInt32.le_iff_toNat_le]; omega
  · rw [UInt32.le_iff_toNat_le]; omega

/-- Shared induction state for proof records under a putative input model. -/
structure RecordState (words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id store_words at_ end_ used : UInt32) (empty : Bool)
    (a : RupCheck.Assignment) : Prop where
  database : InitialState words starts lengths alive store variables max_id store_words at_ end_ used empty a
  assignCapacity : variables.toNat ≤ assign.size
  trailCapacity : variables.toNat ≤ trail.size
  zero : ∀ v, v < variables.toNat → assign.getD v 0 = 0

/-- A production deletion preserves the complete record invariant, including
on partial refusal; the caller's status handling still decides continuation. -/
theorem deletion_record_state (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id store_words at_ end_ used k status : UInt32) (empty : Bool)
    (alive' : Array UInt8) (status' d' : UInt32) (a : RupCheck.Assignment)
    (state : RecordState words starts lengths alive store assign trail variables max_id store_words at_ end_ used empty a)
    (header : lrat_fits at_ 3 end_ fuel = some true)
    (body : lrat_fits (at_ + 3) k end_ fuel = some true)
    (run : lrat_check.loop6 words alive status max_id at_ k 0 fuel = some (alive', status', d')) :
    RecordState words starts lengths alive' store assign trail variables max_id store_words (at_ + 3 + k) end_ used empty a := by
  obtain ⟨_, _, cursor⟩ := deletion_record_bounds fuel at_ k end_ header body
  obtain ⟨size, subset⟩ := deletion_loop_subset fuel words alive status max_id at_ k 0 alive' status' d' run
  refine ⟨?_, state.assignCapacity, state.trailCapacity, state.zero⟩
  refine ⟨state.database.startCapacity, state.database.lengthCapacity,
    by simpa only [size] using state.database.aliveCapacity,
    state.database.storeCapacity, state.database.wordCapacity, cursor, state.database.usedBound,
    ?_, ?_, ?_, state.database.noEmpty⟩
  · intro id lower upper live
    exact state.database.stored id lower upper (subset id live)
  · exact deletion_preserves_variables fuel words starts lengths alive store status variables max_id at_ k 0
      alive' status' d' run state.database.valid
  · exact deletion_preserves_models fuel words starts lengths alive store status max_id at_ k 0
      alive' status' d' run a state.database.models

/-- Accepted production addition with the actual parser framing checks,
RUP execution, and store copy preserves all record-loop invariants. -/
theorem addition_record_state (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id store_words at_ end_ used id last n m : UInt32) (empty : Bool)
    (rupStarts rupLengths : Array UInt32) (rupAlive : Array UInt8) (rupStore : Array UInt32)
    (rupAssign : Array UInt8) (rupTrail : Array UInt32) (store' : Array UInt32) (j' : UInt32)
    (a : RupCheck.Assignment)
    (state : RecordState words starts lengths alive store assign trail variables max_id store_words at_ end_ used empty a)
    (order : id > last) (upper : id ≤ max_id)
    (header : lrat_fits at_ 3 end_ fuel = some true)
    (literals : lrat_fits (at_ + 3) n end_ fuel = some true)
    (countWord : at_ + 3 + n < end_)
    (hints : lrat_fits (at_ + 3 + n + 1) m end_ fuel = some true)
    (space : lrat_fits used n store_words fuel = some true)
    (rup : lrat_rup words (at_ + 3) n (at_ + 3 + n + 1) m starts lengths alive store assign trail variables max_id fuel =
      some (LRAT_ACCEPTED, rupStarts, rupLengths, rupAlive, rupStore, rupAssign, rupTrail))
    (copy : lrat_check.loop7 words rupStore used n (at_ + 3) 0 fuel = some (store', j')) :
    RecordState words (rupStarts.setIfInBounds id.toNat used) (rupLengths.setIfInBounds id.toNat n)
      (rupAlive.setIfInBounds id.toNat 1) store' rupAssign rupTrail variables max_id store_words
      (at_ + 3 + n + 1 + m) end_ (used + n) (empty || (n == 0)) a := by
  have bounds := addition_record_bounds fuel words store at_ n m used store_words end_
    state.database.wordCapacity state.database.storeCapacity header literals countWord hints space
  have positive : 0 < id := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_zero]
    have := UInt32.lt_iff_toNat_lt.mp order
    omega
  have un := UInt32.le_iff_toNat_le.mp upper
  have capS := Nat.lt_of_le_of_lt un state.database.startCapacity
  have capL := Nat.lt_of_le_of_lt un state.database.lengthCapacity
  have capA := Nat.lt_of_le_of_lt un state.database.aliveCapacity
  obtain ⟨sameS, sameL, sameA, sameStore⟩ := rup_database_unchanged fuel words (at_ + 3) n (at_ + 3 + n + 1) m
    starts lengths alive store assign trail variables max_id LRAT_ACCEPTED rupStarts rupLengths rupAlive rupStore rupAssign rupTrail rup
  subst rupStarts rupLengths rupAlive rupStore
  obtain ⟨stored, valid, storeSize, assignSize, trailSize, zero⟩ := production_addition_state fuel words store starts lengths alive
    assign trail variables max_id id used n (at_ + 3) (at_ + 3 + n + 1) m starts lengths alive store rupAssign rupTrail store' j'
    state.assignCapacity state.trailCapacity state.zero state.database.stored state.database.valid capS capL
    bounds.dest bounds.dest32 bounds.source bounds.source32 rup copy
  have models := production_addition_preserves_models fuel words store starts lengths alive assign trail variables max_id
    id used n (at_ + 3) (at_ + 3 + n + 1) m starts lengths alive store rupAssign rupTrail store' j'
    state.database.stored state.database.valid state.assignCapacity state.zero positive upper capS capL capA
    bounds.dest bounds.dest32 bounds.source bounds.source32 rup copy a state.database.models
  have nonempty : n ≠ 0 := by
    have execution := rup
    rw [rup_extraction_eq] at execution
    have clause := LRATRUP.production_rup_entails fuel words (at_ + 3) n (at_ + 3 + n + 1) m starts lengths alive store
      assign trail variables max_id state.assignCapacity state.zero state.database.valid starts lengths alive store
      rupAssign rupTrail execution a state.database.models
    intro emptyClause
    rw [emptyClause] at clause
    simpa [LRATRUP.wordClause, RupCheck.SatisfiesClause] using clause
  refine ⟨?_, by simpa only [assignSize] using state.assignCapacity,
    by simpa only [trailSize] using state.trailCapacity, zero⟩
  exact ⟨by simpa using state.database.startCapacity, by simpa using state.database.lengthCapacity,
    by simpa using state.database.aliveCapacity, by simpa only [storeSize] using state.database.storeCapacity,
    state.database.wordCapacity, bounds.cursorBound, bounds.usedBound, stored, valid, models,
    by simp [state.database.noEmpty, nonempty]⟩

/-- Once the outer proof loop is refused, it cannot exit with acceptance.
All parameters are implicit so parser branches can use the observed run. -/
theorem record_input_accepted {fuel : Nat} {words starts lengths : Array UInt32}
    {alive : Array UInt8} {store : Array UInt32} {assign : Array UInt8} {trail : Array UInt32}
    {status additions deletions variables max_id store_words at_ end_ used : UInt32} {empty : Bool} {last : UInt32}
    {starts' lengths' : Array UInt32} {alive' : Array UInt8} {store' : Array UInt32}
    {assign' : Array UInt8} {trail' : Array UInt32}
    {additions' deletions' at' used' : UInt32} {empty' : Bool} {last' : UInt32}
    (run : lrat_check.loop5 words starts lengths alive store assign trail status additions deletions variables max_id
      store_words at_ end_ used empty last fuel =
      some (starts', lengths', alive', store', assign', trail', LRAT_ACCEPTED, additions', deletions', at', used', empty', last')) :
    status = LRAT_ACCEPTED := by
  apply Classical.byContradiction
  intro refused
  cases fuel with
  | zero => simp [lrat_check.loop5] at run
  | succ fuel =>
    simp only [lrat_check.loop5, beq_eq_false_iff_ne.mpr refused, Bool.and_false, Bool.false_eq_true,
      ite_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    exact refused run.2.2.2.2.2.2.1

end Oak.LRATChecker
