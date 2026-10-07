import Oak.LRATTrail

/-!
The complete production initial-clause traversal preserves every model of an
independently decoded input CNF. The decoder uses natural-number cursors and
has no mutable database, status, scratch, or execution fuel. The proof derives
machine bounds and live-variable validity from the actual framing and literal
checks. Whole proof-record traversal and entry-header composition remain open.
-/

set_option autoImplicit false

namespace Oak.LRATChecker

/-- Mathematical decoding of one input clause, without machine-index wrap. -/
def inputClause (words : Array UInt32) (at_ count : Nat) : RupCheck.Clause :=
  (List.range count).map (fun k => LRATRUP.decodeWord (words.getD (at_ + k) 0))

/-- Initial clauses are length-prefixed. This decoder describes their logical
content; the production traversal separately establishes the framing bounds. -/
def initialClauses (words : Array UInt32) (at_ : Nat) : Nat → List RupCheck.Clause
  | 0 => []
  | count + 1 =>
    let n := (words.getD at_ 0).toNat
    inputClause words (at_ + 1) n :: initialClauses words (at_ + 1 + n) count

theorem wordClause_eq_input (words : Array UInt32) (at_ n : UInt32)
    (bound : at_.toNat + n.toNat < 4294967296) :
    LRATRUP.wordClause words at_ n = inputClause words at_.toNat n.toNat := by
  unfold LRATRUP.wordClause inputClause
  apply List.map_congr_left
  intro k hk
  have kn := List.mem_range.mp hk
  have k32 : (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' (Nat.lt_trans kn n.toNat_lt)
  rw [add_exact at_ (UInt32.ofNat k) (by rw [k32]; omega), k32]

/-- A refused traversal cannot become accepted by exiting its loop. -/
theorem initial_input_accepted (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32)
    (status variables count store_words at_ end_ used : UInt32) (empty : Bool) (c : UInt32)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (at' used' : UInt32) (empty' : Bool) (c' : UInt32)
    (run : lrat_check.loop3 words starts lengths alive store status variables count store_words
      at_ end_ used empty c fuel = some (starts', lengths', alive', store', LRAT_ACCEPTED, at', used', empty', c')) :
    status = LRAT_ACCEPTED := by
  by_contra refused
  cases fuel with
  | zero => simp [lrat_check.loop3] at run
  | succ fuel =>
    simp only [lrat_check.loop3, beq_eq_false_iff_ne.mpr refused, Bool.and_false,
      Bool.false_eq_true, ite_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    exact refused run.2.2.2.2.1

/-- State sufficient for the next production clause or proof record, relative
to an arbitrary input model. Metadata capacities and cursor/store bounds are
preserved alongside semantic validity; no abstract propagation is assumed. -/
structure InitialState (words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (variables max_id store_words at_ end_ used : UInt32)
    (empty : Bool) (a : RupCheck.Assignment) : Prop where
  startCapacity : max_id.toNat < starts.size
  lengthCapacity : max_id.toNat < lengths.size
  aliveCapacity : max_id.toNat < alive.size
  storeCapacity : store_words.toNat ≤ store.size
  wordCapacity : end_.toNat ≤ words.size
  cursor : at_ ≤ end_
  usedBound : used ≤ store_words
  stored : StoredBefore starts lengths alive used max_id
  valid : LRATRUP.LiveVariables starts lengths alive store variables max_id
  models : RupCheck.Models a (LRATRUP.wordDatabase starts lengths alive store max_id)
  noEmpty : empty = false

/-- Compose every iteration of the extracted initial-clause parser with its
actual literal validation, store copy, and metadata writes. Every model of
the independently decoded remaining input survives the whole traversal. -/
theorem initial_loop_preserves (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32)
    (variables count max_id store_words at_ end_ used : UInt32) (empty : Bool) (c : UInt32)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (at' used' : UInt32) (empty' : Bool) (c' : UInt32)
    (a : RupCheck.Assignment)
    (countBound : count ≤ max_id) (noWrap : count.toNat + 1 < 4294967296)
    (positive : 0 < c) (progress : c.toNat ≤ count.toNat + 1)
    (state : InitialState words starts lengths alive store variables max_id store_words at_ end_ used empty a)
    (input : ∀ clause ∈ initialClauses words at_.toNat (count.toNat + 1 - c.toNat), RupCheck.SatisfiesClause a clause)
    (run : lrat_check.loop3 words starts lengths alive store LRAT_ACCEPTED variables count store_words
      at_ end_ used empty c fuel = some (starts', lengths', alive', store', LRAT_ACCEPTED, at', used', empty', c')) :
    InitialState words starts' lengths' alive' store' variables max_id store_words at' end_ used' empty' a ∧
      c'.toNat = count.toNat + 1 := by
  induction fuel generalizing starts lengths alive store at_ used empty c starts' lengths' alive' store' at' used' empty' c' with
  | zero => simp [lrat_check.loop3] at run
  | succ fuel ih =>
    by_cases advance : c ≤ count
    · have cn := UInt32.le_iff_toNat_le.mp advance
      have nextCounter : (c + 1).toNat = c.toNat + 1 := by
        simpa only [UInt32.toNat_one] using add_exact c 1 (by simp only [UInt32.toNat_one]; omega)
      simp only [lrat_check.loop3, advance, decide_true, beq_self_eq_true, Bool.and_self, ite_true] at run
      let n : UInt32 := if at_ < end_ then words.getD at_.toNat 0 else 0
      change (do
        let source ← lrat_fits (at_ + 1) n end_ fuel
        let dest ← lrat_fits used n store_words fuel
        let (s, l, v, t, status, cursor, u, e) ← (if ((decide (at_ < end_) && source) && dest) then (do
          let (t, status, _) ← lrat_check.loop4 words store LRAT_ACCEPTED variables at_ used n 0 fuel
          pure (starts.setIfInBounds c.toNat used, lengths.setIfInBounds c.toNat n,
            alive.setIfInBounds c.toNat 1, t, status, at_ + 1 + n, used + n, empty || (n == 0)))
          else pure (starts, lengths, alive, store, LRAT_MALFORMED, at_, used, empty))
        lrat_check.loop3 words s l v t status variables count store_words cursor end_ u e (c + 1) fuel) = _ at run
      cases sourceRun : lrat_fits (at_ + 1) n end_ fuel with
      | none => simp [sourceRun] at run
      | some source =>
        cases destRun : lrat_fits used n store_words fuel with
        | none => simp [sourceRun, destRun] at run
        | some dest =>
          simp only [sourceRun, destRun, bind, Option.bind, Option.pure_def] at run
          by_cases fits : ((decide (at_ < end_) && source) && dest) = true
          · have parts : at_ < end_ ∧ source = true ∧ dest = true := by simpa [and_assoc] using fits
            obtain ⟨header, rfl, rfl⟩ := parts
            simp only [fits, ite_true] at run
            cases scanRun : lrat_check.loop4 words store LRAT_ACCEPTED variables at_ used n 0 fuel with
            | none => simp [scanRun] at run
            | some result =>
              rcases result with ⟨nextStore, status, j⟩
              simp only [scanRun, bind, Option.bind, Option.pure_def] at run
              have accepted := initial_input_accepted fuel words _ _ _ _ status variables count store_words
                (at_ + 1 + n) end_ (used + n) (empty || (n == 0)) (c + 1)
                starts' lengths' alive' store' at' used' empty' c' run
              subst status
              obtain ⟨headerNext, src, src32, dst, dst32⟩ := initial_clause_bounds fuel words store
                at_ end_ used n store_words header state.wordCapacity state.storeCapacity sourceRun destRun
              have sourceBound := (fits_iff (at_ + 1) n end_ fuel).mp sourceRun
              have destBound := (fits_iff used n store_words fuel).mp destRun
              have nextAt := add_exact (at_ + 1) n src32
              have nextUsed := add_exact used n dst32
              have upper : c ≤ max_id := by
                rw [UInt32.le_iff_toNat_le] at countBound ⊢; omega
              have capS : c.toNat < starts.size := Nat.lt_of_le_of_lt (UInt32.le_iff_toNat_le.mp upper) state.startCapacity
              have capL : c.toNat < lengths.size := Nat.lt_of_le_of_lt (UInt32.le_iff_toNat_le.mp upper) state.lengthCapacity
              have capA : c.toNat < alive.size := Nat.lt_of_le_of_lt (UInt32.le_iff_toNat_le.mp upper) state.aliveCapacity
              obtain ⟨database, stored, valid⟩ := production_initial_clause fuel words store starts lengths alive
                variables max_id c used n at_ nextStore j state.stored state.valid positive upper
                capS capL capA dst dst32 src src32 scanRun
              obtain ⟨_, copy, _⟩ := initial_literal_scan_spec fuel words store LRAT_ACCEPTED variables at_ used n 0
                nextStore LRAT_ACCEPTED j scanRun rfl
              have size := (copy_loop_spec fuel words store used n (at_ + 1) 0 nextStore j (by simp)
                dst dst32 src src32 copy).2.1
              have nValue : n = words.getD at_.toNat 0 := if_pos header
              have remaining : count.toNat + 1 - c.toNat = (count.toNat + 1 - (c + 1).toNat) + 1 := by
                rw [nextCounter]; omega
              have decoded : initialClauses words at_.toNat (count.toNat + 1 - c.toNat) =
                  inputClause words (at_.toNat + 1) n.toNat ::
                  initialClauses words (at_ + 1 + n).toNat (count.toNat + 1 - (c + 1).toNat) := by
                rw [remaining, initialClauses, ← nValue, nextAt, headerNext]
              have headModel := input _ (by rw [decoded]; exact List.mem_cons_self)
              have clauseModel : RupCheck.SatisfiesClause a (LRATRUP.wordClause words (at_ + 1) n) := by
                rw [wordClause_eq_input words (at_ + 1) n src32, headerNext]
                exact headModel
              have nonempty : n ≠ 0 := by
                intro zero
                subst n
                simpa [LRATRUP.wordClause, RupCheck.SatisfiesClause] using clauseModel
              have nextState : InitialState words (starts.setIfInBounds c.toNat used)
                  (lengths.setIfInBounds c.toNat n) (alive.setIfInBounds c.toNat 1) nextStore
                  variables max_id store_words (at_ + 1 + n) end_ (used + n) (empty || (n == 0)) a := by
                refine ⟨by simpa using state.startCapacity, by simpa using state.lengthCapacity,
                  by simpa using state.aliveCapacity, by omega, state.wordCapacity,
                  ?_, ?_, stored, valid, ?_, ?_⟩
                · rw [UInt32.le_iff_toNat_le, nextAt]; exact sourceBound
                · rw [UInt32.le_iff_toNat_le, nextUsed]; exact destBound
                · rw [database]
                  exact RupCheck.insert_preserves state.models clauseModel
                · simp [state.noEmpty, nonempty]
              apply ih _ _ _ _ (at_ + 1 + n) (used + n) _ (c + 1) _ _ _ _ _ _ _ _
                (by rw [UInt32.lt_iff_toNat_lt, nextCounter]; omega)
                (by rw [nextCounter]; omega) nextState _ run
              intro clause member
              apply input clause
              rw [decoded]
              exact List.mem_cons_of_mem _ member
          · simp only [fits, Bool.false_eq_true, ite_false] at run
            have impossible := initial_input_accepted fuel words starts lengths alive store LRAT_MALFORMED
              variables count store_words at_ end_ used empty (c + 1)
              starts' lengths' alive' store' at' used' empty' c' run
            contradiction
    · simp only [lrat_check.loop3, decide_eq_false advance, Bool.false_and, Bool.false_eq_true,
        ite_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl⟩
      refine ⟨state, ?_⟩
      rw [UInt32.le_iff_toNat_le] at advance
      omega

/-- The actual assignment initializer has enough fuel whenever it returns. -/
theorem assignment_loop_fuel (fuel : Nat) (assign : Array UInt8) (variables i : UInt32)
    (result : Array UInt8) (finish : UInt32) (lower : i ≤ variables)
    (run : lrat_check.loop2 assign true variables i fuel = some (result, finish)) :
    variables.toNat - i.toNat < fuel := by
  induction fuel generalizing assign i result finish with
  | zero => simp [lrat_check.loop2] at run
  | succ fuel ih =>
    by_cases advance : i < variables
    · simp only [lrat_check.loop2, advance, decide_true, Bool.and_self, ite_true] at run
      have next := LRATRUP.counter_succ i variables advance
      have bound := UInt32.lt_iff_toNat_lt.mp advance
      have enough := ih _ (i + 1) result finish
        (by rw [UInt32.le_iff_toNat_le, next]; omega) run
      omega
    · rw [UInt32.lt_iff_toNat_lt] at advance
      omega

/-- Derive empty-database state from the completed production live reset;
there is no caller-supplied zero-live or stored-clause invariant. -/
theorem initial_state_from_reset (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (variables max_id store_words at_ end_ : UInt32)
    (reset : Array UInt8) (finish : UInt32) (a : RupCheck.Assignment)
    (startCap : max_id.toNat < starts.size) (lengthCap : max_id.toNat < lengths.size)
    (aliveCap : max_id < alive.size.toUInt32) (storeCap : store_words.toNat ≤ store.size)
    (wordCap : end_.toNat ≤ words.size) (cursor : at_ ≤ end_)
    (run : lrat_check.loop1 alive true max_id 0 fuel = some (reset, finish)) :
    InitialState words starts lengths reset store variables max_id store_words at_ end_ 0 false a := by
  have maxBound : max_id < 4294967295 := by
    have := alive.size.toUInt32.toNat_lt
    rw [UInt32.lt_iff_toNat_lt] at aliveCap ⊢
    change max_id.toNat < 4294967295
    omega
  have next := LRATRUP.counter_succ max_id 4294967295 maxBound
  have resetRun := run
  rw [live_loop_as_assignment fuel alive max_id 0 maxBound] at resetRun
  have enough := assignment_loop_fuel fuel alive (max_id + 1) 0 reset finish (by simp) resetRun
  obtain ⟨expected, execution, size, zero⟩ := live_init_spec alive max_id fuel aliveCap (by simpa [next] using enough)
  rw [execution] at run
  cases run
  have capacity : max_id.toNat < alive.size := by
    have wrap : alive.size.toUInt32.toNat ≤ alive.size := Nat.mod_le _ _
    have := UInt32.lt_iff_toNat_lt.mp aliveCap
    omega
  refine ⟨startCap, lengthCap, by omega, storeCap, wordCap, cursor, by simp, ?_, ?_, ?_, rfl⟩
  · intro id lower upper live
    exact False.elim (live (zero id upper))
  · intro id upper lower live k hk
    exact False.elim (live (zero id.toNat (UInt32.le_iff_toNat_le.mp upper)))
  · rw [initialized_database_empty starts lengths expected store max_id zero]
    intro id clause impossible
    contradiction

end Oak.LRATChecker
