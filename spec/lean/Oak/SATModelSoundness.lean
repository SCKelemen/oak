import Oak.SATModel

/-!
# Soundness of the extracted production SAT-model checker

Validation status at introduction: this proof awaits its first successful
Lean kernel build. `TestOakSATModelSoundnessLean` is mandatory in formal CI;
the loop-refinement obligation stays open until that gate passes.

The hypotheses are execution of `sat_check_model` and representable Oak view
lengths. The proof derives the assignment invariant, exact clause decoding,
complete input consumption, and a model of that decoded database. Neither a
solver verdict nor an assumed correspondence between the scan and a model is
used. Fuel exhaustion cannot satisfy the successful-execution hypothesis.

This is a theorem about the extracted UInt32/Array program. Correct extraction,
compilation, native memory access, and source-to-CNF lowering remain separate
parts of the end-to-end verification chain.
-/

set_option autoImplicit false

namespace Oak.SATModel

private theorem two_nat : (2 : UInt32).toNat = 2 := by decide

private theorem header_nat : LRAT_HEADER_WORDS.toNat = 8 := by decide

private theorem counter_succ (i limit : UInt32) (h : i < limit) :
    (i + 1).toNat = i.toNat + 1 := by
  have := limit.toNat_lt
  rw [UInt32.lt_iff_toNat_lt] at h
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt (by change i.toNat + 1 < 4294967296; omega)

private theorem size_exact (n : Nat) (h : n < 4294967296) :
    n.toUInt32.toNat = n := Nat.mod_eq_of_lt h

private theorem add_exact (a b : UInt32) (h : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt h

def ValueValid (value : UInt32) : Prop := value = 1 ∨ value = 2

/-- Success validates the whole suffix, and cannot recover from a false
admission flag. The counter reaches the declared endpoint without wrapping. -/
theorem assignment_loop_sound (fuel : Nat) (values : Array UInt32)
    (valid : Bool) (i finish : UInt32) (bound : i ≤ values.size.toUInt32)
    (run : sat_check_model.loop1 values valid i fuel = some (true, finish)) :
    valid = true ∧ finish = values.size.toUInt32 ∧
      ∀ k, i.toNat ≤ k → k < values.size.toUInt32.toNat → ValueValid (values.getD k 0) := by
  induction fuel generalizing valid i finish with
  | zero => simp [sat_check_model.loop1] at run
  | succ fuel ih =>
    cases valid with
    | false => simp [sat_check_model.loop1] at run
    | true =>
      by_cases step : i < values.size.toUInt32
      · have successor := counter_succ i values.size.toUInt32 step
        have stepNat := UInt32.lt_iff_toNat_lt.mp step
        have nextBound : i + 1 ≤ values.size.toUInt32 := by
          rw [UInt32.le_iff_toNat_le, successor]
          omega
        simp only [sat_check_model.loop1, Bool.true_and, step, decide_true,
          ite_true, sat_model_value, bind, Option.bind, Option.pure_def] at run
        obtain ⟨checked, endpoint, suffix⟩ := ih _ (i + 1) finish nextBound run
        have current : ValueValid (values.getD i.toNat 0) := by
          simpa [ValueValid] using checked
        refine ⟨rfl, endpoint, ?_⟩
        intro k lower upper
        by_cases same : k = i.toNat
        · simpa [same] using current
        · exact suffix k (by rw [successor]; omega) upper
      · have endpoint : i = values.size.toUInt32 := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.le_iff_toNat_le] at bound
          rw [UInt32.lt_iff_toNat_lt] at step
          omega
        subst i
        have returned : values.size.toUInt32 = finish := by
          simpa [sat_check_model.loop1] using run
        exact ⟨rfl, returned.symm, by intro k lower upper; omega⟩

def arrayAssignment (values : Array UInt32) : RupCheck.Assignment :=
  fun index => values.getD index 0 == 2

def literalTest (word value : UInt32) : Bool :=
  if word % 2 == 1 then value == 2 else value == 1

private theorem literal_spec (word value : UInt32) (fuel : Nat) :
    sat_model_literal word value fuel = some (literalTest word value) := rfl

private theorem literal_test_sound (values : Array UInt32) (word : UInt32)
    (holds : literalTest word (values.getD (word / 2).toNat 0) = true) :
    RupCheck.Holds (arrayAssignment values) (literal word) := by
  apply literal_value_sound word (values.getD (word / 2).toNat 0) 0
  rw [literal_spec, holds]

/-- A witness names an actual offset smaller than the declared clause size.
The outer scan separately proves that these machine addresses do not wrap. -/
def ClauseWitness (formula values : Array UInt32) (at_ count : UInt32) : Prop :=
  ∃ k : UInt32, k < count ∧
    RupCheck.Holds (arrayAssignment values) (literal (formula.getD (at_ + k).toNat 0))

/-- The literal loop only accumulates genuine witnesses. A false validity
flag cannot become true, even if an earlier literal has already satisfied
the clause. This theorem follows the generated loop at every fuel. -/
theorem literal_loop_sound (fuel : Nat) (formula values : Array UInt32)
    (valid satisfied : Bool) (at_ count j finish : UInt32)
    (run : sat_check_model.loop3 formula values valid at_ count satisfied j fuel =
      some (true, true, finish)) :
    valid = true ∧ (satisfied = true ∨ ClauseWitness formula values at_ count) := by
  induction fuel generalizing valid satisfied j finish with
  | zero => simp [sat_check_model.loop3] at run
  | succ fuel ih =>
    cases valid with
    | false => simp [sat_check_model.loop3] at run
    | true =>
      by_cases step : j < count
      · generalize wordAt : formula.getD (at_ + j).toNat 0 = word at *
        by_cases inside : word / 2 < values.size.toUInt32
        · simp only [sat_check_model.loop3, Bool.true_and, step, decide_true,
            ite_true, wordAt, inside, literal_spec, bind, Option.bind,
            Option.pure_def] at run
          obtain ⟨_, witness⟩ := ih true _ (j + 1) finish run
          refine ⟨rfl, ?_⟩
          rcases witness with accumulated | existing
          · rcases Bool.or_eq_true_iff.mp accumulated with current | earlier
            · right
              refine ⟨j, step, ?_⟩
              rw [wordAt]
              exact literal_test_sound values word current
            · exact Or.inl earlier
          · exact Or.inr existing
        · simp only [sat_check_model.loop3, Bool.true_and, step, decide_true,
            ite_true, wordAt, inside, decide_false, Bool.false_eq_true,
            ite_false, bind, Option.bind, Option.pure_def] at run
          have impossible := (ih false satisfied (j + 1) finish run).1
          contradiction
      · have returned : satisfied = true ∧ j = finish := by
          simpa [sat_check_model.loop3, step] using run
        exact ⟨rfl, Or.inl returned.1⟩

/-- Literal words in ordinary, non-wrapping address order. -/
def rawClause (formula : Array UInt32) (at_ count : Nat) : List UInt32 :=
  (List.range count).map (fun k => formula.getD (at_ + k) 0)

private theorem witness_satisfies (formula values : Array UInt32) (at_ count : UInt32)
    (fits : at_.toNat + count.toNat ≤ formula.size)
    (size : formula.size < 4294967296)
    (witness : ClauseWitness formula values at_ count) :
    RupCheck.SatisfiesClause (arrayAssignment values)
      ((rawClause formula at_.toNat count.toNat).map literal) := by
  obtain ⟨k, inside, holds⟩ := witness
  have index := UInt32.lt_iff_toNat_lt.mp inside
  have address := add_exact at_ k (by omega)
  rw [address] at holds
  refine ⟨literal (formula.getD (at_.toNat + k.toNat) 0), ?_, holds⟩
  apply List.mem_map.mpr
  refine ⟨formula.getD (at_.toNat + k.toNat) 0, ?_, rfl⟩
  exact List.mem_map.mpr ⟨k.toNat, List.mem_range.mpr index, rfl⟩

/-- Independent exact decoder: ordinary natural-number offsets, one count
word per clause, no wrapping and no ignored suffix within a clause. -/
def decodeClauses (formula : Array UInt32) (at_ : Nat) :
    Nat → Option (List (List UInt32) × Nat)
  | 0 => some ([], at_)
  | remaining + 1 =>
      if at_ < formula.size then
        let count := (formula.getD at_ 0).toNat
        if at_ + 1 + count ≤ formula.size then do
          let (rest, finish) ← decodeClauses formula (at_ + 1 + count) remaining
          pure (rawClause formula (at_ + 1) count :: rest, finish)
        else none
      else none

def ClausesHold (values : Array UInt32) (clauses : List (List UInt32)) : Prop :=
  ∀ clause ∈ clauses,
    RupCheck.SatisfiesClause (arrayAssignment values) (clause.map literal)

/-- Successful outer scanning constructs the exact independent decoding and
establishes every decoded clause. Its premise is the generated loop's run. -/
theorem clause_loop_sound (fuel : Nat) (formula values : Array UInt32)
    (size : formula.size < 4294967296) (valid : Bool)
    (at_ clause finish finalClause : UInt32)
    (bound : clause ≤ formula.getD 2 0)
    (run : sat_check_model.loop2 formula values valid at_ clause fuel =
      some (true, finish, finalClause)) :
    valid = true ∧ finalClause = formula.getD 2 0 ∧
      ∃ clauses,
        decodeClauses formula at_.toNat ((formula.getD 2 0).toNat - clause.toNat) =
          some (clauses, finish.toNat) ∧ ClausesHold values clauses := by
  induction fuel generalizing valid at_ clause finish finalClause with
  | zero => simp [sat_check_model.loop2] at run
  | succ fuel ih =>
    cases valid with
    | false => simp [sat_check_model.loop2] at run
    | true =>
      by_cases step : clause < formula.getD 2 0
      · have successor := counter_succ clause (formula.getD 2 0) step
        have stepNat := UInt32.lt_iff_toNat_lt.mp step
        have nextBound : clause + 1 ≤ formula.getD 2 0 := by
          rw [UInt32.le_iff_toNat_le, successor]
          omega
        have remaining : (formula.getD 2 0).toNat - clause.toNat =
            ((formula.getD 2 0).toNat - (clause + 1).toNat) + 1 := by omega
        by_cases header : at_ < formula.size.toUInt32
        · let count := formula.getD at_.toNat 0
          let body := at_ + 1
          have countEq : count = formula.getD at_.toNat 0 := rfl
          have bodyEq : body = at_ + 1 := rfl
          have bodyNat : body.toNat = at_.toNat + 1 := counter_succ at_ _ header
          have headerNat : at_.toNat < formula.size := by
            rw [UInt32.lt_iff_toNat_lt, size_exact _ size] at header
            exact header
          cases scan : sat_check_model.loop3 formula values
              (decide (count ≤ formula.size.toUInt32 - body)) body count false 0 fuel with
          | none =>
              simp only [sat_check_model.loop2, two_nat, Bool.true_and, step, decide_true,
                ite_true, header, ← countEq, ← bodyEq, scan,
                bind, Option.bind, Option.pure_def, reduceCtorEq] at run
          | some result =>
              rcases result with ⟨scanValid, satisfied, endLiteral⟩
              by_cases accepted : (scanValid && satisfied) = true
              · obtain ⟨rfl, rfl⟩ := Bool.and_eq_true_iff.mp accepted
                obtain ⟨fitsWord, witness⟩ := literal_loop_sound fuel formula values
                  _ false body count 0 endLiteral scan
                have fits : count ≤ formula.size.toUInt32 - body := of_decide_eq_true fitsWord
                have bodyBound : body ≤ formula.size.toUInt32 := by
                  rw [UInt32.le_iff_toNat_le, bodyNat, size_exact _ size]
                  omega
                have room : body.toNat + count.toNat ≤ formula.size := by
                  rw [UInt32.le_iff_toNat_le,
                    UInt32.toNat_sub_of_le _ _ bodyBound, size_exact _ size] at fits
                  omega
                have endpoint : (body + count).toNat = body.toNat + count.toNat :=
                  add_exact body count (by omega)
                have current : RupCheck.SatisfiesClause (arrayAssignment values)
                    ((rawClause formula body.toNat count.toNat).map literal) := by
                  apply witness_satisfies formula values body count room size
                  exact witness.resolve_left (by decide)
                simp only [sat_check_model.loop2, two_nat, Bool.true_and, step, decide_true,
                  ite_true, header, ← countEq, ← bodyEq, scan, Bool.and_self,
                  bind, Option.bind, Option.pure_def] at run
                obtain ⟨_, endCount, clauses, decoded, holds⟩ :=
                  ih true (body + count) (clause + 1) finish finalClause nextBound run
                refine ⟨rfl, endCount, rawClause formula body.toNat count.toNat :: clauses, ?_, ?_⟩
                · rw [remaining, decodeClauses, if_pos headerNat]
                  have roomNat : at_.toNat + 1 + (formula.getD at_.toNat 0).toNat ≤ formula.size := by
                    simpa only [← countEq, ← bodyNat] using room
                  rw [if_pos roomNat]
                  simpa only [← countEq, ← bodyNat, ← endpoint, decoded,
                    bind, Option.bind, Option.pure_def]
                · intro target member
                  rcases List.mem_cons.mp member with same | tail
                  · simpa [same] using current
                  · exact holds target tail
              · have refused : (scanValid && satisfied) = false := Bool.eq_false_iff.mpr accepted
                simp only [sat_check_model.loop2, two_nat, Bool.true_and, step, decide_true,
                  ite_true, header, ← countEq, ← bodyEq, scan, refused,
                  Bool.false_eq_true, ite_false, bind, Option.bind, Option.pure_def] at run
                have impossible := (ih false body (clause + 1) finish finalClause nextBound run).1
                contradiction
        · simp only [sat_check_model.loop2, two_nat, Bool.true_and, step, decide_true,
            ite_true, header, decide_false, Bool.false_eq_true, ite_false,
            bind, Option.bind, Option.pure_def] at run
          have impossible := (ih false at_ (clause + 1) finish finalClause nextBound run).1
          contradiction
      · have same : clause = formula.getD 2 0 := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.le_iff_toNat_le] at bound
          rw [UInt32.lt_iff_toNat_lt] at step
          omega
        have returned : at_ = finish ∧ clause = finalClause := by
          simpa only [sat_check_model.loop2, two_nat, Bool.true_and, step,
            decide_false, Bool.false_eq_true, ite_false, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq, true_and] using run
        rcases returned with ⟨rfl, rfl⟩
        exact ⟨rfl, same, [], by simp [same, decodeClauses], by simp [ClausesHold]⟩

/-- The entry framing flag, written in the same association as the generated
program. Scalar header fields are not assumed valid by the soundness theorem. -/
def headerValid (formula values : Array UInt32) : Bool :=
  (((decide (formula.size.toUInt32 ≥ LRAT_HEADER_WORDS) &&
    (formula.getD 0 0 == LRAT_MAGIC)) && (formula.getD 4 0 == 0)) &&
    (formula.getD 3 0 == formula.size.toUInt32 - LRAT_HEADER_WORDS)) &&
    (formula.getD 1 0 == values.size.toUInt32)

/-- Proof-free formula framing, interpreted with natural lengths. -/
def Framed (formula : Array UInt32) : Prop :=
  8 ≤ formula.size ∧ formula.getD 0 0 = LRAT_MAGIC ∧
    formula.getD 4 0 = 0 ∧ (formula.getD 3 0).toNat = formula.size - 8

instance (formula : Array UInt32) : Decidable (Framed formula) := by
  unfold Framed
  infer_instance

private theorem header_sound (formula values : Array UInt32)
    (size : formula.size < 4294967296) (valueSize : values.size < 4294967296)
    (accepted : headerValid formula values = true) :
    Framed formula ∧ (formula.getD 1 0).toNat = values.size := by
  simp only [headerValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  obtain ⟨⟨⟨⟨length, magic⟩, proof⟩, body⟩, variables⟩ := accepted
  have lengthNat : 8 ≤ formula.size := by
    simpa only [ge_iff_le, UInt32.le_iff_toNat_le, size_exact _ size,
      header_nat] using length
  have bodyNat := congrArg UInt32.toNat body
  rw [UInt32.toNat_sub_of_le _ _ length, size_exact _ size] at bodyNat
  refine ⟨⟨lengthNat, magic, proof, ?_⟩, ?_⟩
  · simpa only [header_nat] using bodyNat
  · rw [variables, size_exact _ valueSize]

/-- Exact independent formula decoding, including its header and endpoint. -/
def decodeFormula (formula : Array UInt32) : Option (List (List UInt32)) := do
  if Framed formula then
    let (clauses, finish) ← decodeClauses formula 8 (formula.getD 2 0).toNat
    if finish = formula.size then pure clauses else none
  else none

private theorem clauses_model (values : Array UInt32) (clauses : List (List UInt32))
    (holds : ClausesHold values clauses) :
    RupCheck.Models (arrayAssignment values) (database clauses) := by
  intro id clause found
  unfold database at found
  split at found
  · contradiction
  · cases lookup : clauses[id - 1]? with
    | none => simp [lookup] at found
    | some words =>
        have equal : words.map literal = clause := by simpa [lookup] using found
        rw [← equal]
        exact holds words (List.mem_of_getElem? lookup)

/-- Successful execution of the complete extracted checker supplies a model
of the exact, completely consumed formula. View-size assumptions express the
UInt32 length domain of Oak slices; no decoding or model-soundness assumption
is supplied by the caller. -/
theorem production_model_sound (formula values : Array UInt32) (fuel : Nat)
    (formulaSize : formula.size < 4294967296) (valueSize : values.size < 4294967296)
    (accepted : sat_check_model formula values fuel = some true) :
    Framed formula ∧ (formula.getD 1 0).toNat = values.size ∧
    (∀ k, k < values.size → ValueValid (values.getD k 0)) ∧
    ∃ clauses, decodeFormula formula = some clauses ∧
      RupCheck.Models (arrayAssignment values) (database clauses) := by
  change (do
    let (valid, _) ← sat_check_model.loop1 values (headerValid formula values) 0 fuel
    let (valid, at_, _) ← sat_check_model.loop2 formula values valid LRAT_HEADER_WORDS 0 fuel
    pure (valid && (at_ == formula.size.toUInt32))) = some true at accepted
  cases initialized : sat_check_model.loop1 values (headerValid formula values) 0 fuel with
  | none => simp [initialized] at accepted
  | some first =>
    rcases first with ⟨initialValid, initialEnd⟩
    cases scanned : sat_check_model.loop2 formula values initialValid LRAT_HEADER_WORDS 0 fuel with
    | none => simp [initialized, scanned] at accepted
    | some last =>
      rcases last with ⟨finalValid, finish, finalClause⟩
      simp only [initialized, scanned, bind, Option.bind, Option.pure_def,
        Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at accepted
      obtain ⟨rfl, endpoint⟩ := accepted
      obtain ⟨initialTrue, _, clauses, decoded, holds⟩ := clause_loop_sound fuel formula values
        formulaSize initialValid LRAT_HEADER_WORDS 0 finish finalClause (by simp) scanned
      subst initialValid
      obtain ⟨header, _, validValues⟩ := assignment_loop_sound fuel values
        (headerValid formula values) 0 initialEnd (by simp) initialized
      obtain ⟨framed, variables⟩ := header_sound formula values formulaSize valueSize header
      refine ⟨framed, variables, ?_, clauses, ?_, clauses_model values clauses holds⟩
      · intro k bound
        exact validValues k (by simp) (by simpa only [size_exact _ valueSize] using bound)
      · have exactDecode : decodeClauses formula 8 (formula.getD 2 0).toNat =
            some (clauses, formula.size) := by
          simpa only [header_nat, UInt32.toNat_zero, Nat.sub_zero, endpoint, size_exact _ formulaSize] using decoded
        simp only [decodeFormula, if_pos framed, exactDecode, bind, Option.bind,
          Option.pure_def, ite_true]

/-- The production checker and an accepted RUP refutation cannot both accept
the very same decoded formula. This composes execution with the logical RUP
soundness theorem without assuming the SAT solver correct. -/
theorem production_model_not_rup (formula values : Array UInt32) (fuel : Nat)
    (formulaSize : formula.size < 4294967296) (valueSize : values.size < 4294967296)
    (accepted : sat_check_model formula values fuel = some true)
    (clauses : List (List UInt32)) (decoded : decodeFormula formula = some clauses) :
    ¬ RupCheck.Accepted (database clauses) := by
  obtain ⟨_, _, _, actual, same, model⟩ :=
    production_model_sound formula values fuel formulaSize valueSize accepted
  have equal : actual = clauses := Option.some.inj (same.symm.trans decoded)
  subst actual
  intro refutation
  exact RupCheck.accepted_unsatisfiable refutation (arrayAssignment values) model

end Oak.SATModel
