import Oak.LRATFormulaBinding
import Oak.LRATRecordSoundness

/-!
Concrete composition of formula identity and production record soundness.
The caller supplies a successfully decoded expected CNF, not a solver verdict
or an abstract RUP derivation. The natural-cursor decoder checks each length
and exact consumption. Refinement of the production identity predicate to its
list model, source-to-CNF lowering, and compilation remain separate obligations.
-/
set_option autoImplicit false
namespace Oak.LRATFormulaBinding

/-- Project machine words without truncating their values. -/
def project (words : Array UInt32) : List Nat := words.toList.map UInt32.toNat

@[simp] theorem project_word (words : Array UInt32) (i : Nat) :
    word (project words) i = (words.getD i 0).toNat := by
  simp only [word, project, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases words[i]? <;> rfl

/-- Identity supplies every literal-region word, including length prefixes. -/
theorem matches_word {formula record : List Nat}
    (bound : matchesFormula formula record = true) (i : Nat)
    (lower : 8 ≤ i) (upper : i < 8 + word formula 3) :
    word formula i = word record i := by
  have lengths := congrArg FormulaKey.literalWords (matches_exact bound)
  change word formula 3 = word record 3 at lengths
  have body := congrArg (fun xs : List Nat => xs[i - 8]?) (matches_body bound)
  change ((formula.drop 8).take (word formula 3))[i - 8]? =
    ((record.drop 8).take (word record 3))[i - 8]? at body
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega),
    List.getElem?_drop, List.getElem?_drop] at body
  have index : 8 + (i - 8) = i := by omega
  rw [index] at body
  exact congrArg (fun x : Option Nat => x.getD 0) body

/-- Decode precisely the declared initial region, refusing truncated lengths,
clause bodies crossing the endpoint, and unused trailing words. -/
def decodeInitial (words : Array UInt32) (at_ end_ : Nat) : Nat → Option (List RupCheck.Clause)
  | 0 => if at_ = end_ ∧ end_ ≤ words.size then some [] else none
  | count + 1 => do
    if at_ < end_ ∧ end_ ≤ words.size then
      let n := (words.getD at_ 0).toNat
      if at_ + 1 + n ≤ end_ then
        let rest ← decodeInitial words (at_ + 1 + n) end_ count
        pure (LRATChecker.inputClause words (at_ + 1) n :: rest)
      else none
    else none

/-- A bounded successful decode is the production theorem's mathematical
input even when the record has a different header or proof suffix. -/
theorem decodeInitial_transfer (count : Nat) (formula record : Array UInt32)
    (at_ end_ : Nat) (clauses : List RupCheck.Clause)
    (same : ∀ i, at_ ≤ i → i < end_ → formula.getD i 0 = record.getD i 0)
    (decoded : decodeInitial formula at_ end_ count = some clauses) :
    LRATChecker.initialClauses record at_ count = clauses := by
  induction count generalizing at_ clauses with
  | zero =>
    simp only [decodeInitial] at decoded
    split at decoded <;> simp_all [LRATChecker.initialClauses]
  | succ count ih =>
    by_cases header : at_ < end_ ∧ end_ ≤ formula.size
    · have lengthWord := same at_ (by omega) header.1
      by_cases fits : at_ + 1 + (formula.getD at_ 0).toNat ≤ end_
      · simp only [decodeInitial, header, fits, ite_true] at decoded
        cases restRun : decodeInitial formula (at_ + 1 + (formula.getD at_ 0).toNat) end_ count with
        | none => simp only [restRun, bind, Option.bind, reduceCtorEq] at decoded
        | some rest =>
          simp only [restRun, bind, Option.bind, Option.pure_def, Option.some.injEq] at decoded
          rw [← decoded, LRATChecker.initialClauses, ← lengthWord]
          have tail := ih (at_ + 1 + (formula.getD at_ 0).toNat) rest
            (by intro i lo hi; exact same i (by omega) hi) restRun
          rw [tail]
          congr 1
          unfold LRATChecker.inputClause
          apply List.map_congr_left
          intro k member
          have hk := List.mem_range.mp member
          rw [same (at_ + 1 + k) (by omega) (by omega)]
      · simp only [decodeInitial, header, fits, ite_true, ite_false, reduceCtorEq] at decoded
    · simp only [decodeInitial, header, ite_false, reduceCtorEq] at decoded

/-- An accepted production record refutes the independently supplied CNF
when exact formula binding succeeds and that expected CNF decodes fully.
There is no abstract RUP-acceptance or arbitrary-decoder hypothesis. -/
theorem production_bound_record_sound (formula record starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32)
    (fuel : Nat) (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32)
    (x : Array UInt8) (y o : Array UInt32) (clauses : List RupCheck.Clause)
    (bound : matchesFormula (project formula) (project record) = true)
    (decoded : decodeInitial formula 8 (8 + (formula.getD 3 0).toNat)
      (formula.getD 2 0).toNat = some clauses)
    (run : LRATChecker.lrat_check record starts lengths alive store assign trail out fuel =
      some (LRATChecker.LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    ¬ ∃ a, ∀ clause ∈ clauses, RupCheck.SatisfiesClause a clause := by
  have countEq := congrArg FormulaKey.clauses (matches_exact bound)
  change word (project formula) 2 = word (project record) 2 at countEq
  simp only [project_word] at countEq
  have same : ∀ i, 8 ≤ i → i < 8 + (formula.getD 3 0).toNat →
      formula.getD i 0 = record.getD i 0 := by
    intro i lo hi
    apply UInt32.toNat_inj.mp
    simpa only [project_word] using matches_word bound i lo (by simpa only [project_word] using hi)
  have transferred := decodeInitial_transfer (formula.getD 2 0).toNat formula record 8
    (8 + (formula.getD 3 0).toNat) clauses same decoded
  rw [countEq] at transferred
  intro ⟨a, model⟩
  apply LRATChecker.production_record_sound record starts lengths alive store assign trail out fuel s l v t x y o run
  exact ⟨a, by simpa only [LRATChecker.InitialModels, transferred] using model⟩

end Oak.LRATFormulaBinding
