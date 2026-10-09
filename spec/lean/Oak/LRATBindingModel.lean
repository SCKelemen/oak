import Oak.LRATBoundRecord
import Oak.LRATBoundSoundness

/-!
Universal acceptance refinement from the extracted production identity gate
to the list-based formula-binding model. Array lengths must be representable
as Oak UInt32 view lengths. Fuel exhaustion is not successful execution.
-/
set_option autoImplicit false
namespace Oak.LRATFormulaBinding

@[simp] theorem project_length (words : Array UInt32) :
    (project words).length = words.size := by simp [project]

/-- Success cannot bypass the production header checks. -/
theorem production_binding_header (formula record : Array UInt32) (fuel : Nat)
    (run : LRATBinding.lrat_matches_formula formula record fuel = some true) :
    LRATChecker.bindingHeader formula record = true := by
  change (do
    let (same, _) ← LRATBinding.lrat_matches_formula.loop1 formula record
      (LRATChecker.bindingHeader formula record) LRATBinding.LRAT_HEADER_WORDS fuel
    pure same) = some true at run
  cases loopRun : LRATBinding.lrat_matches_formula.loop1 formula record
      (LRATChecker.bindingHeader formula record) LRATBinding.LRAT_HEADER_WORDS fuel with
  | none => simp [loopRun] at run
  | some pair =>
    rcases pair with ⟨same, finish⟩
    simp only [loopRun, bind, Option.bind, Option.pure_def, Option.some.injEq] at run
    subst same
    exact (LRATChecker.binding_loop_exact fuel formula record _ _ finish loopRun).1

/-- Pointwise equality and checked bounds give equality of the entire body,
including zero literals, duplicate literals, and clause length prefixes. -/
theorem projected_body_eq (formula record : Array UInt32) (n : Nat)
    (fc : 8 + n ≤ formula.size) (rc : 8 + n ≤ record.size)
    (same : ∀ k, 8 ≤ k → k < 8 + n → formula.getD k 0 = record.getD k 0) :
    ((project formula).drop 8).take n = ((project record).drop 8).take n := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, project_length]
    omega
  · intro i fi ri
    have bound : i < n := by
      simp only [List.length_take, List.length_drop, project_length] at fi
      omega
    have hf : 8 + i < (project formula).length := by rw [project_length]; omega
    have hr : 8 + i < (project record).length := by rw [project_length]; omega
    have equal : word (project formula) (8 + i) = word (project record) (8 + i) := by
      simp only [project_word, same (8 + i) (by omega) (by omega)]
    simp only [List.getElem_take, List.getElem_drop]
    simpa only [word, List.getElem?_eq_getElem hf, List.getElem?_eq_getElem hr,
      Option.getD_some] using equal

/-- Every successful production identity check satisfies the complete model:
framing, formula-only input, all identity fields, and exact ordered body.
This is universal in the input words, not a bounded corpus comparison. -/
theorem production_binding_refines_model (formula record : Array UInt32) (fuel : Nat)
    (formulaSize : formula.size < 4294967296) (recordSize : record.size < 4294967296)
    (run : LRATBinding.lrat_matches_formula formula record fuel = some true) :
    matchesFormula (project formula) (project record) = true := by
  have header := production_binding_header formula record fuel run
  have exactBinding := LRATChecker.production_binding_exact formula record fuel run
  simp only [LRATChecker.bindingHeader, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc] at header
  obtain ⟨fs, rs, fm, rm, fsteps, flen, rlen, rsteps, vars, counts, lens⟩ := header
  have fsize : formula.size.toUInt32.toNat = formula.size := Nat.mod_eq_of_lt formulaSize
  have rsize : record.size.toUInt32.toNat = record.size := Nat.mod_eq_of_lt recordSize
  change (8 : UInt32) ≤ formula.size.toUInt32 at fs
  change (8 : UInt32) ≤ record.size.toUInt32 at rs
  have fn : 8 ≤ formula.size := by
    have h := UInt32.le_iff_toNat_le.mp fs
    simpa only [fsize] using h
  have rn : 8 ≤ record.size := by
    have h := UInt32.le_iff_toNat_le.mp rs
    simpa only [rsize] using h
  have fl : (formula.getD 3 0).toNat = formula.size - 8 := by
    have h := congrArg UInt32.toNat flen
    simpa only [UInt32.toNat_sub_of_le _ _ fs, fsize] using h
  have rl : (record.getD 3 0).toNat ≤ record.size - 8 := by
    have h := UInt32.le_iff_toNat_le.mp rlen
    simpa only [UInt32.toNat_sub_of_le _ _ rs, rsize] using h
  have steps : (record.getD 4 0).toNat = record.size - 8 - (record.getD 3 0).toNat := by
    have h := congrArg UInt32.toNat rsteps
    simpa only [UInt32.toNat_sub_of_le _ _ rlen, UInt32.toNat_sub_of_le _ _ rs, rsize] using h
  have flit : (formula.getD 3 0).toNat = (record.getD 3 0).toNat := congrArg UInt32.toNat lens
  have body := projected_body_eq formula record (record.getD 3 0).toNat
    (by omega) (by omega) (by intro k lo hi; exact (exactBinding.payload k lo hi).symm)
  unfold matchesFormula
  apply decide_eq_true
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Framed, project_length, project_word]
    refine ⟨fn, ?_, by omega, ?_⟩
    · exact congrArg UInt32.toNat fm
    · have zero : (formula.getD 4 0).toNat = 0 := congrArg UInt32.toNat fsteps
      omega
  · simpa only [project_word] using congrArg UInt32.toNat fsteps
  · simp only [Framed, project_length, project_word]
    exact ⟨rn, congrArg UInt32.toNat rm, rl, steps⟩
  · unfold formulaKey
    simp only [project_word]
    rw [vars, counts, lens]
    exact congrArg (fun b => FormulaKey.mk (record.getD 1 0).toNat (record.getD 2 0).toNat
      (record.getD 3 0).toNat b) body

end Oak.LRATFormulaBinding
