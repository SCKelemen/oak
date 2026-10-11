import Oak.LRATBoundRecord
import Oak.LRATBoundSoundness

/-!
Universal acceptance refinement from the extracted production identity gate
to the list-based formula-binding model. Array lengths must be representable
as Oak UInt32 view lengths. Fuel exhaustion is not successful execution.
-/
set_option autoImplicit false
namespace Oak.LRATFormulaBinding

private theorem eight_nat : (8 : UInt32).toNat = 8 := by decide

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
  change formula.getD 0 0 = LRATBinding.LRAT_MAGIC at fm
  change record.getD 0 0 = LRATBinding.LRAT_MAGIC at rm
  change formula.getD 4 0 = 0 at fsteps
  change formula.getD 3 0 = formula.size.toUInt32 - 8 at flen
  change record.getD 3 0 ≤ record.size.toUInt32 - 8 at rlen
  change record.getD 4 0 = record.size.toUInt32 - 8 - record.getD 3 0 at rsteps
  change formula.getD 1 0 = record.getD 1 0 at vars
  change formula.getD 2 0 = record.getD 2 0 at counts
  change formula.getD 3 0 = record.getD 3 0 at lens
  have fsize : formula.size.toUInt32.toNat = formula.size := Nat.mod_eq_of_lt formulaSize
  have rsize : record.size.toUInt32.toNat = record.size := Nat.mod_eq_of_lt recordSize
  change (8 : UInt32) ≤ formula.size.toUInt32 at fs
  change (8 : UInt32) ≤ record.size.toUInt32 at rs
  have fn : 8 ≤ formula.size := by
    have h := UInt32.le_iff_toNat_le.mp fs
    simpa only [eight_nat, fsize] using h
  have rn : 8 ≤ record.size := by
    have h := UInt32.le_iff_toNat_le.mp rs
    simpa only [eight_nat, rsize] using h
  have fl : (formula.getD 3 0).toNat = formula.size - 8 := by
    have h := congrArg UInt32.toNat flen
    simpa only [UInt32.toNat_sub_of_le _ _ fs, eight_nat, fsize] using h
  have rl : (record.getD 3 0).toNat ≤ record.size - 8 := by
    have h := UInt32.le_iff_toNat_le.mp rlen
    simpa only [UInt32.toNat_sub_of_le _ _ rs, eight_nat, rsize] using h
  have steps : (record.getD 4 0).toNat = record.size - 8 - (record.getD 3 0).toNat := by
    have h := congrArg UInt32.toNat rsteps
    simpa only [UInt32.toNat_sub_of_le _ _ rlen, UInt32.toNat_sub_of_le _ _ rs, eight_nat, rsize] using h
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
  · simpa only [project_word, UInt32.toNat_zero] using congrArg UInt32.toNat fsteps
  · simp only [Framed, project_length, project_word]
    exact ⟨rn, congrArg UInt32.toNat rm, rl, steps⟩
  · unfold formulaKey
    simp only [project_word]
    rw [vars, counts, lens]
    exact congrArg (fun b => FormulaKey.mk (record.getD 1 0).toNat (record.getD 2 0).toNat
      (record.getD 3 0).toNat b) body

/-- A matching model supplies the exact production header guards. -/
theorem model_binding_header (formula record : Array UInt32)
    (formulaSize : formula.size < 4294967296) (recordSize : record.size < 4294967296)
    (bound : matchesFormula (project formula) (project record) = true) :
    LRATChecker.bindingHeader formula record = true := by
  obtain ⟨ff, zero, rf⟩ := matches_framed bound
  have keys := matches_exact bound
  have vars := congrArg FormulaKey.variables keys
  have counts := congrArg FormulaKey.clauses keys
  have lens := congrArg FormulaKey.literalWords keys
  simp only [Framed, project_length, project_word] at ff rf
  simp only [project_word] at zero
  simp only [formulaKey, project_word] at vars counts lens
  have fsize : formula.size.toUInt32.toNat = formula.size := Nat.mod_eq_of_lt formulaSize
  have rsize : record.size.toUInt32.toNat = record.size := Nat.mod_eq_of_lt recordSize
  have fs : (8 : UInt32) ≤ formula.size.toUInt32 := by
    apply UInt32.le_iff_toNat_le.mpr
    simpa only [eight_nat, fsize] using ff.1
  have rs : (8 : UInt32) ≤ record.size.toUInt32 := by
    apply UInt32.le_iff_toNat_le.mpr
    simpa only [eight_nat, rsize] using rf.1
  have rl : record.getD 3 0 ≤ record.size.toUInt32 - 8 := by
    apply UInt32.le_iff_toNat_le.mpr
    simpa only [UInt32.toNat_sub_of_le _ _ rs, eight_nat, rsize] using rf.2.2.1
  simp only [LRATChecker.bindingHeader, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc]
  change 8 ≤ formula.size.toUInt32 ∧ 8 ≤ record.size.toUInt32 ∧
    formula.getD 0 0 = LRATBinding.LRAT_MAGIC ∧ record.getD 0 0 = LRATBinding.LRAT_MAGIC ∧
    formula.getD 4 0 = 0 ∧ formula.getD 3 0 = formula.size.toUInt32 - 8 ∧
    record.getD 3 0 ≤ record.size.toUInt32 - 8 ∧
    record.getD 4 0 = record.size.toUInt32 - 8 - record.getD 3 0 ∧
    formula.getD 1 0 = record.getD 1 0 ∧ formula.getD 2 0 = record.getD 2 0 ∧
    formula.getD 3 0 = record.getD 3 0
  refine ⟨fs, rs, UInt32.toNat_inj.mp ff.2.1, UInt32.toNat_inj.mp rf.2.1,
    UInt32.toNat_inj.mp zero, ?_, rl, ?_, UInt32.toNat_inj.mp vars,
    UInt32.toNat_inj.mp counts, UInt32.toNat_inj.mp lens⟩
  · apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ fs, eight_nat, fsize]
    omega
  · apply UInt32.toNat_inj.mp
    simpa only [UInt32.toNat_sub_of_le _ _ rl, UInt32.toNat_sub_of_le _ _ rs,
      eight_nat, rsize] using rf.2.2.2

/-- Exact list identity includes every production payload read. -/
theorem model_binding_payload (formula record : Array UInt32)
    (bound : matchesFormula (project formula) (project record) = true)
    (k : Nat) (lower : 8 ≤ k) (upper : k < formula.size) :
    formula.getD k 0 = record.getD k 0 := by
  obtain ⟨ff, zero, _⟩ := matches_framed bound
  simp only [Framed, project_length, project_word] at ff
  simp only [project_word] at zero
  have keys := matches_exact bound
  have lens := congrArg FormulaKey.literalWords keys
  simp only [formulaKey, project_word] at lens
  have body := matches_body bound
  simp only [formulaKey, project_word] at body
  have iBound : k - 8 < (formula.getD 3 0).toNat := by omega
  have rBound : k - 8 < (record.getD 3 0).toNat := by omega
  have same := congrArg (fun words : List Nat => words[k - 8]?.getD 0) body
  simp only [List.getElem?_take_of_lt iBound, List.getElem?_take_of_lt rBound,
    List.getElem?_drop] at same
  have index : 8 + (k - 8) = k := by omega
  rw [index] at same
  change word (project formula) k = word (project record) k at same
  simp only [project_word] at same
  exact UInt32.toNat_inj.mp same

/-- One unit of fuel per payload word, plus the terminating guard, suffices. -/
theorem binding_loop_complete (fuel : Nat) (formula record : Array UInt32) (at_ : UInt32)
    (enough : formula.size.toUInt32.toNat - at_.toNat < fuel)
    (payload : ∀ k, at_.toNat ≤ k → k < formula.size.toUInt32.toNat →
      formula.getD k 0 = record.getD k 0) :
    LRATBinding.lrat_matches_formula.loop1 formula record true at_ fuel =
      some (true, max at_ formula.size.toUInt32) := by
  induction fuel generalizing at_ with
  | zero => omega
  | succ fuel ih =>
    by_cases advance : at_ < formula.size.toUInt32
    · have an := UInt32.lt_iff_toNat_lt.mp advance
      have next : (at_ + 1).toNat = at_.toNat + 1 := by
        apply LRATChecker.add_exact
        have := formula.size.toUInt32.toNat_lt
        simp only [UInt32.toNat_one]
        omega
      have same := payload at_.toNat (by omega) an
      simp only [LRATBinding.lrat_matches_formula.loop1, advance, decide_true,
        Bool.and_self, ite_true, same, beq_self_eq_true]
      rw [ih (at_ + 1) (by rw [next]; omega) (by
        intro k lo hi
        exact payload k (by rw [next] at lo; omega) hi)]
      have le : at_ ≤ formula.size.toUInt32 := by
        apply UInt32.le_iff_toNat_le.mpr; omega
      have nextLe : at_ + 1 ≤ formula.size.toUInt32 := by
        apply UInt32.le_iff_toNat_le.mpr; rw [next]; omega
      rw [max_eq_right le, max_eq_right nextLe]
    · have le : formula.size.toUInt32 ≤ at_ := by
        apply UInt32.le_iff_toNat_le.mpr
        have an : ¬ at_.toNat < formula.size.toUInt32.toNat := by
          intro h; exact advance (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      simp [LRATBinding.lrat_matches_formula.loop1, advance, max_eq_left le]

/-- Completeness with the exact payload-length fuel bound. -/
theorem model_binding_accepted (formula record : Array UInt32) (fuel : Nat)
    (formulaSize : formula.size < 4294967296) (recordSize : record.size < 4294967296)
    (enough : formula.size - 8 < fuel)
    (bound : matchesFormula (project formula) (project record) = true) :
    LRATBinding.lrat_matches_formula formula record fuel = some true := by
  have header := model_binding_header formula record formulaSize recordSize bound
  have fsize : formula.size.toUInt32.toNat = formula.size := Nat.mod_eq_of_lt formulaSize
  have loop := binding_loop_complete fuel formula record 8
    (by simpa only [fsize, eight_nat] using enough) (by
      intro k lo hi
      exact model_binding_payload formula record bound k
        (by simpa only [eight_nat] using lo) (by simpa only [fsize] using hi))
  change (do
    let (same, _) ← LRATBinding.lrat_matches_formula.loop1 formula record
      (LRATChecker.bindingHeader formula record) 8 fuel
    pure same) = some true
  rw [header, loop]
  rfl

/-- At sufficient fuel, production acceptance and model identity are equivalent. -/
theorem production_binding_iff_model (formula record : Array UInt32) (fuel : Nat)
    (formulaSize : formula.size < 4294967296) (recordSize : record.size < 4294967296)
    (enough : formula.size - 8 < fuel) :
    LRATBinding.lrat_matches_formula formula record fuel = some true ↔
      matchesFormula (project formula) (project record) = true :=
  ⟨production_binding_refines_model formula record fuel formulaSize recordSize,
    model_binding_accepted formula record fuel formulaSize recordSize enough⟩

end Oak.LRATFormulaBinding
