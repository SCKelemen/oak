import Oak.LRATBoundRecord
import Oak.LRATBoundSoundness

/-! Successful production checking establishes complete bounded CNF decoding. -/
set_option autoImplicit false
namespace Oak.LRATChecker

/-- Accepted initial traversal ending at the declared endpoint admits the
independent bounded decoder, including for another array with equal payload. -/
theorem initial_loop_decodes (fuel : Nat) (words other starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32)
    (variables count store_words at_ end_ used : UInt32) (empty : Bool) (c : UInt32)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (at' used' : UInt32) (empty' : Bool) (c' : UInt32)
    (noWrap : count.toNat + 1 < 4294967296)
    (progress : c.toNat ≤ count.toNat + 1)
    (capacity : end_.toNat ≤ other.size)
    (finish : at' = end_)
    (same : ∀ k, at_.toNat ≤ k → k < end_.toNat → words.getD k 0 = other.getD k 0)
    (run : lrat_check.loop3 words starts lengths alive store LRAT_ACCEPTED variables count store_words
      at_ end_ used empty c fuel = some (starts', lengths', alive', store', LRAT_ACCEPTED, at', used', empty', c')) :
    LRATFormulaBinding.decodeInitial other at_.toNat end_.toNat (count.toNat + 1 - c.toNat) =
      some (initialClauses other at_.toNat (count.toNat + 1 - c.toNat)) := by
  induction fuel generalizing starts lengths alive store at_ used empty c starts' lengths' alive' store' at' used' empty' c' with
  | zero => simp [lrat_check.loop3] at run
  | succ fuel ih =>
    by_cases advance : c ≤ count
    · have cn := UInt32.le_iff_toNat_le.mp advance
      have nextCounter : (c + 1).toNat = c.toNat + 1 := by
        simpa only [UInt32.toNat_one] using add_exact c 1 (by simp only [UInt32.toNat_one]; omega)
      simp only [lrat_check.loop3, advance, decide_true, beq_self_eq_true, Bool.and_self, ite_true] at run
      generalize nDef : (if decide (at_ < end_) then words.getD at_.toNat 0 else (0 : UInt32)) = n at run
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
              simp only [scanRun] at run
              have accepted := initial_input_accepted fuel words _ _ _ _ status variables count store_words
                (at_ + 1 + n) end_ (used + n) (empty || (n == 0)) (c + 1)
                starts' lengths' alive' store' at' used' empty' c' run
              subst status
              have hn := UInt32.lt_iff_toNat_lt.mp header
              have headerNext : (at_ + 1).toNat = at_.toNat + 1 := by
                apply add_exact; have := end_.toNat_lt; simp only [UInt32.toNat_one]; omega
              have sourceBound := (fits_iff (at_ + 1) n end_ fuel).mp sourceRun
              have nextAt : (at_ + 1 + n).toNat = at_.toNat + 1 + n.toNat := by
                rw [add_exact (at_ + 1) n (Nat.lt_of_le_of_lt sourceBound end_.toNat_lt), headerNext]
              have nValue : n = words.getD at_.toNat 0 := by simpa [header] using nDef.symm
              have nOther : words.getD at_.toNat 0 = other.getD at_.toNat 0 := same _ (by omega) hn
              have remaining : count.toNat + 1 - c.toNat = (count.toNat + 1 - (c + 1).toNat) + 1 := by
                rw [nextCounter]; omega
              have otherN : other.getD at_.toNat 0 = n := nOther.symm.trans nValue.symm
              have bodyBound : at_.toNat + 1 + n.toNat ≤ end_.toNat := by
                rw [headerNext] at sourceBound
                exact sourceBound
              rw [remaining, LRATFormulaBinding.decodeInitial, initialClauses, otherN]
              simp only [hn, capacity, bodyBound, and_self, ite_true]
              have tail := ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [nextCounter]; omega) finish
                (by intro k lo hi; exact same k (by rw [nextAt] at lo; omega) hi) run
              rw [nextAt] at tail
              simp only [tail, bind, Option.bind, Option.pure_def]
          · simp only [fits, Bool.false_eq_true, ite_false] at run
            have impossible := initial_input_accepted fuel words starts lengths alive store LRAT_MALFORMED
              variables count store_words at_ end_ used empty (c + 1)
              starts' lengths' alive' store' at' used' empty' c' run
            contradiction
    · have stopped : ¬ c.toNat ≤ count.toNat := by simpa only [UInt32.le_iff_toNat_le] using advance
      have remaining : count.toNat + 1 - c.toNat = 0 := by omega
      simp only [lrat_check.loop3, decide_eq_false advance, Bool.false_and,
        Bool.false_eq_true, ite_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      have finalCursor : at_ = at' := run.2.2.2.2.2.1
      have endpoint : at_.toNat = end_.toNat := congrArg UInt32.toNat (finalCursor.trans finish)
      simp only [remaining, LRATFormulaBinding.decodeInitial, initialClauses, endpoint, capacity,
        and_self, ite_true]

/-- Whole-checker acceptance supplies the successful initial traversal and
exact endpoint check needed by the bounded decoder. -/
theorem checkerBody_initial_decodes (words other starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (h : HeaderData) (fuel : Nat)
    (validHeader : HeaderValid words starts lengths alive store assign trail out h)
    (capacity : h.literal_end.toNat ≤ other.size)
    (same : ∀ k, 8 ≤ k → k < h.literal_end.toNat → words.getD k 0 = other.getD k 0)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (run : checkerBody words starts lengths alive store assign trail out h fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    LRATFormulaBinding.decodeInitial other 8 h.literal_end.toNat h.clause_count.toNat =
      some (initialClauses other 8 h.clause_count.toNat) := by
  have good := checkerBody_accepted_header (run := run)
  unfold checkerBody at run
  simp only [good, ite_true] at run
  cases liveRun : lrat_check.loop1 alive true h.max_id 0 fuel with
  | none => simp [liveRun] at run
  | some pair =>
    rcases pair with ⟨live, liveEnd⟩
    simp only [liveRun, bind, Option.bind, Option.pure_def] at run
    cases assignRun : lrat_check.loop2 assign true h.variables 0 fuel with
    | none => simp [assignRun] at run
    | some pair =>
      rcases pair with ⟨scratch, scratchEnd⟩
      simp only [assignRun] at run
      cases initialRun : lrat_check.loop3 words starts lengths live store LRAT_ACCEPTED h.variables h.clause_count h.store_words
          LRAT_HEADER_WORDS h.literal_end 0 false 1 fuel with
      | none => simp [initialRun] at run
      | some initial =>
        rcases initial with ⟨is, il, iv, it, istatus, iat, iused, iempty, ic⟩
        simp only [initialRun, option_ite] at run
        generalize statusDef : (if ((istatus == LRAT_ACCEPTED) && (iat != h.literal_end)) then LRAT_MALFORMED else istatus) = parserStatus at run
        cases stepRun : lrat_check.loop5 words is il iv it scratch trail parserStatus 0 0 h.variables h.max_id h.store_words
            h.literal_end (h.literal_end + h.step_words) iused iempty h.clause_count fuel with
        | none => simp [stepRun] at run
        | some result =>
          rcases result with ⟨fs, fl, fv, ft, fx, fy, fstatus, fadds, fdels, fat, fused, fempty, flast⟩
          simp only [stepRun] at run
          have finish : fstatus = LRAT_ACCEPTED ∧ fempty = true := by
            cases fempty <;> by_cases accepted : fstatus = LRAT_ACCEPTED <;>
              simp only [accepted, beq_iff_eq, Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false,
                Bool.false_eq_true, ite_false, ite_true] at run <;>
              split at run <;> simp_all [LRAT_NO_EMPTY, LRAT_ACCEPTED]
          obtain ⟨rfl, rfl⟩ := finish
          have ps := record_input_accepted (run := stepRun)
          rw [ps] at stepRun statusDef
          have initialAccepted : istatus = LRAT_ACCEPTED := by
            split at statusDef
            · contradiction
            · exact statusDef
          subst istatus
          have exactEnd : iat = h.literal_end := by
            apply Classical.byContradiction
            intro different
            simp [different, LRAT_ACCEPTED, LRAT_MALFORMED] at statusDef
          have countBound := UInt32.le_iff_toNat_le.mp validHeader.countBound
          have countNoWrap : h.clause_count.toNat + 1 < 4294967296 := by
            have := validHeader.maxBound
            omega
          simpa only [LRAT_HEADER_WORDS, UInt32.toNat_ofNat, Nat.add_sub_cancel] using
            initial_loop_decodes fuel words other starts lengths live store h.variables h.clause_count h.store_words
              8 h.literal_end 0 false 1 is il iv it iat iused iempty ic countNoWrap (by simp) capacity exactEnd same initialRun

/-- The production checker cannot accept a record whose initial CNF fails
bounded decoding, even if later proof records would otherwise refute it. -/
theorem production_record_decodes (words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (fuel : Nat)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (run : lrat_check words starts lengths alive store assign trail out fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    LRATFormulaBinding.decodeInitial words 8 (8 + (words.getD 3 0).toNat) (words.getD 2 0).toNat =
      some (initialClauses words 8 (words.getD 2 0).toNat) := by
  rw [checker_eq_body] at run
  have good := checkerBody_accepted_header (run := run)
  have header := parseHeader_valid words starts lengths alive store assign trail out good
  have decoded := checkerBody_initial_decodes words words starts lengths alive store assign trail out _ fuel header
    header.literalCapacity (by intros; rfl) s l v t x y o run
  simpa only [header.literalEnd_eq, header.count_eq] using decoded

/-- Two accepted production calls establish a fully decoded, unsatisfiable
expected CNF. Successful decoding is a conclusion, never a caller premise. -/
theorem production_bound_cnf_sound (formula words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (bindingFuel fuel : Nat)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (binding : LRATBinding.lrat_matches_formula formula words bindingFuel = some true)
    (run : lrat_check words starts lengths alive store assign trail out fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    ∃ clauses, LRATFormulaBinding.decodeInitial formula 8 (8 + (formula.getD 3 0).toNat)
        (formula.getD 2 0).toNat = some clauses ∧
      ¬ ∃ a, ∀ clause ∈ clauses, RupCheck.SatisfiesClause a clause := by
  have sound := production_bound_record_sound formula words starts lengths alive store assign trail out bindingFuel fuel
    s l v t x y o binding run
  have bound := production_binding_exact formula words bindingFuel binding
  rw [checker_eq_body] at run
  have good := checkerBody_accepted_header (run := run)
  have header := parseHeader_valid words starts lengths alive store assign trail out good
  have capacity : (parseHeader words starts lengths alive store assign trail out).literal_end.toNat ≤ formula.size := by
    rw [header.literalEnd_eq, bound.end_eq]
    exact Nat.mod_le _ _
  have decoded := checkerBody_initial_decodes words formula starts lengths alive store assign trail out _ fuel header
    capacity (by intro k lo hi; exact bound.payload k lo (by rw [header.literalEnd_eq] at hi; exact hi)) s l v t x y o run
  rw [header.literalEnd_eq, header.count_eq, ← bound.count, ← bound.literalWords] at decoded
  exact ⟨initialClauses formula 8 (formula.getD 2 0).toNat, decoded, sound⟩

end Oak.LRATChecker
