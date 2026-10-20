import Oak.LRATRecordSoundness
import Oak.LRATBindingExtracted

/-! Bind production record soundness to an independently retained formula. -/
set_option autoImplicit false
namespace Oak.LRATChecker

/-- Successful initial parsing only observes the declared initial payload. -/
theorem initial_loop_locality (fuel : Nat) (words other starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32)
    (variables count store_words at_ end_ used : UInt32) (empty : Bool) (c : UInt32)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (at' used' : UInt32) (empty' : Bool) (c' : UInt32)
    (noWrap : count.toNat + 1 < 4294967296)
    (progress : c.toNat ≤ count.toNat + 1)
    (same : ∀ k, at_.toNat ≤ k → k < end_.toNat → words.getD k 0 = other.getD k 0)
    (run : lrat_check.loop3 words starts lengths alive store LRAT_ACCEPTED variables count store_words
      at_ end_ used empty c fuel = some (starts', lengths', alive', store', LRAT_ACCEPTED, at', used', empty', c')) :
    initialClauses words at_.toNat (count.toNat + 1 - c.toNat) =
      initialClauses other at_.toNat (count.toNat + 1 - c.toNat) := by
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
              rw [remaining, initialClauses, initialClauses, ← nOther, ← nValue]
              congr 1
              · unfold inputClause
                apply List.map_congr_left
                intro k hk
                have := List.mem_range.mp hk
                rw [same (at_.toNat + 1 + k) (by omega) (by rw [headerNext] at sourceBound; omega)]
              · rw [← nextAt]
                apply ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [nextCounter]; omega) _ run
                intro k lower upper
                exact same k (by rw [nextAt] at lower; omega) upper
          · simp only [fits, Bool.false_eq_true, ite_false] at run
            have impossible := initial_input_accepted fuel words starts lengths alive store LRAT_MALFORMED
              variables count store_words at_ end_ used empty (c + 1)
              starts' lengths' alive' store' at' used' empty' c' run
            contradiction
    · rw [UInt32.le_iff_toNat_le] at advance
      have remaining : count.toNat + 1 - c.toNat = 0 := by omega
      simp only [remaining, initialClauses]

/-- Acceptance of the production identity loop implies equality at every
visited payload position; a mismatch cannot recover on a later iteration. -/
theorem binding_loop_exact (fuel : Nat) (formula record : Array UInt32)
    (same : Bool) (at_ finish : UInt32)
    (run : LRATBinding.lrat_matches_formula.loop1 formula record same at_ fuel = some (true, finish)) :
    same = true ∧ ∀ k, at_.toNat ≤ k → k < formula.size.toUInt32.toNat →
      formula.getD k 0 = record.getD k 0 := by
  induction fuel generalizing same at_ finish with
  | zero => simp [LRATBinding.lrat_matches_formula.loop1] at run
  | succ fuel ih =>
    by_cases advance : same = true ∧ at_ < formula.size.toUInt32
    · simp only [LRATBinding.lrat_matches_formula.loop1, advance.1, advance.2,
        decide_true, Bool.and_self, ite_true] at run
      obtain ⟨eq, tail⟩ := ih _ _ _ run
      have next := LRATRUP.counter_succ at_ formula.size.toUInt32 advance.2
      refine ⟨advance.1, ?_⟩
      intro k lower upper
      by_cases here : k = at_.toNat
      · simpa only [here, beq_iff_eq] using eq
      · exact tail k (by rw [next]; omega) upper
    · have stop : (same && decide (at_ < formula.size.toUInt32)) = false := by
        simp only [Bool.and_eq_false_imp, decide_eq_false_iff_not]
        intro good bound
        exact advance ⟨good, bound⟩
      simp only [LRATBinding.lrat_matches_formula.loop1, stop, Bool.false_eq_true,
        ite_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      refine ⟨run.1, ?_⟩
      intro k lower upper
      have bound : ¬ at_ < formula.size.toUInt32 := fun h => advance ⟨run.1, h⟩
      rw [UInt32.lt_iff_toNat_lt] at bound
      omega

/-- Exact production binding properties needed by the independent decoder. -/
structure BindingExact (formula record : Array UInt32) : Prop where
  count : formula.getD 2 0 = record.getD 2 0
  literalWords : formula.getD 3 0 = record.getD 3 0
  end_eq : 8 + (record.getD 3 0).toNat = formula.size.toUInt32.toNat
  payload : ∀ k, 8 ≤ k → k < 8 + (record.getD 3 0).toNat →
    record.getD k 0 = formula.getD k 0

/-- Header prefix of the extracted identity gate. -/
def bindingHeader (formula record : Array UInt32) : Bool :=
  let same : Bool := ((decide ((formula.size.toUInt32) >= LRATBinding.LRAT_HEADER_WORDS)) && (decide ((record.size.toUInt32) >= LRATBinding.LRAT_HEADER_WORDS)))
  let same := ((same && ((formula.getD (0 : UInt32).toNat (0 : UInt32)) == LRATBinding.LRAT_MAGIC)) && ((record.getD (0 : UInt32).toNat (0 : UInt32)) == LRATBinding.LRAT_MAGIC))
  let same := ((same && ((formula.getD (4 : UInt32).toNat (0 : UInt32)) == (0 : UInt32))) && ((formula.getD (3 : UInt32).toNat (0 : UInt32)) == ((formula.size.toUInt32) - LRATBinding.LRAT_HEADER_WORDS)))
  let same := (same && (decide ((record.getD (3 : UInt32).toNat (0 : UInt32)) <= ((record.size.toUInt32) - LRATBinding.LRAT_HEADER_WORDS))))
  let same := (same && ((record.getD (4 : UInt32).toNat (0 : UInt32)) == (((record.size.toUInt32) - LRATBinding.LRAT_HEADER_WORDS) - (record.getD (3 : UInt32).toNat (0 : UInt32)))))
  let same := (((same && ((formula.getD (1 : UInt32).toNat (0 : UInt32)) == (record.getD (1 : UInt32).toNat (0 : UInt32)))) && ((formula.getD (2 : UInt32).toNat (0 : UInt32)) == (record.getD (2 : UInt32).toNat (0 : UInt32)))) && ((formula.getD (3 : UInt32).toNat (0 : UInt32)) == (record.getD (3 : UInt32).toNat (0 : UInt32))))
  same

theorem production_binding_exact (formula record : Array UInt32) (fuel : Nat)
    (run : LRATBinding.lrat_matches_formula formula record fuel = some true) :
    BindingExact formula record := by
  change (do
    let (same, _) ← LRATBinding.lrat_matches_formula.loop1 formula record
      (bindingHeader formula record) LRATBinding.LRAT_HEADER_WORDS fuel
    pure same) = some true at run
  generalize sameDef : bindingHeader formula record = same at run
  cases loopRun : LRATBinding.lrat_matches_formula.loop1 formula record same LRATBinding.LRAT_HEADER_WORDS fuel with
  | none => simp [loopRun] at run
  | some pair =>
    rcases pair with ⟨result, finish⟩
    simp only [loopRun, bind, Option.bind, Option.pure_def, Option.some.injEq] at run
    subst result
    obtain ⟨good, payload⟩ := binding_loop_exact fuel formula record same 8 finish loopRun
    rw [good] at sameDef
    simp only [bindingHeader, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at sameDef
    obtain ⟨fs, _, _, _, _, len, _, _, _, count, words⟩ := sameDef
    change 8 ≤ formula.size.toUInt32 at fs
    change formula.getD 3 0 = record.getD 3 0 at words
    change formula.getD 3 0 = formula.size.toUInt32 - 8 at len
    have endEq : 8 + (record.getD 3 0).toNat = formula.size.toUInt32.toNat := by
      rw [← words, len, UInt32.toNat_sub_of_le _ _ fs]
      change 8 + (formula.size.toUInt32.toNat - 8) = formula.size.toUInt32.toNat
      have := UInt32.le_iff_toNat_le.mp fs
      change 8 ≤ formula.size.toUInt32.toNat at this
      omega
    refine ⟨count, words, endEq, ?_⟩
    intro k lower upper
    exact (payload k lower (by rw [endEq] at upper; exact upper)).symm

/-- Accepted production parsing gives equality of the independently decoded
initial clauses whenever the declared payload agrees. -/
theorem checkerBody_initial_locality (words other starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (h : HeaderData) (fuel : Nat)
    (validHeader : HeaderValid words starts lengths alive store assign trail out h)
    (same : ∀ k, 8 ≤ k → k < h.literal_end.toNat → words.getD k 0 = other.getD k 0)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (run : checkerBody words starts lengths alive store assign trail out h fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    initialClauses words 8 h.clause_count.toNat = initialClauses other 8 h.clause_count.toNat := by
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
          have countBound := UInt32.le_iff_toNat_le.mp validHeader.countBound
          have countNoWrap : h.clause_count.toNat + 1 < 4294967296 := by
            have := validHeader.maxBound
            omega
          simpa only [LRAT_HEADER_WORDS, UInt32.toNat_ofNat, Nat.add_sub_cancel] using
            initial_loop_locality fuel words other starts lengths live store h.variables h.clause_count h.store_words
              8 h.literal_end 0 false 1 is il iv it iat iused iempty ic countNoWrap (by simp) same initialRun

/-- Every accepted production identity gate followed by an accepted production
checker call refutes the independently supplied expected formula. No parser
trace, payload equality, scratch invariant, or abstract acceptance is assumed. -/
theorem production_bound_record_sound (formula words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (bindingFuel fuel : Nat)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (binding : LRATBinding.lrat_matches_formula formula words bindingFuel = some true)
    (run : lrat_check words starts lengths alive store assign trail out fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    ¬ ∃ a, InitialModels formula (formula.getD 2 0).toNat 8 a := by
  have sound := production_record_sound words starts lengths alive store assign trail out fuel s l v t x y o run
  have bound := production_binding_exact formula words bindingFuel binding
  rw [checker_eq_body] at run
  have good := checkerBody_accepted_header (run := run)
  have header := parseHeader_valid words starts lengths alive store assign trail out good
  have decoded := checkerBody_initial_locality words formula starts lengths alive store assign trail out _ fuel header
    (by intro k lower upper; exact bound.payload k lower (by rw [header.literalEnd_eq] at upper; exact upper))
    s l v t x y o run
  rw [header.count_eq] at decoded
  intro ⟨a, model⟩
  apply sound
  refine ⟨a, ?_⟩
  unfold InitialModels at model ⊢
  rw [decoded, ← bound.count]
  exact model

end Oak.LRATChecker
