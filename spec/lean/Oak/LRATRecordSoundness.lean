import Oak.LRATSteps

/-! Whole-record soundness of the extracted production word checker. -/
set_option autoImplicit false
namespace Oak.LRATChecker

theorem option_ite {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then some a else some b) = some (if p then a else b) := by
  split <;> rfl

/-- Models of the independent natural-cursor input decoder. -/
def InitialModels (words : Array UInt32) (count at_ : Nat) (a : RupCheck.Assignment) : Prop :=
  ∀ clause ∈ initialClauses words at_ count, RupCheck.SatisfiesClause a clause

structure HeaderData where
  ok : Bool
  variables : UInt32
  clause_count : UInt32
  literal_end : UInt32
  step_words : UInt32
  max_id : UInt32
  store_words : UInt32

/-- Pure projection of the production header checks. -/
def parseHeader (words starts lengths : Array UInt32) (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) : HeaderData :=
  let ok : Bool := (((decide ((words.size.toUInt32) >= LRAT_HEADER_WORDS)) && ((words.getD (0 : UInt32).toNat (0 : UInt32)) == LRAT_MAGIC)) && (decide ((out.size.toUInt32) >= (3 : UInt32))))
  let variables : UInt32 := (if ok then (words.getD (1 : UInt32).toNat (0 : UInt32)) else (0 : UInt32))
  let clause_count : UInt32 := (if ok then (words.getD (2 : UInt32).toNat (0 : UInt32)) else (0 : UInt32))
  let literal_words : UInt32 := (if ok then (words.getD (3 : UInt32).toNat (0 : UInt32)) else (0 : UInt32))
  let step_words : UInt32 := (if ok then (words.getD (4 : UInt32).toNat (0 : UInt32)) else (0 : UInt32))
  let max_id : UInt32 := (if ok then (words.getD (5 : UInt32).toNat (0 : UInt32)) else (0 : UInt32))
  let store_words : UInt32 := (if ok then (words.getD (6 : UInt32).toNat (0 : UInt32)) else (0 : UInt32))
  let r1 := decide (LRAT_HEADER_WORDS.toNat + literal_words.toNat ≤ words.size.toUInt32.toNat)
  let ok := (ok && r1)
  let literal_end : UInt32 := (if ok then (LRAT_HEADER_WORDS + literal_words) else (0 : UInt32))
  let r2 := decide (literal_end.toNat + step_words.toNat ≤ words.size.toUInt32.toNat)
  let ok := (ok && r2)
  let ok := (ok && ((literal_end + step_words) == (words.size.toUInt32)))
  let ok := (((ok && (decide ((starts.size.toUInt32) > max_id))) && (decide ((lengths.size.toUInt32) > max_id))) && (decide ((alive.size.toUInt32) > max_id)))
  let ok := (((ok && (decide ((store.size.toUInt32) >= store_words))) && (decide ((assign.size.toUInt32) >= variables))) && (decide ((trail.size.toUInt32) >= variables)))
  let ok := (ok && (decide (clause_count <= max_id)))
  ⟨ok, variables, clause_count, literal_end, step_words, max_id, store_words⟩

/-- The production continuation after its header checks. -/
def checkerBody (words starts lengths : Array UInt32) (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (h : HeaderData) (fuel : Nat) :
    Option (UInt32 × Array UInt32 × Array UInt32 × Array UInt8 × Array UInt32 × Array UInt8 × Array UInt32 × Array UInt32) := do
  let ok := h.ok
  let variables := h.variables
  let clause_count := h.clause_count
  let literal_end := h.literal_end
  let step_words := h.step_words
  let max_id := h.max_id
  let store_words := h.store_words
  let additions : UInt32 := 0
  let deletions : UInt32 := 0
  let status := (if ok then LRAT_ACCEPTED else LRAT_CAPACITY)
  let i : UInt32 := (0 : UInt32)
  let (alive, _i) ← lrat_check.loop1 alive ok max_id i fuel
  let i := (0 : UInt32)
  let (assign, _i) ← lrat_check.loop2 assign ok variables i fuel
  let at_ : UInt32 := LRAT_HEADER_WORDS
  let end_ : UInt32 := literal_end
  let used : UInt32 := (0 : UInt32)
  let empty : Bool := false
  let c : UInt32 := (1 : UInt32)
  let (starts, lengths, alive, store, status, at_, used, empty, _c) ← lrat_check.loop3 words starts lengths alive store status variables clause_count store_words at_ end_ used empty c fuel
  let status ← (if ((status == LRAT_ACCEPTED) && (at_ != end_)) then (do
      let status := LRAT_MALFORMED
      pure status)
    else (do
      pure status))
  let last : UInt32 := clause_count
  let at_ := end_
  let end_ := (if ok then (end_ + step_words) else (0 : UInt32))
  let (starts, lengths, alive, store, assign, trail, status, additions, deletions, _at_, _used, empty, _last) ← lrat_check.loop5 words starts lengths alive store assign trail status additions deletions variables max_id store_words at_ end_ used empty last fuel
  let status ← (if ((status == LRAT_ACCEPTED) && (!empty)) then (do
      let status := LRAT_NO_EMPTY
      pure status)
    else (do
      pure status))
  let out ← (if (decide ((out.size.toUInt32) >= (3 : UInt32))) then (do
      let out := out.setIfInBounds (0 : UInt32).toNat status
      let out := out.setIfInBounds (1 : UInt32).toNat additions
      let out := out.setIfInBounds (2 : UInt32).toNat deletions
      pure out)
    else (do
      pure out))
  pure (status, starts, lengths, alive, store, assign, trail, out)

theorem checker_eq_body (words starts lengths : Array UInt32) (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (fuel : Nat) :
    lrat_check words starts lengths alive store assign trail out fuel =
      checkerBody words starts lengths alive store assign trail out
        (parseHeader words starts lengths alive store assign trail out) fuel := by
  simp only [lrat_check, checkerBody, parseHeader, fits_spec, bind, Option.bind, Option.pure_def]
  rfl

structure HeaderValid (words starts lengths : Array UInt32) (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (h : HeaderData) : Prop where
  variables_eq : h.variables = words.getD 1 0
  count_eq : h.clause_count = words.getD 2 0
  literalEnd_eq : h.literal_end.toNat = 8 + (words.getD 3 0).toNat
  startBound : 8 ≤ h.literal_end.toNat
  literalCapacity : h.literal_end.toNat ≤ words.size
  fullCapacity : (h.literal_end + h.step_words).toNat ≤ words.size
  startsCapacity : h.max_id.toNat < starts.size
  lengthsCapacity : h.max_id.toNat < lengths.size
  aliveCapacity : h.max_id < alive.size.toUInt32
  storeCapacity : h.store_words.toNat ≤ store.size
  assignCapacity : h.variables.toNat ≤ assign.size
  trailCapacity : h.variables.toNat ≤ trail.size
  countBound : h.clause_count ≤ h.max_id
  maxBound : h.max_id.toNat < 4294967295

theorem parseHeader_valid (words starts lengths : Array UInt32) (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32)
    (good : (parseHeader words starts lengths alive store assign trail out).ok = true) :
    HeaderValid words starts lengths alive store assign trail out (parseHeader words starts lengths alive store assign trail out) := by
  simp only [parseHeader, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at good
  simp only [and_assoc] at good
  obtain ⟨ws, magic, os, litfit, stepfit, whole, sc, lc, ac, stc, asc, trc, cc⟩ := good
  simp only [ws, magic, os, and_self, ite_true] at litfit stepfit whole sc lc ac stc asc trc cc
  simp only [litfit, and_self, ite_true] at stepfit whole
  simp only [parseHeader, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    ws, magic, os, litfit, and_self, ite_true]
  have wordMod : words.size.toUInt32.toNat ≤ words.size := Nat.mod_le _ _
  have startMod : starts.size.toUInt32.toNat ≤ starts.size := Nat.mod_le _ _
  have lengthMod : lengths.size.toUInt32.toNat ≤ lengths.size := Nat.mod_le _ _
  have storeMod : store.size.toUInt32.toNat ≤ store.size := Nat.mod_le _ _
  have assignMod : assign.size.toUInt32.toNat ≤ assign.size := Nat.mod_le _ _
  have trailMod : trail.size.toUInt32.toNat ≤ trail.size := Nat.mod_le _ _
  have sum : (LRAT_HEADER_WORDS + words.getD 3 0).toNat = 8 + (words.getD 3 0).toNat := by
    apply add_exact
    exact Nat.lt_of_le_of_lt litfit words.size.toUInt32.toNat_lt
  constructor
  · rfl
  · rfl
  · exact sum
  · change 8 ≤ (LRAT_HEADER_WORDS + words.getD 3 0).toNat
    rw [sum]; omega
  · change (LRAT_HEADER_WORDS + words.getD 3 0).toNat ≤ words.size
    rw [sum]; exact Nat.le_trans litfit wordMod
  · rw [whole]; exact wordMod
  · exact Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp sc) startMod
  · exact Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp lc) lengthMod
  · exact ac
  · exact Nat.le_trans (UInt32.le_iff_toNat_le.mp stc) storeMod
  · exact Nat.le_trans (UInt32.le_iff_toNat_le.mp asc) assignMod
  · exact Nat.le_trans (UInt32.le_iff_toNat_le.mp trc) trailMod
  · exact cc
  · change (words.getD 5 0).toNat < 4294967295
    change words.getD 5 0 < alive.size.toUInt32 at ac
    have := UInt32.lt_iff_toNat_lt.mp ac
    have := alive.size.toUInt32.toNat_lt
    omega

theorem checkerBody_accepted_header (words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (h : HeaderData) (fuel : Nat)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (run : checkerBody words starts lengths alive store assign trail out h fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    h.ok = true := by
  cases good : h.ok with
  | true => rfl
  | false =>
    cases fuel with
    | zero => simp [checkerBody, good, lrat_check.loop1] at run
    | succ fuel =>
      simp [checkerBody, good, lrat_check.loop1, lrat_check.loop2, lrat_check.loop3, lrat_check.loop5,
        LRAT_ACCEPTED, LRAT_CAPACITY, option_ite] at run

theorem checkerBody_no_model (words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (h : HeaderData) (fuel : Nat)
    (validHeader : HeaderValid words starts lengths alive store assign trail out h)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (run : checkerBody words starts lengths alive store assign trail out h fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o))
    (a : RupCheck.Assignment) (input : InitialModels words h.clause_count.toNat 8 a) : False := by
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
          obtain ⟨decoded, _, scratchSize, scratchZero⟩ := production_initialization fuel words starts lengths alive store assign
            h.variables h.clause_count h.max_id h.store_words 8 h.literal_end live liveEnd scratch scratchEnd
            is il iv it iat iused iempty ic a validHeader.startsCapacity validHeader.lengthsCapacity
            validHeader.aliveCapacity validHeader.storeCapacity validHeader.assignCapacity validHeader.literalCapacity
            (by rw [UInt32.le_iff_toNat_le]; exact validHeader.startBound) validHeader.countBound input liveRun assignRun initialRun
          have state : StepModel is il iv it scratch trail h.variables h.max_id h.store_words iused a :=
            ⟨⟨decoded.startCapacity, decoded.lengthCapacity, decoded.aliveCapacity, decoded.storeCapacity,
              UInt32.le_iff_toNat_le.mp decoded.usedBound, decoded.stored, decoded.valid, decoded.models⟩,
              by rw [scratchSize]; exact validHeader.assignCapacity, validHeader.trailCapacity, scratchZero⟩
          have impossible := (steps_loop_models fuel words h.variables h.max_id h.store_words (h.literal_end + h.step_words) a
            validHeader.fullCapacity is il iv it scratch trail 0 0 h.literal_end iused iempty h.clause_count state decoded.noEmpty
            fs fl fv ft fx fy fadds fdels fat fused true flast stepRun).2
          contradiction

/-- Every accepted call to the extracted production checker refutes its
independently decoded initial formula. All parser, store, and scratch
preconditions are derived from the call itself. -/
theorem production_record_sound (words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (fuel : Nat)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (run : lrat_check words starts lengths alive store assign trail out fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    ¬ ∃ a, InitialModels words (words.getD 2 0).toNat 8 a := by
  rw [checker_eq_body] at run
  have good := checkerBody_accepted_header (run := run)
  have header := parseHeader_valid words starts lengths alive store assign trail out good
  intro ⟨a, model⟩
  apply checkerBody_no_model (validHeader := header) (run := run) (a := a)
  rw [header.count_eq]
  exact model

end Oak.LRATChecker
