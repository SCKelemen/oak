import Oak.LRATCheckerState
import Oak.LRATBounds
import Oak.LRATRUPValidity

/-!
Literal-store refinement for the extracted production checker. The copy
theorems characterize the exact written interval and preserve all other cells.
Database insertion then connects these writes to the clause entailed by RUP.
Whole-record decoding and scratch/trail preservation are separate obligations.
-/

namespace Oak.LRATChecker

theorem fits_iff (at_ count limit : UInt32) (fuel : Nat) :
    lrat_fits at_ count limit fuel = some true ↔
      at_.toNat + count.toNat ≤ limit.toNat := LRATBounds.fits_iff at_ count limit fuel

theorem add_exact (a b : UInt32) (bound : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt bound

theorem set_word_getD (words : Array UInt32) (at_ k : Nat) (value : UInt32)
    (hk : k < words.size) :
    (words.setIfInBounds at_ value).getD k 0 =
      if at_ = k then value else words.getD k 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases same : at_ = k
  · subst at_
    simp [hk]
  · simp [same]

/-- The production addition-copy loop writes exactly the unprocessed suffix
of the target clause and changes no other literal-store word. Bounds exclude
both machine-index wrapping and array access outside the supplied spans. -/
theorem copy_loop_spec (fuel : Nat) (words store : Array UInt32)
    (used n lits_at j : UInt32) (store' : Array UInt32) (j' : UInt32)
    (progress : j ≤ n)
    (dest : used.toNat + n.toNat ≤ store.size)
    (dest32 : used.toNat + n.toNat < 4294967296)
    (_source : lits_at.toNat + n.toNat ≤ words.size)
    (source32 : lits_at.toNat + n.toNat < 4294967296)
    (run : lrat_check.loop7 words store used n lits_at j fuel = some (store', j')) :
    j' = n ∧ store'.size = store.size ∧
      ∀ k, k < store.size → store'.getD k 0 =
        if used.toNat + j.toNat ≤ k ∧ k < used.toNat + n.toNat then
          words.getD (lits_at.toNat + (k - used.toNat)) 0 else store.getD k 0 := by
  induction fuel generalizing store j store' j' with
  | zero => simp [lrat_check.loop7] at run
  | succ fuel ih =>
    by_cases advance : j < n
    · have jn := UInt32.lt_iff_toNat_lt.mp advance
      have js := LRATRUP.counter_succ j n advance
      have de : (used + j).toNat = used.toNat + j.toNat := add_exact used j (by omega)
      have se : (lits_at + j).toNat = lits_at.toNat + j.toNat := add_exact lits_at j (by omega)
      simp only [lrat_check.loop7, decide_eq_true advance, ite_true] at run
      obtain ⟨done, size, values⟩ := ih _ (j + 1) _ _
        (by rw [UInt32.le_iff_toNat_le, js]; omega) (by simpa using dest) run
      refine ⟨done, size.trans Array.size_setIfInBounds, ?_⟩
      intro k hk
      rw [values k (by simpa using hk), set_word_getD store _ k _ hk, de, se, js]
      by_cases here : used.toNat + j.toNat = k
      · have inside : used.toNat + j.toNat ≤ k ∧ k < used.toNat + n.toNat := by omega
        have outsideNext : ¬(used.toNat + (j.toNat + 1) ≤ k ∧ k < used.toNat + n.toNat) := by omega
        rw [if_neg outsideNext, if_pos here, if_pos inside]
        congr 1
        omega
      · have same : (used.toNat + (j.toNat + 1) ≤ k ∧ k < used.toNat + n.toNat) ↔
            (used.toNat + j.toNat ≤ k ∧ k < used.toNat + n.toNat) := by omega
        simp only [if_neg here, same]
    · have done : j = n := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.le_iff_toNat_le] at progress
        rw [UInt32.lt_iff_toNat_lt] at advance
        omega
      simp only [lrat_check.loop7, decide_eq_false advance, Bool.false_eq_true,
        ite_false, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨done, rfl, ?_⟩
      intro k hk
      rw [done, if_neg (by omega)]

/-- A completed production copy contains the exact decoded target clause. -/
theorem copied_clause_eq (fuel : Nat) (words store : Array UInt32)
    (used n lits_at : UInt32) (store' : Array UInt32) (j' : UInt32)
    (dest : used.toNat + n.toNat ≤ store.size)
    (dest32 : used.toNat + n.toNat < 4294967296)
    (source : lits_at.toNat + n.toNat ≤ words.size)
    (source32 : lits_at.toNat + n.toNat < 4294967296)
    (run : lrat_check.loop7 words store used n lits_at 0 fuel = some (store', j')) :
    LRATRUP.wordClause store' used n = LRATRUP.wordClause words lits_at n := by
  obtain ⟨done, size, values⟩ := copy_loop_spec fuel words store used n lits_at 0 store' j'
    (by simp) dest dest32 source source32 run
  unfold LRATRUP.wordClause
  apply List.map_congr_left
  intro k hk
  have kn : k < n.toNat := List.mem_range.mp hk
  have k32 : (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' (Nat.lt_trans kn n.toNat_lt)
  have de : (used + UInt32.ofNat k).toNat = used.toNat + k := by
    rw [add_exact used _ (by rw [k32]; omega), k32]
  have se : (lits_at + UInt32.ofNat k).toNat = lits_at.toNat + k := by
    rw [add_exact lits_at _ (by rw [k32]; omega), k32]
  rw [de, se, values _ (by omega), if_pos (by simp only [UInt32.toNat_zero]; omega)]
  congr 2
  omega

theorem array_getD_set_ne {α : Type} (a : Array α) (at_ k : Nat) (value fallback : α)
    (different : at_ ≠ k) :
    (a.setIfInBounds at_ value).getD k fallback = a.getD k fallback := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne different]

theorem array_getD_set_self {α : Type} (a : Array α) (at_ : Nat) (value fallback : α)
    (bound : at_ < a.size) :
    (a.setIfInBounds at_ value).getD at_ fallback = value := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt bound, Option.getD_some]

theorem wordClause_ext (before after : Array UInt32) (start count : UInt32)
    (same : ∀ k : UInt32, k < count → before.getD (start + k).toNat 0 = after.getD (start + k).toNat 0) :
    LRATRUP.wordClause before start count = LRATRUP.wordClause after start count := by
  unfold LRATRUP.wordClause
  apply List.map_congr_left
  intro k hk
  have kn := List.mem_range.mp hk
  have k32 : (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' (Nat.lt_trans kn count.toNat_lt)
  rw [same (UInt32.ofNat k) (by rw [UInt32.lt_iff_toNat_lt, k32]; exact kn)]

/-- All live clauses occupy the already-used prefix of the literal store. -/
def StoredBefore (starts lengths : Array UInt32) (alive : Array UInt8) (used max_id : UInt32) : Prop :=
  ∀ id : Nat, 0 < id → id ≤ max_id.toNat → alive.getD id 0 ≠ 0 →
    (starts.getD id 0).toNat + (lengths.getD id 0).toNat ≤ used.toNat

theorem copy_preserves_database (fuel : Nat) (words store : Array UInt32)
    (starts lengths : Array UInt32) (alive : Array UInt8) (max_id used n lits_at : UInt32)
    (store' : Array UInt32) (j' : UInt32)
    (stored : StoredBefore starts lengths alive used max_id)
    (dest : used.toNat + n.toNat ≤ store.size)
    (dest32 : used.toNat + n.toNat < 4294967296)
    (source : lits_at.toNat + n.toNat ≤ words.size)
    (source32 : lits_at.toNat + n.toNat < 4294967296)
    (run : lrat_check.loop7 words store used n lits_at 0 fuel = some (store', j')) :
    LRATRUP.wordDatabase starts lengths alive store' max_id =
      LRATRUP.wordDatabase starts lengths alive store max_id := by
  obtain ⟨done, size, values⟩ := copy_loop_spec fuel words store used n lits_at 0 store' j'
    (by simp) dest dest32 source source32 run
  funext id
  unfold LRATRUP.wordDatabase
  split
  · rename_i live
    congr 1
    apply wordClause_ext
    intro k hk
    have before := stored id live.1 live.2.1 live.2.2
    have kn := UInt32.lt_iff_toNat_lt.mp hk
    have exactIndex : (starts.getD id 0 + k).toNat = (starts.getD id 0).toNat + k.toNat := by
      apply add_exact
      have := used.toNat_lt
      omega
    rw [exactIndex, values _ (by omega), if_neg (by simp only [UInt32.toNat_zero]; omega)]
  · rfl

/-- The metadata writes in both initial decoding and addition implement one
database insertion, including replacement at an already occupied slot. -/
theorem metadata_insert_eq (starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (max_id id used n : UInt32)
    (positive : 0 < id) (upper : id ≤ max_id)
    (startCap : id.toNat < starts.size) (lengthCap : id.toNat < lengths.size) (aliveCap : id.toNat < alive.size) :
    LRATRUP.wordDatabase (starts.setIfInBounds id.toNat used) (lengths.setIfInBounds id.toNat n)
      (alive.setIfInBounds id.toNat 1) store max_id =
    RupCheck.insert (LRATRUP.wordDatabase starts lengths alive store max_id) id.toNat
      (LRATRUP.wordClause store used n) := by
  funext key
  by_cases same : key = id.toNat
  · subst key
    have lower : 0 < id.toNat := UInt32.lt_iff_toNat_lt.mp positive
    have higher : id.toNat ≤ max_id.toNat := UInt32.le_iff_toNat_le.mp upper
    simp only [RupCheck.insert, LRATRUP.wordDatabase, ite_true,
      array_getD_set_self starts id.toNat used 0 startCap,
      array_getD_set_self lengths id.toNat n 0 lengthCap,
      array_getD_set_self alive id.toNat 1 0 aliveCap]
    rw [if_pos ⟨lower, higher, by decide⟩]
  · have different : id.toNat ≠ key := Ne.symm same
    simp only [RupCheck.insert, if_neg same, LRATRUP.wordDatabase,
      array_getD_set_ne starts id.toNat key used 0 different,
      array_getD_set_ne lengths id.toNat key n 0 different,
      array_getD_set_ne alive id.toNat key 1 0 different]

/-- The copy plus metadata writes store exactly the original target clause,
with every previous database entry preserved except the selected id. -/
theorem copied_database_insert (fuel : Nat) (words store : Array UInt32)
    (starts lengths : Array UInt32) (alive : Array UInt8) (max_id id used n lits_at : UInt32)
    (store' : Array UInt32) (j' : UInt32)
    (stored : StoredBefore starts lengths alive used max_id)
    (positive : 0 < id) (upper : id ≤ max_id)
    (startCap : id.toNat < starts.size) (lengthCap : id.toNat < lengths.size) (aliveCap : id.toNat < alive.size)
    (dest : used.toNat + n.toNat ≤ store.size) (dest32 : used.toNat + n.toNat < 4294967296)
    (source : lits_at.toNat + n.toNat ≤ words.size) (source32 : lits_at.toNat + n.toNat < 4294967296)
    (run : lrat_check.loop7 words store used n lits_at 0 fuel = some (store', j')) :
    LRATRUP.wordDatabase (starts.setIfInBounds id.toNat used) (lengths.setIfInBounds id.toNat n)
      (alive.setIfInBounds id.toNat 1) store' max_id =
    RupCheck.insert (LRATRUP.wordDatabase starts lengths alive store max_id) id.toNat
      (LRATRUP.wordClause words lits_at n) := by
  rw [metadata_insert_eq starts lengths alive store' max_id id used n positive upper startCap lengthCap aliveCap,
    copy_preserves_database fuel words store starts lengths alive max_id used n lits_at store' j'
      stored dest dest32 source source32 run,
    copied_clause_eq fuel words store used n lits_at store' j' dest dest32 source source32 run]

/-- An accepted initial-clause literal scan is the same exact copy as the
addition loop, and every copied literal names a declared variable. This
follows the production validation branch; validity is a conclusion. -/
theorem initial_literal_scan_spec (fuel : Nat) (words store : Array UInt32)
    (status variables at_ used n j : UInt32) (store' : Array UInt32) (status' j' : UInt32)
    (run : lrat_check.loop4 words store status variables at_ used n j fuel = some (store', status', j'))
    (accepted : status' = LRAT_ACCEPTED) :
    status = LRAT_ACCEPTED ∧
    lrat_check.loop7 words store used n (at_ + 1) j fuel = some (store', j') ∧
    ∀ k : UInt32, j ≤ k → k < n → words.getD (at_ + 1 + k).toNat 0 / 2 < variables := by
  induction fuel generalizing store status j store' status' j' with
  | zero => simp [lrat_check.loop4] at run
  | succ fuel ih =>
    by_cases enter : j < n ∧ status = LRAT_ACCEPTED
    · obtain ⟨hj, hs⟩ := enter
      subst status
      by_cases valid : words.getD (at_ + 1 + j).toNat 0 / 2 < variables
      · simp only [lrat_check.loop4, hj, decide_true, beq_self_eq_true, Bool.and_self,
          ite_true, valid, bind, Option.bind, Option.pure_def] at run
        obtain ⟨hs, copy, vars⟩ := ih _ LRAT_ACCEPTED (j + 1) _ _ _ run accepted
        refine ⟨rfl, ?_, ?_⟩
        · simp only [lrat_check.loop7, hj, decide_true, ite_true, copy]
        · intro k lower upper
          by_cases same : k = j
          · simpa only [same] using valid
          · apply vars k ?_ upper
            rw [UInt32.le_iff_toNat_le, LRATRUP.counter_succ j n hj]
            have := UInt32.le_iff_toNat_le.mp lower
            have unequal : k.toNat ≠ j.toNat := fun h => same (UInt32.toNat_inj.mp h)
            omega
      · simp only [lrat_check.loop4, hj, decide_true, beq_self_eq_true, Bool.and_self,
          ite_true, decide_eq_false valid, Bool.false_eq_true, ite_false,
          bind, Option.bind, Option.pure_def] at run
        have impossible := (ih store LRAT_MALFORMED (j + 1) _ _ _ run accepted).1
        contradiction
    · have guard : (decide (j < n) && (status == LRAT_ACCEPTED)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        by_cases hj : j < n
        · exact Or.inr (fun hs => enter ⟨hj, hs⟩)
        · exact Or.inl hj
      simp only [lrat_check.loop4, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl⟩
      have done : ¬j < n := fun hj => enter ⟨hj, accepted⟩
      refine ⟨accepted, ?_, ?_⟩
      · simp [lrat_check.loop7, done]
      · intro k lower upper
        have := UInt32.le_iff_toNat_le.mp lower
        have := UInt32.lt_iff_toNat_lt.mp upper
        rw [UInt32.lt_iff_toNat_lt] at done
        omega

/-- RUP's mutable parameters include the database, but the production body
only mutates assignment/trail scratch. This ties the database used in its
entailment theorem to the database the caller receives back. -/
theorem rup_database_unchanged (fuel : Nat) (words : Array UInt32)
    (target_at target_n hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id status : UInt32) (starts' lengths' : Array UInt32)
    (alive' : Array UInt8) (store' : Array UInt32) (assign' : Array UInt8) (trail' : Array UInt32)
    (run : lrat_rup words target_at target_n hints_at hints_n starts lengths alive store assign trail
      variables max_id fuel = some (status, starts', lengths', alive', store', assign', trail')) :
    starts' = starts ∧ lengths' = lengths ∧ alive' = alive ∧ store' = store := by
  rw [rup_extraction_eq] at run
  unfold LRATRUP.lrat_rup at run
  cases targetRun : LRATRUP.lrat_rup.loop1 words target_at target_n assign trail variables LRATRUP.LRAT_ACCEPTED false 0 0 fuel with
  | none => simp [targetRun] at run
  | some state =>
    rcases state with ⟨a1, t1, s1, q1, u1, i1⟩
    simp only [targetRun, bind, Option.bind, Option.pure_def] at run
    cases hintsRun : LRATRUP.lrat_rup.loop2 words hints_at hints_n starts lengths alive store a1 t1 max_id s1 q1 u1 0 fuel with
    | none => simp [hintsRun] at run
    | some state =>
      rcases state with ⟨a2, t2, s2, q2, u2, h2⟩
      simp only [hintsRun] at run
      cases undoRun : LRATRUP.lrat_undo a2 t2 u2 fuel with
      | none => split at run <;> simp [undoRun] at run
      | some state =>
        rcases state with ⟨unused, a3, t3⟩
        split at run <;>
          (try simp only [undoRun, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at run) <;>
          exact ⟨run.2.1.symm, run.2.2.1.symm, run.2.2.2.1.symm, run.2.2.2.2.1.symm⟩

/-- Compose actual RUP execution with the actual store-copy loop and metadata
writes: every old model satisfies the resulting database. Caller range,
scratch, and live-variable invariants are explicit rather than assumed as a
logical propagation certificate. -/
theorem production_addition_preserves_models (fuel : Nat) (words store : Array UInt32)
    (starts lengths : Array UInt32) (alive : Array UInt8) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id id used n lits_at hints_at hints_n : UInt32)
    (rupStarts rupLengths : Array UInt32) (rupAlive : Array UInt8) (rupStore : Array UInt32)
    (rupAssign : Array UInt8) (rupTrail : Array UInt32) (store' : Array UInt32) (j' : UInt32)
    (stored : StoredBefore starts lengths alive used max_id)
    (valid : LRATRUP.LiveVariables starts lengths alive store variables max_id)
    (capacity : variables.toNat ≤ assign.size)
    (zero : ∀ v, v < variables.toNat → assign.getD v 0 = 0)
    (positive : 0 < id) (upper : id ≤ max_id)
    (startCap : id.toNat < starts.size) (lengthCap : id.toNat < lengths.size) (aliveCap : id.toNat < alive.size)
    (dest : used.toNat + n.toNat ≤ store.size) (dest32 : used.toNat + n.toNat < 4294967296)
    (source : lits_at.toNat + n.toNat ≤ words.size) (source32 : lits_at.toNat + n.toNat < 4294967296)
    (rup : lrat_rup words lits_at n hints_at hints_n starts lengths alive store assign trail variables max_id fuel =
      some (LRAT_ACCEPTED, rupStarts, rupLengths, rupAlive, rupStore, rupAssign, rupTrail))
    (copy : lrat_check.loop7 words rupStore used n lits_at 0 fuel = some (store', j'))
    (a : RupCheck.Assignment) (models : RupCheck.Models a (LRATRUP.wordDatabase starts lengths alive store max_id)) :
    RupCheck.Models a (LRATRUP.wordDatabase (rupStarts.setIfInBounds id.toNat used)
      (rupLengths.setIfInBounds id.toNat n) (rupAlive.setIfInBounds id.toNat 1) store' max_id) := by
  obtain ⟨sameStarts, sameLengths, sameAlive, sameStore⟩ := rup_database_unchanged fuel words lits_at n hints_at hints_n starts lengths alive store
    assign trail variables max_id LRAT_ACCEPTED rupStarts rupLengths rupAlive rupStore rupAssign rupTrail rup
  subst rupStarts rupLengths rupAlive rupStore
  rw [copied_database_insert fuel words store starts lengths alive max_id id used n lits_at store' j'
    stored positive upper startCap lengthCap aliveCap dest dest32 source source32 copy]
  apply RupCheck.insert_preserves models
  rw [rup_extraction_eq] at rup
  exact LRATRUP.production_rup_entails fuel words lits_at n hints_at hints_n starts lengths alive store assign trail
    variables max_id capacity zero valid starts lengths alive store rupAssign rupTrail rup a models

/-- Appending a clause preserves the used-prefix invariant, even if the
selected id replaces an older live clause. -/
theorem insertion_stored_before (starts lengths : Array UInt32) (alive : Array UInt8)
    (max_id id used n : UInt32) (stored : StoredBefore starts lengths alive used max_id)
    (startCap : id.toNat < starts.size) (lengthCap : id.toNat < lengths.size)
    (dest32 : used.toNat + n.toNat < 4294967296) :
    StoredBefore (starts.setIfInBounds id.toNat used) (lengths.setIfInBounds id.toNat n)
      (alive.setIfInBounds id.toNat 1) (used + n) max_id := by
  intro key lower upper live
  rw [add_exact used n dest32]
  by_cases same : id.toNat = key
  · subst key
    rw [array_getD_set_self starts id.toNat used 0 startCap,
      array_getD_set_self lengths id.toNat n 0 lengthCap]
    exact Nat.le_refl _
  · rw [array_getD_set_ne alive id.toNat key 1 0 same] at live
    rw [array_getD_set_ne starts id.toNat key used 0 same,
      array_getD_set_ne lengths id.toNat key n 0 same]
    have before := stored key lower upper live
    omega

/-- Every copied literal is a declared variable if every source literal is.
The equality is about stored words, before semantic literal decoding. -/
theorem copied_literals_valid (fuel : Nat) (words store : Array UInt32)
    (used n lits_at variables : UInt32) (store' : Array UInt32) (j' : UInt32)
    (dest : used.toNat + n.toNat ≤ store.size) (dest32 : used.toNat + n.toNat < 4294967296)
    (source : lits_at.toNat + n.toNat ≤ words.size) (source32 : lits_at.toNat + n.toNat < 4294967296)
    (valid : ∀ k : UInt32, k < n → words.getD (lits_at + k).toNat 0 / 2 < variables)
    (run : lrat_check.loop7 words store used n lits_at 0 fuel = some (store', j')) :
    ∀ k : UInt32, k < n → store'.getD (used + k).toNat 0 / 2 < variables := by
  obtain ⟨done, size, values⟩ := copy_loop_spec fuel words store used n lits_at 0 store' j'
    (by simp) dest dest32 source source32 run
  intro k hk
  have kn := UInt32.lt_iff_toNat_lt.mp hk
  have de := add_exact used k (by omega)
  have se := add_exact lits_at k (by omega)
  have next := valid k hk
  rw [se] at next
  rw [de, values _ (by omega), if_pos (by simp only [UInt32.toNat_zero]; omega)]
  simpa only [Nat.add_sub_cancel_left] using next

/-- Copying into the unused store suffix preserves variable validity in every
old live clause. -/
theorem copy_preserves_variables (fuel : Nat) (words store : Array UInt32)
    (starts lengths : Array UInt32) (alive : Array UInt8) (variables max_id used n lits_at : UInt32)
    (store' : Array UInt32) (j' : UInt32)
    (stored : StoredBefore starts lengths alive used max_id)
    (valid : LRATRUP.LiveVariables starts lengths alive store variables max_id)
    (dest : used.toNat + n.toNat ≤ store.size) (dest32 : used.toNat + n.toNat < 4294967296)
    (source : lits_at.toNat + n.toNat ≤ words.size) (source32 : lits_at.toNat + n.toNat < 4294967296)
    (run : lrat_check.loop7 words store used n lits_at 0 fuel = some (store', j')) :
    LRATRUP.LiveVariables starts lengths alive store' variables max_id := by
  obtain ⟨done, size, values⟩ := copy_loop_spec fuel words store used n lits_at 0 store' j'
    (by simp) dest dest32 source source32 run
  intro id upper lower live k hk
  have before := stored id.toNat (UInt32.lt_iff_toNat_lt.mp lower) (UInt32.le_iff_toNat_le.mp upper) live
  have kn := UInt32.lt_iff_toNat_lt.mp hk
  have exactIndex := add_exact (starts.getD id.toNat 0) k (by have := used.toNat_lt; omega)
  have old := valid id upper lower live k hk
  rw [exactIndex] at old ⊢
  rw [values _ (by omega), if_neg (by simp only [UInt32.toNat_zero]; omega)]
  exact old

/-- Metadata insertion preserves all live-variable checks when the new
stored clause and the old database both have declared variables. -/
theorem insertion_variables (starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (variables max_id id used n : UInt32)
    (valid : LRATRUP.LiveVariables starts lengths alive store variables max_id)
    (newValid : ∀ k : UInt32, k < n → store.getD (used + k).toNat 0 / 2 < variables)
    (startCap : id.toNat < starts.size) (lengthCap : id.toNat < lengths.size) :
    LRATRUP.LiveVariables (starts.setIfInBounds id.toNat used) (lengths.setIfInBounds id.toNat n)
      (alive.setIfInBounds id.toNat 1) store variables max_id := by
  intro key upper lower live k hk
  by_cases same : id.toNat = key.toNat
  · rw [← same, array_getD_set_self lengths id.toNat n 0 lengthCap] at hk
    rw [← same, array_getD_set_self starts id.toNat used 0 startCap]
    exact UInt32.lt_iff_toNat_lt.mp (newValid k hk)
  · rw [array_getD_set_ne alive id.toNat key.toNat 1 0 same] at live
    rw [array_getD_set_ne lengths id.toNat key.toNat n 0 same] at hk
    rw [array_getD_set_ne starts id.toNat key.toNat used 0 same]
    exact valid key upper lower live k hk

/-- One accepted production initial-clause scan inserts exactly its input
clause, with store-prefix and declared-variable invariants established for
the resulting database. Its variable checks are proved from execution. -/
theorem production_initial_clause (fuel : Nat) (words store : Array UInt32)
    (starts lengths : Array UInt32) (alive : Array UInt8)
    (variables max_id id used n at_ : UInt32) (store' : Array UInt32) (j' : UInt32)
    (stored : StoredBefore starts lengths alive used max_id)
    (valid : LRATRUP.LiveVariables starts lengths alive store variables max_id)
    (positive : 0 < id) (upper : id ≤ max_id)
    (startCap : id.toNat < starts.size) (lengthCap : id.toNat < lengths.size) (aliveCap : id.toNat < alive.size)
    (dest : used.toNat + n.toNat ≤ store.size) (dest32 : used.toNat + n.toNat < 4294967296)
    (source : (at_ + 1).toNat + n.toNat ≤ words.size) (source32 : (at_ + 1).toNat + n.toNat < 4294967296)
    (run : lrat_check.loop4 words store LRAT_ACCEPTED variables at_ used n 0 fuel = some (store', LRAT_ACCEPTED, j')) :
    LRATRUP.wordDatabase (starts.setIfInBounds id.toNat used) (lengths.setIfInBounds id.toNat n)
      (alive.setIfInBounds id.toNat 1) store' max_id =
      RupCheck.insert (LRATRUP.wordDatabase starts lengths alive store max_id) id.toNat
        (LRATRUP.wordClause words (at_ + 1) n) ∧
    StoredBefore (starts.setIfInBounds id.toNat used) (lengths.setIfInBounds id.toNat n)
      (alive.setIfInBounds id.toNat 1) (used + n) max_id ∧
    LRATRUP.LiveVariables (starts.setIfInBounds id.toNat used) (lengths.setIfInBounds id.toNat n)
      (alive.setIfInBounds id.toNat 1) store' variables max_id := by
  obtain ⟨status, copy, vars⟩ := initial_literal_scan_spec fuel words store LRAT_ACCEPTED variables at_ used n 0
    store' LRAT_ACCEPTED j' run rfl
  refine ⟨copied_database_insert fuel words store starts lengths alive max_id id used n (at_ + 1) store' j'
      stored positive upper startCap lengthCap aliveCap dest dest32 source source32 copy,
    insertion_stored_before starts lengths alive max_id id used n stored startCap lengthCap dest32, ?_⟩
  apply insertion_variables starts lengths alive store' variables max_id id used n
    (copy_preserves_variables fuel words store starts lengths alive variables max_id used n (at_ + 1) store' j'
      stored valid dest dest32 source source32 copy) _ startCap lengthCap
  exact copied_literals_valid fuel words store used n (at_ + 1) variables store' j' dest dest32 source source32
    (fun k hk => vars k (by simp) hk) copy

/-- The production framing guards imply ordinary natural-number ranges for
one initial clause. In particular, computing `at + 1` cannot wrap because
the length word was already required to precede the endpoint. -/
theorem initial_clause_bounds (fuel : Nat) (words store : Array UInt32)
    (at_ end_ used n store_words : UInt32)
    (header : at_ < end_) (wordCapacity : end_.toNat ≤ words.size)
    (storeCapacity : store_words.toNat ≤ store.size)
    (sourceFit : lrat_fits (at_ + 1) n end_ fuel = some true)
    (destFit : lrat_fits used n store_words fuel = some true) :
    (at_ + 1).toNat = at_.toNat + 1 ∧
    (at_ + 1).toNat + n.toNat ≤ words.size ∧
    (at_ + 1).toNat + n.toNat < 4294967296 ∧
    used.toNat + n.toNat ≤ store.size ∧ used.toNat + n.toNat < 4294967296 := by
  have source := (fits_iff (at_ + 1) n end_ fuel).mp sourceFit
  have dest := (fits_iff used n store_words fuel).mp destFit
  have endBound := end_.toNat_lt
  have storeBound := store_words.toNat_lt
  have headerBound := UInt32.lt_iff_toNat_lt.mp header
  refine ⟨?_, by omega, by omega, by omega, by omega⟩
  simpa only [UInt32.toNat_one] using add_exact at_ 1 (by simp only [UInt32.toNat_one]; omega)

/-- After an accepted RUP addition, the actual store copy and metadata writes
preserve the invariants needed by subsequent RUP calls. The target-variable
condition is derived from RUP execution, including tautological targets. -/
theorem production_addition_invariants (fuel : Nat) (words store : Array UInt32)
    (starts lengths : Array UInt32) (alive : Array UInt8) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id id used n lits_at hints_at hints_n : UInt32)
    (rupStarts rupLengths : Array UInt32) (rupAlive : Array UInt8) (rupStore : Array UInt32)
    (rupAssign : Array UInt8) (rupTrail : Array UInt32) (store' : Array UInt32) (j' : UInt32)
    (stored : StoredBefore starts lengths alive used max_id)
    (valid : LRATRUP.LiveVariables starts lengths alive store variables max_id)
    (startCap : id.toNat < starts.size) (lengthCap : id.toNat < lengths.size)
    (dest : used.toNat + n.toNat ≤ store.size) (dest32 : used.toNat + n.toNat < 4294967296)
    (source : lits_at.toNat + n.toNat ≤ words.size) (source32 : lits_at.toNat + n.toNat < 4294967296)
    (rup : lrat_rup words lits_at n hints_at hints_n starts lengths alive store assign trail variables max_id fuel =
      some (LRAT_ACCEPTED, rupStarts, rupLengths, rupAlive, rupStore, rupAssign, rupTrail))
    (copy : lrat_check.loop7 words rupStore used n lits_at 0 fuel = some (store', j')) :
    StoredBefore (rupStarts.setIfInBounds id.toNat used) (rupLengths.setIfInBounds id.toNat n)
      (rupAlive.setIfInBounds id.toNat 1) (used + n) max_id ∧
    LRATRUP.LiveVariables (rupStarts.setIfInBounds id.toNat used) (rupLengths.setIfInBounds id.toNat n)
      (rupAlive.setIfInBounds id.toNat 1) store' variables max_id ∧ store'.size = store.size := by
  obtain ⟨sameStarts, sameLengths, sameAlive, sameStore⟩ := rup_database_unchanged fuel words lits_at n hints_at hints_n starts lengths alive store
    assign trail variables max_id LRAT_ACCEPTED rupStarts rupLengths rupAlive rupStore rupAssign rupTrail rup
  subst rupStarts rupLengths rupAlive rupStore
  refine ⟨insertion_stored_before starts lengths alive max_id id used n stored startCap lengthCap dest32, ?_,
    (copy_loop_spec fuel words store used n lits_at 0 store' j' (by simp) dest dest32 source source32 copy).2.1⟩
  apply insertion_variables starts lengths alive store' variables max_id id used n
    (copy_preserves_variables fuel words store starts lengths alive variables max_id used n lits_at store' j'
      stored valid dest dest32 source source32 copy) _ startCap lengthCap
  apply copied_literals_valid fuel words store used n lits_at variables store' j' dest dest32 source source32 _ copy
  rw [rup_extraction_eq] at rup
  exact LRATRUP.production_target_valid fuel words lits_at n hints_at hints_n starts lengths alive store assign trail
    variables max_id starts lengths alive store rupAssign rupTrail rup

end Oak.LRATChecker
