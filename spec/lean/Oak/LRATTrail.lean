import Oak.LRATStore

/-!
Trail coverage for successive production RUP calls. The trail contains each
assigned declared var once, so a fresh assignment has space in a trail
of `variables` entries and its counter cannot wrap. Rollback then restores
the zero scratch required by the next addition's soundness theorem.
-/

set_option autoImplicit false

namespace Oak.LRATRUP

structure TrailState (assign : Array UInt8) (trail : Array UInt32)
    (variables used : UInt32) : Prop where
  distinct : (trailIndices trail 0 used.toNat).Nodup
  domain : ∀ v ∈ trailIndices trail 0 used.toNat, v < variables.toNat
  nonzero : ∀ v ∈ trailIndices trail 0 used.toNat, assign.getD v 0 ≠ 0
  covers : ∀ v, v < variables.toNat → assign.getD v 0 ≠ 0 →
    v ∈ trailIndices trail 0 used.toNat

theorem trail_initial (assign : Array UInt8) (trail : Array UInt32) (variables : UInt32)
    (zero : ∀ v, v < variables.toNat → assign.getD v 0 = 0) :
    TrailState assign trail variables 0 := by
  constructor
  · simp [trailIndices]
  · simp [trailIndices]
  · simp [trailIndices]
  · intro v hv nonzero
    exact False.elim (nonzero (zero v hv))

theorem trail_fresh_room (assign : Array UInt8) (trail : Array UInt32)
    (variables used var : UInt32) (state : TrailState assign trail variables used)
    (inside : var < variables) (fresh : assign.getD var.toNat 0 = 0) :
    used < variables := by
  have absent : var.toNat ∉ trailIndices trail 0 used.toNat := by
    intro member
    exact state.nonzero _ member fresh
  have distinct := List.nodup_cons.mpr ⟨absent, state.distinct⟩
  have subset : var.toNat :: trailIndices trail 0 used.toNat ⊆ List.range variables.toNat := by
    intro v member
    rcases List.mem_cons.mp member with same | old
    · subst v
      exact List.mem_range.mpr (UInt32.lt_iff_toNat_lt.mp inside)
    · exact List.mem_range.mpr (state.domain v old)
  have bound := distinct.length_le_of_subset subset
  simp only [List.length_cons, trailIndices, List.length_map, List.length_range', List.length_range] at bound
  rw [UInt32.lt_iff_toNat_lt]
  omega

theorem trail_push_indices (trail : Array UInt32) (used var : UInt32)
    (room : used.toNat < trail.size) (noWrap : (used + 1).toNat = used.toNat + 1) :
    trailIndices (trail.setIfInBounds used.toNat var) 0 (used + 1).toNat =
      trailIndices trail 0 used.toNat ++ [var.toNat] := by
  unfold trailIndices
  rw [noWrap, List.range'_1_concat, List.map_append]
  have prefix : (List.range' 0 used.toNat).map
      (fun k => ((trail.setIfInBounds used.toNat var).getD k 0).toNat) =
      (List.range' 0 used.toNat).map (fun k => (trail.getD k 0).toNat) := by
    apply List.map_congr_left
    intro k member
    have bound : k < used.toNat := by simpa using member
    rw [LRATChecker.array_getD_set_ne trail used.toNat k var 0 (by omega)]
  rw [prefix]
  simp only [Nat.zero_add, List.map_cons, List.map_nil,
    LRATChecker.array_getD_set_self trail used.toNat var 0 room]

theorem trail_push (assign : Array UInt8) (trail : Array UInt32)
    (variables used var : UInt32) (value : UInt8)
    (state : TrailState assign trail variables used)
    (assignCapacity : variables.toNat ≤ assign.size) (trailCapacity : variables.toNat ≤ trail.size)
    (inside : var < variables) (fresh : assign.getD var.toNat 0 = 0)
    (valueNonzero : value ≠ 0) :
    TrailState (assign.setIfInBounds var.toNat value)
      (trail.setIfInBounds used.toNat var) variables (used + 1) := by
  have room := trail_fresh_room assign trail variables used var state inside fresh
  have successor := counter_succ used variables room
  have rn := UInt32.lt_iff_toNat_lt.mp room
  have vn := UInt32.lt_iff_toNat_lt.mp inside
  have entries := trail_push_indices trail used var (by omega) successor
  have absent : var.toNat ∉ trailIndices trail 0 used.toNat := by
    intro member
    exact state.nonzero _ member fresh
  constructor
  · rw [entries, List.nodup_append]
    refine ⟨state.distinct, by simp, ?_⟩
    intro a member b singleton
    have same : b = var.toNat := List.mem_singleton.mp singleton
    subst b
    intro equal
    exact absent (equal ▸ member)
  · rw [entries]
    intro v member
    rcases List.mem_append.mp member with old | new
    · exact state.domain v old
    · simpa only [List.mem_singleton.mp new] using vn
  · rw [entries]
    intro v member
    have bound : v < assign.size := by
      rcases List.mem_append.mp member with old | new
      · have := state.domain v old; omega
      · have := List.mem_singleton.mp new; omega
    rw [set_getD assign var.toNat v value bound]
    by_cases same : var.toNat = v
    · simpa only [if_pos same] using valueNonzero
    · rw [if_neg same]
      rcases List.mem_append.mp member with old | new
      · exact state.nonzero v old
      · exact False.elim (same (List.mem_singleton.mp new).symm)
  · intro v insideV nonzero
    rw [entries]
    by_cases same : var.toNat = v
    · exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr same.symm))
    · rw [set_getD assign var.toNat v value (by omega), if_neg same] at nonzero
      exact List.mem_append.mpr (Or.inl (state.covers v insideV nonzero))

theorem undo_loop_fuel (fuel : Nat) (assign : Array UInt8) (trail : Array UInt32)
    (used i : UInt32) (result : Array UInt8) (finish : UInt32)
    (bound : i ≤ used)
    (run : lrat_undo.loop1 assign trail used i fuel = some (result, finish)) :
    used.toNat - i.toNat < fuel := by
  induction fuel generalizing assign i result finish with
  | zero => simp [lrat_undo.loop1] at run
  | succ fuel ih =>
    by_cases step : i < used
    · simp only [lrat_undo.loop1, step, decide_true, ite_true] at run
      have successor := counter_succ i used step
      have sn := UInt32.lt_iff_toNat_lt.mp step
      have next := ih _ (i + 1) result finish
        (by rw [UInt32.le_iff_toNat_le, successor]; omega) run
      omega
    · rw [UInt32.lt_iff_toNat_lt] at step
      omega

theorem undo_tracked_zero (fuel : Nat) (assign : Array UInt8) (trail : Array UInt32)
    (variables used : UInt32) (result : Array UInt8) (trail' : Array UInt32)
    (state : TrailState assign trail variables used) (capacity : variables.toNat ≤ assign.size)
    (run : lrat_undo assign trail used fuel = some ((), result, trail')) :
    result.size = assign.size ∧ trail' = trail ∧
      ∀ v, v < variables.toNat → result.getD v 0 = 0 := by
  unfold lrat_undo at run
  cases scanned : lrat_undo.loop1 assign trail used 0 fuel with
  | none => simp [scanned] at run
  | some pair =>
    rcases pair with ⟨cleared, finish⟩
    have enough := undo_loop_fuel fuel assign trail used 0 cleared finish (by simp) scanned
    obtain ⟨expected, execution, size, values⟩ := undo_spec assign trail used fuel (by simpa using enough)
    have fullRun : lrat_undo assign trail used fuel = some ((), result, trail') := run
    rw [execution] at fullRun
    cases fullRun
    refine ⟨size, rfl, ?_⟩
    intro v inside
    rw [values v (by omega)]
    by_cases zero : assign.getD v 0 = 0
    · simp [zero]
    · rw [if_pos (state.covers v inside zero)]

theorem trueValue_ne_zero (lit : UInt32) : trueValue lit ≠ 0 := by
  unfold trueValue
  split <;> decide

theorem target_tracks (fuel : Nat) (words : Array UInt32)
    (target_at target_n variables : UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (status : UInt32) (settled : Bool) (used i : UInt32)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (status' : UInt32) (settled' : Bool) (used' i' : UInt32)
    (assignCapacity : variables.toNat ≤ assign.size) (trailCapacity : variables.toNat ≤ trail.size)
    (state : TrailState assign trail variables used)
    (run : lrat_rup.loop1 words target_at target_n assign trail variables status settled used i fuel =
      some (assign', trail', status', settled', used', i')) :
    assign'.size = assign.size ∧ trail'.size = trail.size ∧ TrailState assign' trail' variables used' := by
  induction fuel generalizing assign trail status settled used i assign' trail' status' settled' used' i' with
  | zero => simp [lrat_rup.loop1] at run
  | succ fuel ih =>
    have next (a : Array UInt8) (t : Array UInt32) (s : UInt32) (q : Bool) (u : UInt32)
        (asize : a.size = assign.size) (tsize : t.size = trail.size)
        (inv : TrailState a t variables u)
        (recur : lrat_rup.loop1 words target_at target_n a t variables s q u (i + 1) fuel =
          some (assign', trail', status', settled', used', i')) :
        assign'.size = assign.size ∧ trail'.size = trail.size ∧ TrailState assign' trail' variables used' := by
      obtain ⟨sa, st, inv'⟩ := ih a t s q u (i + 1) _ _ _ _ _ _
        (by omega) (by omega) inv recur
      exact ⟨sa.trans asize, st.trans tsize, inv'⟩
    by_cases enter : i < target_n ∧ status = LRAT_ACCEPTED
    · obtain ⟨hi, hs⟩ := enter
      subst status
      generalize wordAt : words.getD (target_at + i).toNat 0 = lit at *
      by_cases invalid : lit / 2 ≥ variables
      · simp only [lrat_rup.loop1, hi, decide_true, beq_self_eq_true, Bool.and_self,
          ite_true, wordAt, invalid, LRAT_MALFORMED, LRAT_ACCEPTED, BEq.beq,
          bind, Option.bind, Option.pure_def] at run
        exact next assign trail 1 settled used rfl rfl state run
      · have inside : lit / 2 < variables := by
          rw [ge_iff_le, UInt32.le_iff_toNat_le] at invalid
          rw [UInt32.lt_iff_toNat_lt]; omega
        cases settled with
        | true =>
          simp only [lrat_rup.loop1, hi, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, wordAt, invalid, decide_false, Bool.false_eq_true, ite_false,
            Bool.not_true, Bool.and_false, bind, Option.bind, Option.pure_def] at run
          exact next assign trail LRAT_ACCEPTED true used rfl rfl state (by simpa only [last] using run)
        | false =>
          simp only [lrat_rup.loop1, hi, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, wordAt, invalid, decide_false, Bool.false_eq_true, ite_false,
            Bool.not_false, Bool.and_true, false_value_spec, bind, Option.bind, Option.pure_def] at run
          by_cases fresh : assign.getD (lit / 2).toNat 0 = LRAT_UNASSIGNED
          · simp only [beq_iff_eq, fresh, ite_true] at run
            exact next _ _ LRAT_ACCEPTED false (used + 1) Array.size_setIfInBounds Array.size_setIfInBounds
              (trail_push assign trail variables used (lit / 2) (falseValue lit) state
                assignCapacity trailCapacity inside fresh (falseValue_ne_zero lit)) run
          · simp only [beq_iff_eq, fresh, ite_false] at run
            exact next assign trail LRAT_ACCEPTED _ used rfl rfl state run
    · have guard : (decide (i < target_n) && (status == LRAT_ACCEPTED)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        by_cases hi : i < target_n
        · exact Or.inr (fun hs => enter ⟨hi, hs⟩)
        · exact Or.inl hi
      simp only [lrat_rup.loop1, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, state⟩

/-- Any selected unit is an unassigned declared var. This is proved
from the actual scan, including duplicate literals and refused scans. -/
theorem scan_fresh (fuel : Nat) (store : Array UInt32) (assign : Array UInt8)
    (start count variables status remaining unit j status' remaining' unit' j' : UInt32)
    (valid : ∀ k : UInt32, k < count → store.getD (start + k).toNat 0 / 2 < variables)
    (initial : remaining = 0 ∨ (assign.getD (unit / 2).toNat 0 = 0 ∧ unit / 2 < variables))
    (run : lrat_rup.loop3 store assign status start count remaining unit j fuel =
      some (status', remaining', unit', j')) :
    remaining' = 0 ∨ (assign.getD (unit' / 2).toNat 0 = 0 ∧ unit' / 2 < variables) := by
  induction fuel generalizing status remaining unit j status' remaining' unit' j' with
  | zero => simp [lrat_rup.loop3] at run
  | succ fuel ih =>
    by_cases enter : j < count ∧ status = LRAT_ACCEPTED
    · obtain ⟨hj, hs⟩ := enter
      subst status
      generalize wordAt : store.getD (start + j).toNat 0 = lit at *
      have inside : lit / 2 < variables := by simpa only [wordAt] using valid j hj
      simp only [lrat_rup.loop3, hj, decide_true, beq_self_eq_true, Bool.and_self,
        ite_true, wordAt, true_value_spec, bind, Option.bind, Option.pure_def] at run
      by_cases satisfied : assign.getD (lit / 2).toNat 0 = trueValue lit
      · simp only [beq_iff_eq, satisfied, ite_true] at run
        exact ih LRAT_SATISFIED remaining unit (j + 1) _ _ _ _ initial run
      · simp only [beq_eq_false_iff_ne.mpr satisfied, Bool.false_eq_true, ite_false] at run
        by_cases fresh : assign.getD (lit / 2).toNat 0 = LRAT_UNASSIGNED ∧ (remaining = 0 ∨ unit ≠ lit)
        · have guard : ((assign.getD (lit / 2).toNat 0 == LRAT_UNASSIGNED) &&
              ((remaining == 0) || (unit != lit))) = true := by simpa using fresh
          simp only [guard, ite_true] at run
          exact ih LRAT_ACCEPTED (remaining + 1) lit (j + 1) _ _ _ _ (Or.inr ⟨fresh.1, inside⟩) run
        · have guard : ((assign.getD (lit / 2).toNat 0 == LRAT_UNASSIGNED) &&
              ((remaining == 0) || (unit != lit))) = false := by simpa using fresh
          simp only [guard, Bool.false_eq_true, ite_false] at run
          exact ih LRAT_ACCEPTED remaining unit (j + 1) _ _ _ _ initial run
    · have guard : (decide (j < count) && (status == LRAT_ACCEPTED)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        by_cases hj : j < count
        · exact Or.inr (fun hs => enter ⟨hj, hs⟩)
        · exact Or.inl hj
      simp only [lrat_rup.loop3, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl⟩
      exact initial

theorem hints_track (fuel : Nat) (words : Array UInt32)
    (hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (variables max_id : UInt32)
    (valid : LiveVariables starts lengths alive store variables max_id)
    (assign : Array UInt8) (trail : Array UInt32)
    (status : UInt32) (settled : Bool) (used h : UInt32)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (status' : UInt32) (settled' : Bool) (used' h' : UInt32)
    (assignCapacity : variables.toNat ≤ assign.size) (trailCapacity : variables.toNat ≤ trail.size)
    (state : TrailState assign trail variables used)
    (run : lrat_rup.loop2 words hints_at hints_n starts lengths alive store assign trail max_id
      status settled used h fuel = some (assign', trail', status', settled', used', h')) :
    assign'.size = assign.size ∧ trail'.size = trail.size ∧ TrailState assign' trail' variables used' := by
  induction fuel generalizing assign trail status settled used h assign' trail' status' settled' used' h' with
  | zero => simp [lrat_rup.loop2] at run
  | succ fuel ih =>
    have next (a : Array UInt8) (t : Array UInt32) (s : UInt32) (q : Bool) (u : UInt32)
        (asize : a.size = assign.size) (tsize : t.size = trail.size)
        (inv : TrailState a t variables u)
        (recur : lrat_rup.loop2 words hints_at hints_n starts lengths alive store a t max_id s q u (h + 1) fuel =
          some (assign', trail', status', settled', used', h')) :
        assign'.size = assign.size ∧ trail'.size = trail.size ∧ TrailState assign' trail' variables used' := by
      obtain ⟨sa, st, inv'⟩ := ih a t s q u (h + 1) _ _ _ _ _ _
        (by omega) (by omega) inv recur
      exact ⟨sa.trans asize, st.trans tsize, inv'⟩
    by_cases enter : h < hints_n ∧ status = LRAT_ACCEPTED ∧ settled = false
    · obtain ⟨hh, hs, hq⟩ := enter
      subst status settled
      generalize hid : words.getD (hints_at + h).toNat 0 = id at *
      by_cases live : id ≤ max_id ∧ 0 < id ∧ alive.getD id.toNat 0 ≠ 0
      · have hlive : ((decide (id ≤ max_id) && decide (id > 0)) &&
            (alive.getD id.toNat 0 != 0)) = true := by simpa [and_assoc] using live
        simp only [lrat_rup.loop2, hh, decide_true, beq_self_eq_true, Bool.not_false,
          Bool.and_self, ite_true, hid, hlive] at run
        cases scanRun : lrat_rup.loop3 store assign LRAT_ACCEPTED (starts.getD id.toNat 0)
            (lengths.getD id.toNat 0) 0 0 0 fuel with
        | none => simp only [scanRun, bind, Option.bind, Option.pure_def] at run; contradiction
        | some result =>
          rcases result with ⟨scanned, remaining, unit, j⟩
          simp only [scanRun, bind, Option.bind, Option.pure_def] at run
          by_cases accepted : scanned = LRAT_ACCEPTED
          · simp only [accepted, beq_self_eq_true, ite_true] at run
            by_cases empty : remaining = 0
            · simp only [empty, beq_self_eq_true, ite_true] at run
              by_cases last : h + 1 = hints_n
              · simp only [last, beq_self_eq_true, ite_true] at run
                exact next assign trail LRAT_ACCEPTED true used rfl rfl state (by simpa only [last] using run)
              · simp only [beq_eq_false_iff_ne.mpr last, Bool.false_eq_true, ite_false] at run
                exact next assign trail LRAT_MALFORMED false used rfl rfl state run
            · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at run
              by_cases one : remaining = 1
              · have fresh := scan_fresh fuel store assign (starts.getD id.toNat 0) (lengths.getD id.toNat 0)
                  variables LRAT_ACCEPTED 0 0 0 scanned remaining unit j
                  (fun k hk => UInt32.lt_iff_toNat_lt.mpr (valid id live.1 live.2.1 live.2.2 k hk))
                  (Or.inl rfl) scanRun
                obtain ⟨zero, inside⟩ := fresh.resolve_left empty
                simp only [one, beq_self_eq_true, ite_true, true_value_spec] at run
                exact next _ _ LRAT_ACCEPTED false (used + 1) Array.size_setIfInBounds Array.size_setIfInBounds
                  (trail_push assign trail variables used (unit / 2) (trueValue unit) state
                    assignCapacity trailCapacity inside zero (trueValue_ne_zero unit)) run
              · simp only [beq_eq_false_iff_ne.mpr one, Bool.false_eq_true, ite_false] at run
                exact next assign trail LRAT_NOT_UNIT false used rfl rfl state run
          · simp only [beq_eq_false_iff_ne.mpr accepted, Bool.false_eq_true, ite_false] at run
            exact next assign trail scanned false used rfl rfl state run
      · have hlive : ((decide (id ≤ max_id) && decide (id > 0)) &&
            (alive.getD id.toNat 0 != 0)) = false := by simpa [and_assoc] using live
        simp only [lrat_rup.loop2, hh, decide_true, beq_self_eq_true, Bool.not_false,
          Bool.and_self, ite_true, hid, hlive, Bool.false_eq_true, ite_false,
          bind, Option.bind, Option.pure_def] at run
        exact next assign trail LRAT_NOT_LIVE false used rfl rfl state run
    · have guard : ((decide (h < hints_n) && (status == LRAT_ACCEPTED)) && !settled) = false := by
        cases settled <;> simp_all
      simp only [lrat_rup.loop2, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, state⟩

/-- Every completed production RUP call restores zero declared-var
scratch, including refused calls. Trail coverage is derived from execution,
not supplied by the caller. The caller supplies only capacities, initial
zero scratch, and the database's declared-var invariant. -/
theorem production_rup_restores_zero (fuel : Nat) (words : Array UInt32)
    (target_at target_n hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id : UInt32) (status : UInt32)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (assignCapacity : variables.toNat ≤ assign.size) (trailCapacity : variables.toNat ≤ trail.size)
    (zero : ∀ v, v < variables.toNat → assign.getD v 0 = 0)
    (valid : LiveVariables starts lengths alive store variables max_id)
    (run : lrat_rup words target_at target_n hints_at hints_n starts lengths alive store assign trail variables max_id fuel =
      some (status, starts', lengths', alive', store', assign', trail')) :
    assign'.size = assign.size ∧ trail'.size = trail.size ∧
      ∀ v, v < variables.toNat → assign'.getD v 0 = 0 := by
  unfold lrat_rup at run
  cases targetRun : lrat_rup.loop1 words target_at target_n assign trail variables LRAT_ACCEPTED false 0 0 fuel with
  | none => simp [targetRun] at run
  | some state =>
    rcases state with ⟨a1, t1, s1, q1, u1, i1⟩
    simp only [targetRun, bind, Option.bind, Option.pure_def] at run
    obtain ⟨as1, ts1, inv1⟩ := target_tracks fuel words target_at target_n variables assign trail
      LRAT_ACCEPTED false 0 0 a1 t1 s1 q1 u1 i1 assignCapacity trailCapacity
      (trail_initial assign trail variables zero) targetRun
    cases hintsRun : lrat_rup.loop2 words hints_at hints_n starts lengths alive store a1 t1 max_id s1 q1 u1 0 fuel with
    | none => simp [hintsRun] at run
    | some state =>
      rcases state with ⟨a2, t2, s2, q2, u2, h2⟩
      simp only [hintsRun, bind, Option.bind, Option.pure_def] at run
      obtain ⟨as2, ts2, inv2⟩ := hints_track fuel words hints_at hints_n starts lengths alive store
        variables max_id valid a1 t1 s1 q1 u1 0 a2 t2 s2 q2 u2 h2
        (by omega) (by omega) inv1 hintsRun
      cases undoRun : lrat_undo a2 t2 u2 fuel with
      | none => split at run <;> simp [undoRun] at run
      | some state =>
        rcases state with ⟨unused, a3, t3⟩
        cases unused
        obtain ⟨as3, ts3, zeros⟩ := undo_tracked_zero fuel a2 t2 variables u2 a3 t3 inv2 (by omega) undoRun
        split at run <;>
          (try simp only [undoRun, bind, Option.bind, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run) <;>
          rcases run with ⟨_, _, _, _, _, rfl, rfl⟩ <;>
          exact ⟨as3.trans (as2.trans as1), by rw [ts3, ts2, ts1], zeros⟩

end Oak.LRATRUP

namespace Oak.LRATChecker

/-- One accepted production addition preserves the live store and restores
all scratch preconditions for the next addition. No trail-coverage premise
is supplied: it is derived from the observed RUP execution. -/
theorem production_addition_state (fuel : Nat) (words store : Array UInt32)
    (starts lengths : Array UInt32) (alive : Array UInt8) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id id used n lits_at hints_at hints_n : UInt32)
    (rupStarts rupLengths : Array UInt32) (rupAlive : Array UInt8) (rupStore : Array UInt32)
    (rupAssign : Array UInt8) (rupTrail : Array UInt32) (store' : Array UInt32) (j' : UInt32)
    (assignCapacity : variables.toNat ≤ assign.size) (trailCapacity : variables.toNat ≤ trail.size)
    (zero : ∀ v, v < variables.toNat → assign.getD v 0 = 0)
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
      (rupAlive.setIfInBounds id.toNat 1) store' variables max_id ∧ store'.size = store.size ∧
    rupAssign.size = assign.size ∧ rupTrail.size = trail.size ∧
    (∀ v, v < variables.toNat → rupAssign.getD v 0 = 0) := by
  obtain ⟨storedNext, validNext, storeSize⟩ := production_addition_invariants fuel words store starts lengths alive
    assign trail variables max_id id used n lits_at hints_at hints_n rupStarts rupLengths rupAlive rupStore
    rupAssign rupTrail store' j' stored valid startCap lengthCap dest dest32 source source32 rup copy
  have restoreRun := rup
  rw [rup_extraction_eq] at restoreRun
  obtain ⟨assignSize, trailSize, zeroNext⟩ := LRATRUP.production_rup_restores_zero fuel words lits_at n hints_at hints_n
    starts lengths alive store assign trail variables max_id LRAT_ACCEPTED rupStarts rupLengths rupAlive rupStore
    rupAssign rupTrail assignCapacity trailCapacity zero valid restoreRun
  exact ⟨storedNext, validNext, storeSize, assignSize, trailSize, zeroNext⟩

end Oak.LRATChecker
