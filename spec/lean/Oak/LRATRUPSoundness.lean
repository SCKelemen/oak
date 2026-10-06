import Oak.LRATRUP
import Oak.RupCheck

/-!
Soundness of the extracted production RUP implementation, pinned to
`prove/solver/lrat.oak` by `TestLRATKernelRUPExtract`. Target negation, the
duplicate-aware clause scan, and the hint loop preserve agreement with any
model of the live database that falsifies the target. Consequently acceptance
entails the decoded target; accepting an empty target refutes that database.
The calling parser must establish zero scratch and the live-variable invariant.
This module does not yet prove those invariants over a whole record, memory
safety of the whole parser, or the correctness of extraction or native code.
-/
namespace Oak.LRATRUP

def trueValue (lit : UInt32) : UInt8 := if lit % 2 == 1 then 2 else 1
def falseValue (lit : UInt32) : UInt8 := if lit % 2 == 1 then 1 else 2

theorem falseValue_ne_zero (lit : UInt32) : falseValue lit ≠ 0 := by
  unfold falseValue
  split <;> decide

theorem true_value_spec (lit : UInt32) (fuel : Nat) :
    lrat_true_value lit fuel = some (trueValue lit) := rfl

theorem false_value_spec (lit : UInt32) (fuel : Nat) :
    lrat_false_value lit fuel = some (falseValue lit) := rfl

/-- Scratch either leaves a variable unassigned or agrees with the model. -/
def Agrees (assign : Array UInt8) (model : Nat → UInt8) : Prop :=
  ∀ v, v < assign.size → assign.getD v 0 = 0 ∨ assign.getD v 0 = model v

theorem agrees_write {assign : Array UInt8} {model : Nat → UInt8}
    (h : Agrees assign model) (v : Nat) :
    Agrees (assign.setIfInBounds v (model v)) model := by
  intro k hk
  have hk' : k < assign.size := by simpa using hk
  rw [set_getD assign v k (model v) hk']
  by_cases he : v = k
  · subst v
    simp
  · simp only [he, ite_false]
    exact h k hk'

/-- Assuming a target false never creates a clash in scratch that agrees with
that model. This is about the actual machine loop and its return status. -/
theorem target_preserves_model (fuel : Nat) (words : Array UInt32)
    (target_at target_n variables : UInt32) (model : Nat → UInt8)
    (falseTarget : ∀ j : UInt32, j < target_n →
      model ((words.getD (target_at + j).toNat 0) / 2).toNat =
        falseValue (words.getD (target_at + j).toNat 0))
    (assign : Array UInt8) (trail : Array UInt32)
    (status : UInt32) (settled : Bool) (used i : UInt32)
    (capacity : variables.toNat ≤ assign.size)
    (initial : status = LRAT_ACCEPTED → settled = false ∧ Agrees assign model)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (status' : UInt32) (settled' : Bool) (used' i' : UInt32)
    (run : lrat_rup.loop1 words target_at target_n assign trail variables
      status settled used i fuel = some (assign', trail', status', settled', used', i')) :
    assign'.size = assign.size ∧
      (status' = LRAT_ACCEPTED → settled' = false ∧ Agrees assign' model) := by
  induction fuel generalizing assign trail status settled used i assign' trail' status' settled' used' i' with
  | zero => simp [lrat_rup.loop1] at run
  | succ fuel ih =>
    by_cases enter : i < target_n ∧ status = LRAT_ACCEPTED
    · obtain ⟨hi, hs⟩ := enter
      obtain ⟨hq, hm⟩ := initial hs
      subst status
      subst settled
      generalize hlit : words.getD (target_at + i).toNat 0 = lit at *
      generalize hvdef : (lit / 2).toNat = v at *
      have hf : model v = falseValue lit := by
        have ht := falseTarget i hi
        rw [hlit, hvdef] at ht
        exact ht
      by_cases invalid : lit / 2 ≥ variables
      · simp only [lrat_rup.loop1, hi, decide_true, Bool.and_self,
          ite_true, hlit, invalid, Bool.not_false, LRAT_ACCEPTED, LRAT_MALFORMED,
          BEq.beq, Option.pure_def] at run
        exact ih assign trail 1 false used (i + 1) capacity (by intro h; contradiction)
          assign' trail' status' settled' used' i' run
      · have hv : v < assign.size := by
          have hvar : (lit / 2).toNat < variables.toNat := by
            rw [ge_iff_le, UInt32.le_iff_toNat_le] at invalid
            omega
          omega
        by_cases fresh : assign.getD v 0 = 0
        · have hmodel : Agrees (assign.setIfInBounds v (falseValue lit)) model := by
            rw [← hf]
            exact agrees_write hm v
          simp only [lrat_rup.loop1, hi, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, hlit, invalid, decide_false, Bool.not_false,
            Bool.and_true, false_value_spec, Option.pure_def,
            LRAT_UNASSIGNED, hvdef, fresh] at run
          obtain ⟨sz, inv⟩ := ih _ _ _ _ _ _ (by simpa using capacity)
            (by intro _; exact ⟨rfl, hmodel⟩) _ _ _ _ _ _ run
          exact ⟨sz.trans Array.size_setIfInBounds, inv⟩
        · have prior : assign.getD v 0 = falseValue lit := (hm v hv).resolve_left fresh |>.trans hf
          simp only [lrat_rup.loop1, hi, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, hlit, invalid, decide_false, ite_false, Bool.not_false,
            Bool.and_true, false_value_spec, Option.pure_def,
            LRAT_UNASSIGNED, hvdef, prior, bne_self_eq_false,
            Bool.false_eq_true, beq_iff_eq,
            bind, Option.bind, falseValue_ne_zero] at run
          exact ih assign trail LRAT_ACCEPTED false used (i + 1) capacity
            (by intro _; exact ⟨rfl, hm⟩) _ _ _ _ _ _ run
    · have guard : (decide (i < target_n) && (status == LRAT_ACCEPTED)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        by_cases hi : i < target_n
        · exact Or.inr (fun hs => enter ⟨hi, hs⟩)
        · exact Or.inl hi
      simp only [lrat_rup.loop1, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, initial⟩

/-- Once the scan has passed a model's satisfying literal, either it has at
least two candidates or its sole candidate is that literal. -/
def SeenWitness (k : UInt32) (lit : UInt32) (remaining unit j : UInt32) : Prop :=
  k.toNat < j.toNat → 0 < remaining.toNat ∧ (remaining = 1 → unit = lit)

theorem seen_increment (k lit remaining unit j count current : UInt32)
    (hj : j < count) (hr : remaining.toNat ≤ j.toNat)
    (seen : SeenWitness k lit remaining unit j)
    (currentAt : k = j → current = lit) :
    SeenWitness k lit (remaining + 1) current (j + 1) := by
  have hjs := counter_succ j count hj
  have hjn := UInt32.lt_iff_toNat_lt.mp hj
  have hrs := counter_succ remaining count (by rw [UInt32.lt_iff_toNat_lt]; omega)
  intro passed
  refine ⟨by rw [hrs]; omega, ?_⟩
  intro single
  have one : (remaining + 1).toNat = 1 := by rw [single]; rfl
  rw [hrs] at one
  have notPassed : ¬ k.toNat < j.toNat := by
    intro h
    have := (seen h).1
    omega
  apply currentAt
  apply UInt32.toNat_inj.mp
  omega

theorem seen_unchanged (k lit remaining unit j count : UInt32)
    (hj : j < count) (seen : SeenWitness k lit remaining unit j)
    (current : k = j → 0 < remaining.toNat ∧ unit = lit) :
    SeenWitness k lit remaining unit (j + 1) := by
  intro passed
  have hjs := counter_succ j count hj
  by_cases before : k.toNat < j.toNat
  · exact seen before
  · have same : k = j := UInt32.toNat_inj.mp (by omega)
    obtain ⟨positive, equal⟩ := current same
    exact ⟨positive, fun _ => equal⟩

/-- A clause satisfied by the model cannot be scanned as a conflict. If the
production scan returns one candidate, that candidate holds in the model.
The `remaining ≤ j` invariant prevents its machine counter from wrapping. -/
theorem scan_model_witness (fuel : Nat) (store : Array UInt32) (assign : Array UInt8)
    (model : Nat → UInt8) (agree : Agrees assign model)
    (start count k : UInt32) (hk : k < count)
    (witnessBound : (store.getD (start + k).toNat 0 / 2).toNat < assign.size)
    (witnessTrue : model (store.getD (start + k).toNat 0 / 2).toNat =
      trueValue (store.getD (start + k).toNat 0))
    (status remaining unit j status' remaining' unit' j' : UInt32)
    (initial : status = LRAT_ACCEPTED →
      remaining.toNat ≤ j.toNat ∧ j ≤ count ∧
      SeenWitness k (store.getD (start + k).toNat 0) remaining unit j)
    (run : lrat_rup.loop3 store assign status start count remaining unit j fuel =
      some (status', remaining', unit', j')) :
    status' = LRAT_ACCEPTED → j' = count ∧ 0 < remaining'.toNat ∧
      (remaining' = 1 → unit' = store.getD (start + k).toNat 0) := by
  induction fuel generalizing status remaining unit j status' remaining' unit' j' with
  | zero => simp [lrat_rup.loop3] at run
  | succ fuel ih =>
    by_cases enter : j < count ∧ status = LRAT_ACCEPTED
    · obtain ⟨hj, hs⟩ := enter
      obtain ⟨hr, hjc, seen⟩ := initial hs
      subst status
      generalize hlit : store.getD (start + j).toNat 0 = lit at *
      generalize ha : assign.getD (lit / 2).toNat 0 = value at *
      have nextBound : j + 1 ≤ count := by
        rw [UInt32.le_iff_toNat_le, counter_succ j count hj]
        have := UInt32.lt_iff_toNat_lt.mp hj
        omega
      by_cases satisfied : value = trueValue lit
      · simp only [lrat_rup.loop3, hj, decide_true, beq_self_eq_true, Bool.and_self,
          ite_true, hlit, ha, true_value_spec, bind, Option.bind, Option.pure_def,
          satisfied] at run
        exact ih LRAT_SATISFIED remaining unit (j + 1) _ _ _ _
          (by intro h; contradiction) run
      · by_cases fresh : value = 0 ∧ (remaining = 0 ∨ unit ≠ lit)
        · have hinc : ((value == LRAT_UNASSIGNED) && ((remaining == 0) || (unit != lit))) = true := by
            simpa [LRAT_UNASSIGNED] using fresh
          simp only [lrat_rup.loop3, hj, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, hlit, ha, true_value_spec, bind, Option.bind, Option.pure_def,
            beq_eq_false_iff_ne.mpr satisfied, Bool.false_eq_true, ite_false, hinc] at run
          apply ih (status := LRAT_ACCEPTED) (remaining := remaining + 1) (unit := lit) (j := j + 1)
            (status' := status') (remaining' := remaining') (unit' := unit') (j' := j') ?_ run
          intro _
          have hjs := counter_succ j count hj
          have hrs := counter_succ remaining count (by
            rw [UInt32.lt_iff_toNat_lt]
            have := UInt32.lt_iff_toNat_lt.mp hj
            omega)
          refine ⟨by rw [hrs, hjs]; omega, nextBound, ?_⟩
          apply seen_increment k _ remaining unit j count lit hj hr seen
          intro eq
          subst k
          exact hlit.symm
        · have hno : ((value == LRAT_UNASSIGNED) && ((remaining == 0) || (unit != lit))) = false := by
            simpa [LRAT_UNASSIGNED] using fresh
          simp only [lrat_rup.loop3, hj, decide_true, beq_self_eq_true, Bool.and_self,
            ite_true, hlit, ha, true_value_spec, bind, Option.bind, Option.pure_def,
            beq_eq_false_iff_ne.mpr satisfied, Bool.false_eq_true, ite_false, hno] at run
          apply ih (status := LRAT_ACCEPTED) (remaining := remaining) (unit := unit) (j := j + 1)
            (status' := status') (remaining' := remaining') (unit' := unit') (j' := j') ?_ run
          intro _
          refine ⟨by rw [counter_succ j count hj]; omega, nextBound, ?_⟩
          apply seen_unchanged k _ remaining unit j count hj seen
          intro eq
          subst k
          rw [hlit] at witnessBound witnessTrue ⊢
          have actual := agree (lit / 2).toNat witnessBound
          rw [ha] at actual
          have zero : value = 0 := actual.resolve_right (fun he => satisfied (he.trans witnessTrue))
          have nonzero : remaining ≠ 0 := fun hz => fresh ⟨zero, Or.inl hz⟩
          have equal : unit = lit := by
            by_cases he : unit = lit
            · exact he
            · exact False.elim (fresh ⟨zero, Or.inr he⟩)
          refine ⟨?_, equal⟩
          have hn : remaining.toNat ≠ 0 := fun hn => nonzero (UInt32.toNat_inj.mp hn)
          omega
    · have guard : (decide (j < count) && (status == LRAT_ACCEPTED)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        by_cases hj : j < count
        · exact Or.inr (fun hs => enter ⟨hj, hs⟩)
        · exact Or.inl hj
      simp only [lrat_rup.loop3, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl⟩
      intro accepted
      obtain ⟨hr, hj, seen⟩ := initial accepted
      have done : j = count := by
        apply UInt32.toNat_inj.mp
        have hn : ¬ j < count := fun h => enter ⟨h, accepted⟩
        rw [UInt32.lt_iff_toNat_lt] at hn
        rw [UInt32.le_iff_toNat_le] at hj
        omega
      exact ⟨done, seen (by rw [done]; exact UInt32.lt_iff_toNat_lt.mp hk)⟩

/-- A model satisfies every live clause, with a declared-variable witness in
the exact word range the production scan reads. Parser refinement supplies
the range and variable invariants separately. -/
def WordModels (model : Nat → UInt8) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (variables max_id : UInt32) : Prop :=
  ∀ id : UInt32, id ≤ max_id → 0 < id → alive.getD id.toNat 0 ≠ 0 →
    ∃ k : UInt32, k < lengths.getD id.toNat 0 ∧
      (store.getD (starts.getD id.toNat 0 + k).toNat 0 / 2).toNat < variables.toNat ∧
      model (store.getD (starts.getD id.toNat 0 + k).toNat 0 / 2).toNat =
        trueValue (store.getD (starts.getD id.toNat 0 + k).toNat 0)

theorem hints_preserve_model (fuel : Nat) (words : Array UInt32)
    (hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (variables max_id : UInt32)
    (model : Nat → UInt8) (models : WordModels model starts lengths alive store variables max_id)
    (assign : Array UInt8) (trail : Array UInt32)
    (status : UInt32) (settled : Bool) (used h : UInt32)
    (capacity : variables.toNat ≤ assign.size)
    (initial : status = LRAT_ACCEPTED → settled = false ∧ Agrees assign model)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (status' : UInt32) (settled' : Bool) (used' h' : UInt32)
    (run : lrat_rup.loop2 words hints_at hints_n starts lengths alive store assign trail max_id
      status settled used h fuel = some (assign', trail', status', settled', used', h')) :
    assign'.size = assign.size ∧
      (status' = LRAT_ACCEPTED → settled' = false ∧ Agrees assign' model) := by
  induction fuel generalizing assign trail status settled used h assign' trail' status' settled' used' h' with
  | zero => simp [lrat_rup.loop2] at run
  | succ fuel ih =>
    by_cases enter : h < hints_n ∧ status = LRAT_ACCEPTED ∧ settled = false
    · obtain ⟨hh, hs, hq⟩ := enter
      have hm := (initial hs).2
      subst status
      subst settled
      generalize hid : words.getD (hints_at + h).toNat 0 = id at *
      by_cases live : id ≤ max_id ∧ 0 < id ∧ alive.getD id.toNat 0 ≠ 0
      · have hlive : ((decide (id ≤ max_id) && decide (id > 0)) &&
            (alive.getD id.toNat 0 != 0)) = true := by simpa [and_assoc] using live
        obtain ⟨k, hk, hkv, hkt⟩ := models id live.1 live.2.1 live.2.2
        have hkb : (store.getD (starts.getD id.toNat 0 + k).toNat 0 / 2).toNat < assign.size := by omega
        simp only [lrat_rup.loop2, hh, decide_true, beq_self_eq_true, Bool.not_false,
          Bool.and_self, ite_true, hid, hlive] at run
        cases scanRun : lrat_rup.loop3 store assign LRAT_ACCEPTED (starts.getD id.toNat 0)
            (lengths.getD id.toNat 0) 0 0 0 fuel with
        | none => simp only [scanRun, bind, Option.bind, Option.pure_def] at run; contradiction
        | some result =>
          rcases result with ⟨scanned, remaining, unit, j⟩
          simp only [scanRun, bind, Option.bind, Option.pure_def] at run
          by_cases accepted : scanned = LRAT_ACCEPTED
          · obtain ⟨done, positive, single⟩ := scan_model_witness fuel store assign model hm
              (starts.getD id.toNat 0) (lengths.getD id.toNat 0) k hk hkb hkt
              LRAT_ACCEPTED 0 0 0 scanned remaining unit j
              (by intro _; exact ⟨by simp, by simp, by intro impossible; simp at impossible⟩)
              scanRun accepted
            have notEmpty : remaining ≠ 0 := by intro hz; rw [hz] at positive; contradiction
            by_cases one : remaining = 1
            · have unitTrue : model (unit / 2).toNat = trueValue unit := by rw [single one]; exact hkt
              have nextModel : Agrees (assign.setIfInBounds (unit / 2).toNat (trueValue unit)) model := by
                rw [← unitTrue]
                exact agrees_write hm _
              simp only [accepted, beq_self_eq_true, ite_true,
                one, true_value_spec] at run
              obtain ⟨sz, inv⟩ := ih _ _ _ _ _ _ (by simpa using capacity)
                (by intro _; exact ⟨rfl, nextModel⟩) _ _ _ _ _ _ run
              exact ⟨sz.trans Array.size_setIfInBounds, inv⟩
            · simp only [accepted, beq_self_eq_true, ite_true,
                beq_eq_false_iff_ne.mpr notEmpty, Bool.false_eq_true, ite_false,
                beq_eq_false_iff_ne.mpr one] at run
              exact ih assign trail LRAT_NOT_UNIT false used (h + 1) capacity
                (by intro impossible; contradiction) _ _ _ _ _ _ run
          · simp only [beq_eq_false_iff_ne.mpr accepted, Bool.false_eq_true, ite_false] at run
            exact ih assign trail scanned false used (h + 1) capacity
              (by intro impossible; exact False.elim (accepted impossible)) _ _ _ _ _ _ run
      · have hlive : ((decide (id ≤ max_id) && decide (id > 0)) &&
            (alive.getD id.toNat 0 != 0)) = false := by simpa [and_assoc] using live
        simp only [lrat_rup.loop2, hh, decide_true, beq_self_eq_true, Bool.not_false,
          Bool.and_self, ite_true, hid, hlive, Bool.false_eq_true, ite_false,
          bind, Option.bind, Option.pure_def] at run
        exact ih assign trail LRAT_NOT_LIVE false used (h + 1) capacity
          (by intro impossible; contradiction) _ _ _ _ _ _ run
    · have guard : ((decide (h < hints_n) && (status == LRAT_ACCEPTED)) && !settled) = false := by
        cases settled <;> simp_all
      simp only [lrat_rup.loop2, guard, Bool.false_eq_true, ite_false,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, initial⟩

/-- Production RUP acceptance rules out a countermodel of the target clause.
The scratch starts consistent with the candidate model (zero scratch suffices).
The proof follows both extracted propagation loops; rollback cannot change
the reported status. It does not assume an abstract `Propagate` derivation. -/
theorem rup_no_countermodel (fuel : Nat) (words : Array UInt32)
    (target_at target_n hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id : UInt32) (model : Nat → UInt8)
    (models : WordModels model starts lengths alive store variables max_id)
    (capacity : variables.toNat ≤ assign.size) (agree : Agrees assign model)
    (falseTarget : ∀ j : UInt32, j < target_n →
      model ((words.getD (target_at + j).toNat 0) / 2).toNat =
        falseValue (words.getD (target_at + j).toNat 0))
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (accepted : lrat_rup words target_at target_n hints_at hints_n starts lengths alive store assign trail
      variables max_id fuel = some (LRAT_ACCEPTED, starts', lengths', alive', store', assign', trail')) : False := by
  unfold lrat_rup at accepted
  cases targetRun : lrat_rup.loop1 words target_at target_n assign trail variables LRAT_ACCEPTED false 0 0 fuel with
  | none => simp [targetRun] at accepted
  | some result =>
    rcases result with ⟨a1, t1, s1, q1, u1, i1⟩
    simp only [targetRun, bind, Option.bind, Option.pure_def] at accepted
    obtain ⟨size1, invariant1⟩ := target_preserves_model fuel words target_at target_n variables model falseTarget
      assign trail LRAT_ACCEPTED false 0 0 capacity (fun _ => ⟨rfl, agree⟩) a1 t1 s1 q1 u1 i1 targetRun
    cases hintsRun : lrat_rup.loop2 words hints_at hints_n starts lengths alive store a1 t1 max_id s1 q1 u1 0 fuel with
    | none => simp [hintsRun] at accepted
    | some result =>
      rcases result with ⟨a2, t2, s2, q2, u2, h2⟩
      simp only [hintsRun] at accepted
      obtain ⟨size2, invariant2⟩ := hints_preserve_model fuel words hints_at hints_n starts lengths alive store
        variables max_id model models a1 t1 s1 q1 u1 0 (by rw [size1]; exact capacity) invariant1
        a2 t2 s2 q2 u2 h2 hintsRun
      by_cases hs : s2 = LRAT_ACCEPTED
      · have hq := (invariant2 hs).1
        simp only [hs, hq, beq_self_eq_true, Bool.not_false, Bool.and_self, ite_true] at accepted
        cases undoRun : lrat_undo a2 t2 u2 fuel <;>
          simp [undoRun, LRAT_NO_CONFLICT, LRAT_ACCEPTED] at accepted
      · simp only [beq_eq_false_iff_ne.mpr hs, Bool.false_and, Bool.false_eq_true, ite_false] at accepted
        cases undoRun : lrat_undo a2 t2 u2 fuel <;> simp [undoRun, hs] at accepted

def decodeWord (lit : UInt32) : RupCheck.Literal :=
  ⟨(lit / 2).toNat, lit % 2 == 1⟩

def encodeAssignment (a : RupCheck.Assignment) (v : Nat) : UInt8 :=
  if a v then 2 else 1

def wordClause (words : Array UInt32) (start count : UInt32) : RupCheck.Clause :=
  (List.range count.toNat).map (fun n => decodeWord (words.getD (start + UInt32.ofNat n).toNat 0))

def wordDatabase (starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (max_id : UInt32) : RupCheck.Database :=
  fun id => if 0 < id ∧ id ≤ max_id.toNat ∧ alive.getD id 0 ≠ 0 then
    some (wordClause store (starts.getD id 0) (lengths.getD id 0)) else none

theorem word_holds_iff (a : RupCheck.Assignment) (lit : UInt32) :
    RupCheck.Holds a (decodeWord lit) ↔
      encodeAssignment a (lit / 2).toNat = trueValue lit := by
  cases hv : a (lit / 2).toNat <;> cases hp : (lit % 2 == 1) <;>
    simp [RupCheck.Holds, decodeWord, encodeAssignment, trueValue, hp]

theorem word_false_iff (a : RupCheck.Assignment) (lit : UInt32) :
    ¬ RupCheck.Holds a (decodeWord lit) ↔
      encodeAssignment a (lit / 2).toNat = falseValue lit := by
  cases hv : a (lit / 2).toNat <;> cases hp : (lit % 2 == 1) <;>
    simp [RupCheck.Holds, decodeWord, encodeAssignment, falseValue, hp]

theorem wordClause_satisfied_iff (a : RupCheck.Assignment) (words : Array UInt32) (start count : UInt32) :
    RupCheck.SatisfiesClause a (wordClause words start count) ↔
      ∃ k : UInt32, k < count ∧
        encodeAssignment a (words.getD (start + k).toNat 0 / 2).toNat =
          trueValue (words.getD (start + k).toNat 0) := by
  constructor
  · rintro ⟨lit, member, holds⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp member
    have hn' : n < count.toNat := List.mem_range.mp hn
    have hn32 : (UInt32.ofNat n).toNat = n := by
      change n % 4294967296 = n
      exact Nat.mod_eq_of_lt (Nat.lt_trans hn' count.toNat_lt)
    exact ⟨UInt32.ofNat n, by rw [UInt32.lt_iff_toNat_lt, hn32]; exact hn',
      (word_holds_iff a _).mp holds⟩
  · rintro ⟨k, hk, holds⟩
    refine ⟨decodeWord (words.getD (start + k).toNat 0), ?_, (word_holds_iff a _).mpr holds⟩
    apply List.mem_map.mpr
    exact ⟨k.toNat, List.mem_range.mpr (UInt32.lt_iff_toNat_lt.mp hk), by simp⟩

/-- The live database invariant required from the parser/store proof. -/
def LiveVariables (starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (variables max_id : UInt32) : Prop :=
  ∀ id : UInt32, id ≤ max_id → 0 < id → alive.getD id.toNat 0 ≠ 0 →
    ∀ k : UInt32, k < lengths.getD id.toNat 0 →
      (store.getD (starts.getD id.toNat 0 + k).toNat 0 / 2).toNat < variables.toNat

theorem wordModels_of_models (a : RupCheck.Assignment) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (variables max_id : UInt32)
    (valid : LiveVariables starts lengths alive store variables max_id)
    (models : RupCheck.Models a (wordDatabase starts lengths alive store max_id)) :
    WordModels (encodeAssignment a) starts lengths alive store variables max_id := by
  intro id upper lower live
  have lookup : wordDatabase starts lengths alive store max_id id.toNat =
      some (wordClause store (starts.getD id.toNat 0) (lengths.getD id.toNat 0)) := by
    have hlo : 0 < id.toNat := UInt32.lt_iff_toNat_lt.mp lower
    have hup : id.toNat ≤ max_id.toNat := UInt32.le_iff_toNat_le.mp upper
    exact if_pos ⟨hlo, hup, live⟩
  obtain ⟨k, hk, holds⟩ := (wordClause_satisfied_iff a _ _ _).mp (models _ _ lookup)
  exact ⟨k, hk, valid id upper lower live k hk, holds⟩

/-- An accepted call to the extracted production `lrat_rup` entails its
decoded target clause in the exact live word database. Unlike the abstract
`RupCheck.rup_entails`, the hypothesis here is execution of the production
implementation, not a supplied logical propagation derivation. Zero scratch
and the declared-variable invariant are obligations for the calling parser. -/
theorem production_rup_entails (fuel : Nat) (words : Array UInt32)
    (target_at target_n hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id : UInt32)
    (capacity : variables.toNat ≤ assign.size)
    (zero : ∀ v, v < assign.size → assign.getD v 0 = 0)
    (valid : LiveVariables starts lengths alive store variables max_id)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (accepted : lrat_rup words target_at target_n hints_at hints_n starts lengths alive store assign trail
      variables max_id fuel = some (LRAT_ACCEPTED, starts', lengths', alive', store', assign', trail'))
    (a : RupCheck.Assignment) (models : RupCheck.Models a (wordDatabase starts lengths alive store max_id)) :
    RupCheck.SatisfiesClause a (wordClause words target_at target_n) := by
  apply Classical.byContradiction
  intro notTarget
  apply rup_no_countermodel fuel words target_at target_n hints_at hints_n starts lengths alive store assign trail
    variables max_id (encodeAssignment a) (wordModels_of_models a _ _ _ _ _ _ valid models) capacity
    (fun v hv => Or.inl (zero v hv)) ?_ starts' lengths' alive' store' assign' trail' accepted
  intro j hj
  apply (word_false_iff a _).mp
  intro holds
  exact notTarget ((wordClause_satisfied_iff a words target_at target_n).mpr
    ⟨j, hj, (word_holds_iff a _).mp holds⟩)

/-- The empty-target case is the contradiction needed at the certificate's
acceptance point. Earlier additions and deletions must separately be shown to
preserve models from the original formula to this live database. -/
theorem production_empty_unsatisfiable (fuel : Nat) (words : Array UInt32)
    (target_at hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id : UInt32)
    (capacity : variables.toNat ≤ assign.size)
    (zero : ∀ v, v < assign.size → assign.getD v 0 = 0)
    (valid : LiveVariables starts lengths alive store variables max_id)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (assign' : Array UInt8) (trail' : Array UInt32)
    (accepted : lrat_rup words target_at 0 hints_at hints_n starts lengths alive store assign trail
      variables max_id fuel = some (LRAT_ACCEPTED, starts', lengths', alive', store', assign', trail')) :
    ∀ a, ¬ RupCheck.Models a (wordDatabase starts lengths alive store max_id) := by
  intro a models
  have impossible := production_rup_entails fuel words target_at 0 hints_at hints_n starts lengths alive store
    assign trail variables max_id capacity zero valid starts' lengths' alive' store' assign' trail' accepted a models
  simpa [RupCheck.SatisfiesClause, wordClause] using impossible

end Oak.LRATRUP
