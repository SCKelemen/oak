import Oak.LRATPreflightExtracted
import Oak.LRATBounds

/-! Production admission before allocation. This proves the actual header and
record guards supply non-wrapping positive byte requests and complete framing.
It does not model malloc, ownership conversion, free, or FFI execution. -/
set_option autoImplicit false
namespace Oak.LRATPreflight

/-- Facts established by the production header gate, also used by the stream
reader before allocating its input buffer. -/
structure HeaderSafe (words : Array UInt32) : Prop where
  header : 8 ≤ words.size.toUInt32.toNat
  magic : words.getD 0 0 = LRAT_MAGIC
  variables : (words.getD 1 0).toNat < 1073741823
  identifiers : (words.getD 5 0).toNat < 1073741823
  store : (words.getD 6 0).toNat < 1073741823
  clauses : words.getD 2 0 ≤ words.getD 5 0
  body : (words.getD 3 0).toNat + (words.getD 4 0).toNat ≤ 1073741815

theorem production_header_safe (words : Array UInt32) (fuel : Nat)
    (run : lrat_header_fits words fuel = some true) : HeaderSafe words := by
  simp only [lrat_header_fits, lrat_alloc_fits, lrat_fits, bind, Option.bind,
    Option.pure_def, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc] at run
  obtain ⟨size, magic, variables, identifiers, store, clauses, first, second⟩ := run
  constructor
  · exact UInt32.le_iff_toNat_le.mp size
  · exact magic
  · exact UInt32.lt_iff_toNat_lt.mp variables
  · exact UInt32.lt_iff_toNat_lt.mp identifiers
  · exact UInt32.lt_iff_toNat_lt.mp store
  · exact clauses
  · rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ first] at second
    have := UInt32.le_iff_toNat_le.mp first
    change (words.getD 3 0).toNat ≤ 1073741815 at this
    change (words.getD 4 0).toNat ≤ 1073741815 - (words.getD 3 0).toNat at second
    omega

/-- Actual allocation expressions, with one reserved sentinel element. -/
structure AllocationSafe (count : UInt32) : Prop where
  elements : (count + 1).toNat = count.toNat + 1
  positiveElements : 0 < (count + 1).toNat
  bytes : ((count + 1) * 4).toNat = (count.toNat + 1) * 4
  positiveBytes : 0 < ((count + 1) * 4).toNat

theorem allocation_safe (count : UInt32) (bound : count.toNat < 1073741823) :
    AllocationSafe count := by
  have gate : LRATBounds.lrat_alloc_fits count 0 = some true := by
    simp only [LRATBounds.lrat_alloc_fits, Option.pure_def, Option.some.injEq,
      decide_eq_true_eq, UInt32.lt_iff_toNat_lt]
    exact bound
  obtain ⟨elements, bytes, positive⟩ := LRATBounds.allocation_exact count 0 gate
  exact ⟨elements, by rw [elements]; omega, bytes, positive⟩

/-- The three counts cover all six scratch allocations: starts/lengths/alive,
store, and assign/trail. The word-sized and byte-sized requests are exact. -/
theorem production_header_allocations (words : Array UInt32) (fuel : Nat)
    (run : lrat_header_fits words fuel = some true) :
    AllocationSafe (words.getD 5 0) ∧ AllocationSafe (words.getD 6 0) ∧
      AllocationSafe (words.getD 1 0) := by
  have h := production_header_safe words fuel run
  exact ⟨allocation_safe _ h.identifiers, allocation_safe _ h.store, allocation_safe _ h.variables⟩

/-- Stream input allocation is also guarded by the actual header predicate. -/
theorem production_stream_allocation (words : Array UInt32) (fuel : Nat)
    (run : lrat_header_fits words fuel = some true) :
    ((8 + (words.getD 3 0 + words.getD 4 0)) * 4).toNat =
      (8 + (words.getD 3 0).toNat + (words.getD 4 0).toNat) * 4 ∧
    0 < ((8 + (words.getD 3 0 + words.getD 4 0)) * 4).toNat := by
  have h := production_header_safe words fuel run
  exact (LRATBounds.stream_allocation_exact _ _ 0
    ((LRATBounds.fits_iff _ _ _ _).mpr h.body)).2

/-- Accepted complete-record preflight establishes its header and exact
machine-view framing; no clause syntax or proof acceptance is claimed. -/
theorem production_record_preflight (words : Array UInt32) (fuel : Nat)
    (run : lrat_record_fits words fuel = some true) :
    lrat_header_fits words fuel = some true ∧
      8 + (words.getD 3 0).toNat + (words.getD 4 0).toNat = words.size.toUInt32.toNat := by
  unfold lrat_record_fits at run
  cases headerRun : lrat_header_fits words fuel with
  | none => simp [headerRun] at run
  | some header =>
    simp only [headerRun, lrat_fits, bind, Option.bind, Option.pure_def,
      Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at run
    obtain ⟨⟨rfl, first, second⟩, steps⟩ := run
    refine ⟨rfl, ?_⟩
    change 8 ≤ words.size.toUInt32 at first
    change words.getD 3 0 ≤ words.size.toUInt32 - 8 at second
    change words.getD 4 0 = words.size.toUInt32 - 8 - words.getD 3 0 at steps
    have firstN := UInt32.le_iff_toNat_le.mp first
    have secondN := UInt32.le_iff_toNat_le.mp second
    rw [UInt32.toNat_sub_of_le _ _ first] at secondN
    have stepN := congrArg UInt32.toNat steps
    rw [UInt32.toNat_sub_of_le _ _ second, UInt32.toNat_sub_of_le _ _ first] at stepN
    change 8 ≤ words.size.toUInt32.toNat at firstN
    change (words.getD 3 0).toNat ≤ words.size.toUInt32.toNat - 8 at secondN
    change (words.getD 4 0).toNat = words.size.toUInt32.toNat - 8 - (words.getD 3 0).toNat at stepN
    omega

/-- The allocating entry's complete preflight supplies all scratch arithmetic
and bounds every header read. No allocation-success premise is needed. -/
theorem production_record_allocation_safe (words : Array UInt32) (fuel : Nat)
    (run : lrat_record_fits words fuel = some true) :
    (∀ i, i < 8 → i < words.size) ∧
    AllocationSafe (words.getD 5 0) ∧ AllocationSafe (words.getD 6 0) ∧
    AllocationSafe (words.getD 1 0) ∧
    8 + (words.getD 3 0).toNat + (words.getD 4 0).toNat = words.size.toUInt32.toNat := by
  obtain ⟨headerRun, frame⟩ := production_record_preflight words fuel run
  have h := production_header_safe words fuel headerRun
  obtain ⟨ids, store, variables⟩ := production_header_allocations words fuel headerRun
  refine ⟨?_, ids, store, variables, frame⟩
  intro i hi
  have modBound : words.size.toUInt32.toNat ≤ words.size := Nat.mod_le _ _
  have := h.header
  omega

end Oak.LRATPreflight
