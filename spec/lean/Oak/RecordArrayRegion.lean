import Oak.CheckerRefinement
import Oak.PairStoreEffects

/-!
# Exact record-array field geometry

This module isolates the geometry needed before a four-word pair-store block
may be related to one direct fixed-size `u64` array field.  The record and field
metadata are a projection of a successful compiler-supplied lookup; the lookup,
its uniqueness, and its direct-`u64` classification are not formalized here.

The predicates and theorems grant no memory authority and do not inspect the
region's writability.  They prove neither instruction admission or execution,
trap preservation, memory type, alias or observer exclusion, ordering,
atomicity, visibility, completion, nor publication safety.
-/

namespace Oak.RecordArrayRegion

open Oak.CheckerRefinement

/-- The exact declared record-array field selected by the compiler. Sizes and
offsets count bytes; `length` counts eight-byte elements. -/
structure RecordArrayField where
  recordName : String
  fieldName : String
  recordSize : Int
  offset : Int
  size : Int
  length : Int
  deriving Repr, DecidableEq

/-- The selected field exactly matches the nominal record place and fits in
the remaining byte extent. This is geometry only; `extent.writable` is
deliberately irrelevant. -/
def validField (place : RecordPlace) (extent : Region)
    (field : RecordArrayField) : Bool :=
  decide (place.name != "" ∧
    field.recordName = place.name ∧
    field.fieldName != "" ∧
    field.recordSize > 0 ∧
    place.offset ≥ 0 ∧ place.offset ≤ field.recordSize ∧
    extent.size = field.recordSize - place.offset ∧
    field.offset = place.offset ∧
    field.offset % 8 = 0 ∧
    field.length > 0 ∧ field.length ≤ 4294967296 ∧
    field.size = 8 * field.length ∧
    field.size ≤ extent.size)

/-- A constant loop bound leaves four elements beginning at every admitted
index of the selected eight-byte field. -/
def quadAdmits (field : RecordArrayField) (bound : IdxFact)
    (stride : Int) : Bool :=
  decide (stride = 8 ∧
    bound.boundReg < 0 ∧
    bound.slack = false ∧
    bound.bound > 0 ∧
    field.length ≥ 4 ∧
    bound.bound ≤ field.length - 3)

/-- Valid field geometry plus the quad-loop decision places all four words
inside the exact nominal field and below the verifier's 32-bit index modulus. -/
theorem valid_quad_sound (place : RecordPlace) (extent : Region)
    (field : RecordArrayField) (bound : IdxFact) (stride i : Int)
    (hvalid : validField place extent field = true)
    (hquad : quadAdmits field bound stride = true)
    (hi : 0 ≤ i) (hib : i < bound.bound) :
    field.recordName = place.name ∧
      place.name != "" ∧
      field.offset = place.offset ∧
      0 ≤ 8 * i ∧
      8 * i + 32 ≤ field.size ∧
      field.offset + 8 * i + 32 ≤ field.recordSize ∧
      i + 3 < 4294967296 := by
  simp only [validField, decide_eq_true_eq] at hvalid
  simp only [quadAdmits, decide_eq_true_eq] at hquad
  obtain ⟨hplace, hrecord, _, _, _, _, hextent, hoffset, _, _,
    hlengthMax, hsize, hfits⟩ := hvalid
  obtain ⟨_, _, _, _, _, hbound⟩ := hquad
  refine ⟨hrecord, hplace, hoffset, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Under the same checked geometry, the staged two-pair write log has the
same final word memory as four scalar stores. This composes final-state algebra
only; the surrounding admission and authority obligations remain separate. -/
theorem quad_writes_eq_fillWords_four (m : Oak.PairCopies.Mem)
    (place : RecordPlace) (extent : Region) (field : RecordArrayField)
    (bound : IdxFact) (stride : Int) (i value : Nat)
    (hvalid : validField place extent field = true)
    (hquad : quadAdmits field bound stride = true)
    (hi : 0 ≤ (Int.ofNat i)) (hib : Int.ofNat i < bound.bound) :
    Oak.PairStoreEffects.applyWrites m
        (Oak.PairStoreEffects.block4Writes i value) =
      Oak.BlockedFill.fillWords m i value 4 := by
  obtain ⟨_, _, _, _, _, _, hnowrap⟩ :=
    valid_quad_sound place extent field bound stride (Int.ofNat i)
      hvalid hquad hi hib
  have hnowrapNat : i + 3 < Oak.PairStoreEffects.indexModulus := by
    change i + 3 < 4294967296
    apply Int.ofNat_lt.mp
    simpa using hnowrap
  exact Oak.PairStoreEffects.apply_block4_writes_eq_fillWords_four
    m i value hnowrapNat

/-! Exact decisions for the synchronized Go geometry helper. -/

example : validField ⟨"Regime", 0⟩ ⟨2072, true⟩ ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ = true := by decide
example : validField ⟨"Regime", 0⟩ ⟨2072, false⟩ ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ = true := by decide
example : validField ⟨"Regime", 24⟩ ⟨2048, true⟩ ⟨"Regime", "pages", 2072, 24, 2048, 256⟩ = true := by decide
example : validField ⟨"Regime", 0⟩ ⟨2072, true⟩ ⟨"Decoy", "pages", 2072, 0, 2048, 256⟩ = false := by decide
example : validField ⟨"Regime", 0⟩ ⟨2072, true⟩ ⟨"Regime", "", 2072, 0, 2048, 256⟩ = false := by decide
example : validField ⟨"Regime", 1⟩ ⟨2071, true⟩ ⟨"Regime", "pages", 2072, 1, 2048, 256⟩ = false := by decide
example : validField ⟨"Regime", 0⟩ ⟨2072, true⟩ ⟨"Regime", "pages", 2072, 0, 0, 0⟩ = false := by decide
example : validField ⟨"Regime", 24⟩ ⟨2048, true⟩ ⟨"Regime", "pages", 2072, 24, 2056, 257⟩ = false := by decide
example : validField ⟨"Regime", 0⟩ ⟨34359738368, true⟩ ⟨"Regime", "pages", 34359738368, 0, 34359738368, 4294967296⟩ = true := by decide
example : validField ⟨"Regime", 0⟩ ⟨34359738376, true⟩ ⟨"Regime", "pages", 34359738376, 0, 34359738376, 4294967297⟩ = false := by decide
example : quadAdmits ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ ⟨(-1), 253, false, 0⟩ 8 = true := by decide
example : quadAdmits ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ ⟨(-1), 254, false, 0⟩ 8 = false := by decide
example : quadAdmits ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ ⟨(-1), 256, false, 0⟩ 8 = false := by decide
example : quadAdmits ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ ⟨(-1), 0, false, 0⟩ 8 = false := by decide
example : quadAdmits ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ ⟨1, 253, false, 0⟩ 8 = false := by decide
example : quadAdmits ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ ⟨(-1), 253, true, 0⟩ 8 = false := by decide
example : quadAdmits ⟨"Regime", "pages", 2072, 0, 2048, 256⟩ ⟨(-1), 253, false, 0⟩ 4 = false := by decide
example : quadAdmits ⟨"Regime", "pages", 34359738368, 0, 34359738368, 4294967296⟩ ⟨(-1), 4294967293, false, 0⟩ 8 = true := by decide
example : quadAdmits ⟨"Regime", "pages", 34359738368, 0, 34359738368, 4294967296⟩ ⟨(-1), 4294967294, false, 0⟩ 8 = false := by decide

end Oak.RecordArrayRegion
