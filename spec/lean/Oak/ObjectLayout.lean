import Std.Tactic.BVDecide

/-!
# Object-writer relocation footprints

`asm/object.go` admits a relocation only when every instruction word the
object or executable writer consumes lies inside its defining function.  Most
relocations occupy one four-byte instruction.  The AArch64 `adrl21` pseudo and
the two RV64 PC-relative pseudos occupy adjacent instruction pairs.

This module is the direct mathematical transliteration of that small admission
decision.  It proves only the footprint and bounds seam: ELF/Mach-O relocation
meaning, symbol resolution, and the bytes emitted for their records remain
separate obligations.
-/

namespace Oak.ObjectLayout

/-- Relocations whose application consumes one instruction word. -/
def singleWordRelocation (kind : String) : Bool :=
  kind == "call26" || kind == "jump26" || kind == "branch26" ||
  kind == "condbr19" || kind == "tbz14" || kind == "adr21" ||
  kind == "adrp21" || kind == "lo12"

/-- Relocations whose application consumes two adjacent instruction words. -/
def pairedRelocation (kind : String) : Bool :=
  kind == "adrl21" || kind == "riscv_pcrel" || kind == "riscv_call_plt"

/-- Number of function bytes a recognized relocation may inspect or patch.

Returning `none` for every unrecognized spelling makes the specification's
classification boundary fail closed. -/
def relocationFootprint (kind : String) : Option Nat :=
  if singleWordRelocation kind then some 4
  else if pairedRelocation kind then some 8
  else none

/-- The overflow-free bounds decision used before placing a relocation.

The signed offset reflects Go's `Relocation.Offset`; section lengths and
footprints are nonnegative.  Stating the sum in unbounded `Int` makes explicit
that acceptance cannot arise from machine-integer wraparound. -/
def relocationFits (textLen : Nat) (offset : Int) (kind : String) : Bool :=
  match relocationFootprint kind with
  | none => false
  | some width => decide (0 ≤ offset ∧ offset + (width : Int) ≤ (textLen : Int))

theorem relocationFootprint_four_or_eight {kind : String} {width : Nat}
    (h : relocationFootprint kind = some width) :
    width = 4 ∨ width = 8 := by
  unfold relocationFootprint at h
  split at h
  · simp_all
  · split at h <;> simp_all

theorem relocationFootprint_positive {kind : String} {width : Nat}
    (h : relocationFootprint kind = some width) : 0 < width := by
  rcases relocationFootprint_four_or_eight h with h | h <;> omega

theorem relocationFootprint_at_least_word {kind : String} {width : Nat}
    (h : relocationFootprint kind = some width) : 4 ≤ width := by
  rcases relocationFootprint_four_or_eight h with h | h <;> omega

/-- Admission places the relocation's first complete instruction word inside
the function. -/
theorem relocationFits_first_word {textLen : Nat} {offset : Int} {kind : String}
    (h : relocationFits textLen offset kind = true) :
    0 ≤ offset ∧ offset + 4 ≤ (textLen : Int) := by
  unfold relocationFits at h
  generalize hfoot : relocationFootprint kind = footprint at h
  cases footprint with
  | none => simp at h
  | some width =>
      simp only [decide_eq_true_eq] at h
      constructor
      · exact h.1
      · have hwidth : 4 ≤ width := relocationFootprint_at_least_word hfoot
        have hwidthInt : (4 : Int) ≤ width := by exact_mod_cast hwidth
        omega

/-- A paired relocation's second complete instruction word is also inside the
function; this is the condition needed before a writer reads or patches it. -/
theorem relocationFits_paired_second_word {textLen : Nat} {offset : Int} {kind : String}
    (hpair : relocationFootprint kind = some 8)
    (h : relocationFits textLen offset kind = true) :
    offset + 8 ≤ (textLen : Int) := by
  simp [relocationFits, hpair] at h
  exact h.2

/-- For a paired relocation, admission is exactly nonnegative placement of its
eight-byte instruction pair inside the function. -/
theorem pair_fits_iff {textLen : Nat} {offset : Int} {kind : String}
    (hpair : relocationFootprint kind = some 8) :
    relocationFits textLen offset kind = true ↔
      0 ≤ offset ∧ offset + 8 ≤ (textLen : Int) := by
  simp [relocationFits, hpair]

/-! ## Go correspondence pins

`asm/object_layout_refinement_test.go` renders the production Go decisions in
this form.  A changed Go kind table or boundary decision must therefore update
these kernel-checked examples deliberately.
-/

example : relocationFootprint "call26" = some 4 := by decide
example : relocationFootprint "jump26" = some 4 := by decide
example : relocationFootprint "branch26" = some 4 := by decide
example : relocationFootprint "condbr19" = some 4 := by decide
example : relocationFootprint "tbz14" = some 4 := by decide
example : relocationFootprint "adr21" = some 4 := by decide
example : relocationFootprint "adrp21" = some 4 := by decide
example : relocationFootprint "lo12" = some 4 := by decide
example : relocationFootprint "adrl21" = some 8 := by decide
example : relocationFootprint "riscv_pcrel" = some 8 := by decide
example : relocationFootprint "riscv_call_plt" = some 8 := by decide
example : relocationFootprint "unknown" = none := by decide

-- Every public spelling is pinned at the same five boundaries: negative,
-- one byte short, exact at zero, exact at offset four, and one byte past that
-- nonzero fit.
example : relocationFits 4 (-1) "call26" = false := by decide
example : relocationFits 3 0 "call26" = false := by decide
example : relocationFits 4 0 "call26" = true := by decide
example : relocationFits 8 4 "call26" = true := by decide
example : relocationFits 8 5 "call26" = false := by decide

example : relocationFits 4 (-1) "jump26" = false := by decide
example : relocationFits 3 0 "jump26" = false := by decide
example : relocationFits 4 0 "jump26" = true := by decide
example : relocationFits 8 4 "jump26" = true := by decide
example : relocationFits 8 5 "jump26" = false := by decide

example : relocationFits 4 (-1) "branch26" = false := by decide
example : relocationFits 3 0 "branch26" = false := by decide
example : relocationFits 4 0 "branch26" = true := by decide
example : relocationFits 8 4 "branch26" = true := by decide
example : relocationFits 8 5 "branch26" = false := by decide

example : relocationFits 4 (-1) "condbr19" = false := by decide
example : relocationFits 3 0 "condbr19" = false := by decide
example : relocationFits 4 0 "condbr19" = true := by decide
example : relocationFits 8 4 "condbr19" = true := by decide
example : relocationFits 8 5 "condbr19" = false := by decide

example : relocationFits 4 (-1) "tbz14" = false := by decide
example : relocationFits 3 0 "tbz14" = false := by decide
example : relocationFits 4 0 "tbz14" = true := by decide
example : relocationFits 8 4 "tbz14" = true := by decide
example : relocationFits 8 5 "tbz14" = false := by decide

example : relocationFits 4 (-1) "adr21" = false := by decide
example : relocationFits 3 0 "adr21" = false := by decide
example : relocationFits 4 0 "adr21" = true := by decide
example : relocationFits 8 4 "adr21" = true := by decide
example : relocationFits 8 5 "adr21" = false := by decide

example : relocationFits 4 (-1) "adrp21" = false := by decide
example : relocationFits 3 0 "adrp21" = false := by decide
example : relocationFits 4 0 "adrp21" = true := by decide
example : relocationFits 8 4 "adrp21" = true := by decide
example : relocationFits 8 5 "adrp21" = false := by decide

example : relocationFits 4 (-1) "lo12" = false := by decide
example : relocationFits 3 0 "lo12" = false := by decide
example : relocationFits 4 0 "lo12" = true := by decide
example : relocationFits 8 4 "lo12" = true := by decide
example : relocationFits 8 5 "lo12" = false := by decide

example : relocationFits 8 (-1) "adrl21" = false := by decide
example : relocationFits 7 0 "adrl21" = false := by decide
example : relocationFits 8 0 "adrl21" = true := by decide
example : relocationFits 12 4 "adrl21" = true := by decide
example : relocationFits 12 5 "adrl21" = false := by decide

example : relocationFits 8 (-1) "riscv_pcrel" = false := by decide
example : relocationFits 7 0 "riscv_pcrel" = false := by decide
example : relocationFits 8 0 "riscv_pcrel" = true := by decide
example : relocationFits 12 4 "riscv_pcrel" = true := by decide
example : relocationFits 12 5 "riscv_pcrel" = false := by decide

example : relocationFits 8 (-1) "riscv_call_plt" = false := by decide
example : relocationFits 7 0 "riscv_call_plt" = false := by decide
example : relocationFits 8 0 "riscv_call_plt" = true := by decide
example : relocationFits 12 4 "riscv_call_plt" = true := by decide
example : relocationFits 12 5 "riscv_call_plt" = false := by decide

example : relocationFits 4 (-1) "unknown" = false := by decide
example : relocationFits 3 0 "unknown" = false := by decide
example : relocationFits 4 0 "unknown" = false := by decide
example : relocationFits 8 4 "unknown" = false := by decide
example : relocationFits 8 5 "unknown" = false := by decide

end Oak.ObjectLayout
