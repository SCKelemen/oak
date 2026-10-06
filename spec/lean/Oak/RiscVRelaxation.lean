import Oak.RiscVCompressedBranchEncoding

/-!
# RV64 shrinking layout and relaxation

A layout records whether each expanded instruction occupies two bytes (`true`)
or four (`false`). Labels identify boundaries between these instructions.
There are no alignment regions: `rv64Expand` rejects them. Shrinking keeps
instruction/label indices fixed and cannot increase any intervening distance.

Each pass consumes eligibility decisions from a single old-layout snapshot.
The driver is proved terminating for any such decision function; the production
eligibility oracle and Go loop are checked by bounded correspondence tests.
Addresses here are unbounded natural numbers, with signed integer differences.
-/

namespace Oak.RiscVRelaxation

abbrev Layout := List Bool

def width (short : Bool) : Nat := if short then 2 else 4

def offset : Layout → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | short :: rest, i + 1 => width short + offset rest i

def delta (layout : Layout) (source target : Nat) : Int :=
  (offset layout target : Int) - (offset layout source : Int)

@[simp] theorem offset_zero (layout : Layout) : offset layout 0 = 0 := by
  cases layout <;> rfl

/-- Pointwise shrinking, without inserting, deleting, or reordering units. -/
inductive Shrinks : Layout → Layout → Prop
  | nil : Shrinks [] []
  | cons {n o : Bool} {ns os : Layout} (head : width n ≤ width o)
      (tail : Shrinks ns os) : Shrinks (n :: ns) (o :: os)

theorem Shrinks.refl (layout : Layout) : Shrinks layout layout := by
  induction layout with
  | nil => exact .nil
  | cons b bs ih => exact .cons (Nat.le_refl _) ih

theorem Shrinks.trans {a b c : Layout} (hab : Shrinks a b) (hbc : Shrinks b c) :
    Shrinks a c := by
  induction hab generalizing c with
  | nil => cases hbc; exact .nil
  | cons hhead htail ih =>
      cases hbc with
      | cons hhead' htail' => exact .cons (Nat.le_trans hhead hhead') (ih htail')

theorem Shrinks.length_eq {n o : Layout} (h : Shrinks n o) : n.length = o.length := by
  induction h <;> simp_all

theorem offset_even (layout : Layout) (i : Nat) : (offset layout i : Int) % 2 = 0 := by
  induction layout generalizing i with
  | nil => simp [offset]
  | cons b bs ih =>
      cases i with
      | zero => simp [offset]
      | succ i => cases b <;> simp [offset, width, Int.add_emod, ih]

theorem delta_even (layout : Layout) (source target : Nat) :
    delta layout source target % 2 = 0 := by
  have hs := offset_even layout source
  have ht := offset_even layout target
  unfold delta
  omega

/-- Forward distances stay nonnegative and cannot grow. This includes labels
at the end of the function and shrinking the source instruction itself. -/
theorem forward_bounds {n o : Layout} (h : Shrinks n o) (i j : Nat) (hij : i ≤ j) :
    0 ≤ delta n i j ∧ delta n i j ≤ delta o i j := by
  induction h generalizing i j with
  | nil => simp [delta, offset]
  | @cons n o ns os hhead htail ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp [delta, offset]
          | succ j =>
              have hb := ih 0 j (Nat.zero_le _)
              simp only [delta, offset, offset_zero, Int.natCast_add, Int.natCast_zero, Int.sub_zero] at *
              omega
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              have hb := ih i j (by omega)
              simp only [delta, offset, Int.natCast_add] at *
              omega

def fits (limit : Nat) (layout : Layout) (source target : Nat) : Bool :=
  decide (delta layout source target % 2 = 0 ∧
    -(limit : Int) ≤ delta layout source target ∧ delta layout source target < limit)

/-- The signed range is asymmetric at the positive endpoint. Both directions
are handled without replacing it by an absolute-value bound. -/
theorem fits_preserved {n o : Layout} (h : Shrinks n o) {limit source target : Nat}
    (hf : fits limit o source target = true) : fits limit n source target = true := by
  simp only [fits, decide_eq_true_eq] at *
  have he := delta_even n source target
  by_cases hforward : source ≤ target
  · have hb := forward_bounds h source target hforward
    omega
  · have hb := forward_bounds h target source (by omega)
    simp only [delta] at *
    omega

open Oak.RiscVCompressedBranchEncoding in
theorem localCB_preserved {n o : Layout} (h : Shrinks n o)
    {nonzero : Bool} {rs1 rs2 source target : Nat} {word : BitVec 16}
    (hc : localCB nonzero rs1 rs2 (offset o source) (offset o target) = some word) :
    ∃ next, localCB nonzero rs1 rs2 (offset n source) (offset n target) = some next ∧
      (offset n source : Int) + decodeCB next = (offset n target : Int) := by
  obtain ⟨hr1, hr2, hz, hf⟩ := (localCB_some_iff _ _ _ _ _).mp ⟨word, hc⟩
  have hf' := fits_preserved h (limit := 256) (source := source) (target := target) hf
  obtain ⟨next, hn⟩ := (localCB_some_iff nonzero rs1 rs2 (offset n source) (offset n target)).mpr
    ⟨hr1, hr2, hz, hf'⟩
  exact ⟨next, hn, localCB_reaches hn⟩

open Oak.RiscVCompressedBranchEncoding in
theorem localCJ_preserved {n o : Layout} (h : Shrinks n o)
    {rd source target : Nat} {word : BitVec 16}
    (hc : localCJ rd (offset o source) (offset o target) = some word) :
    ∃ next, localCJ rd (offset n source) (offset n target) = some next ∧
      (offset n source : Int) + decodeCJ next = (offset n target : Int) := by
  obtain ⟨hr, hf⟩ := (localCJ_some_iff _ _ _).mp ⟨word, hc⟩
  have hf' := fits_preserved h (limit := 2048) (source := source) (target := target) hf
  obtain ⟨next, hn⟩ := (localCJ_some_iff rd (offset n source) (offset n target)).mpr ⟨hr, hf'⟩
  exact ⟨next, hn, localCJ_reaches hn⟩

/-- A snapshot's eligible units shrink simultaneously. Eligibility includes
register restrictions, pinned relocation pairs, label lookup, and range. -/
def pass (eligible : Nat → Bool) : Layout → Layout
  | [] => []
  | short :: rest => (short || eligible 0) :: pass (fun i => eligible (i + 1)) rest

theorem pass_shrinks (eligible : Nat → Bool) (layout : Layout) :
    Shrinks (pass eligible layout) layout := by
  induction layout generalizing eligible with
  | nil => exact .nil
  | cons b bs ih =>
      apply Shrinks.cons _ (ih _)
      cases b <;> cases eligible 0 <;> decide

/-- The decreasing measure counts remaining four-byte instructions, including
ones that are permanently ineligible; it is bounded by the instruction count. -/
def wideCount : Layout → Nat
  | [] => 0
  | short :: rest => (if short then 0 else 1) + wideCount rest

theorem wideCount_le_length (layout : Layout) : wideCount layout ≤ layout.length := by
  induction layout with
  | nil => simp [wideCount]
  | cons b bs ih => cases b <;> simp [wideCount] <;> omega

theorem Shrinks.count_le {n o : Layout} (h : Shrinks n o) : wideCount n ≤ wideCount o := by
  induction h with
  | nil => simp [wideCount]
  | @cons n o ns os hhead htail ih =>
      cases n <;> cases o <;> simp_all [width, wideCount] <;> omega

theorem Shrinks.eq_of_count_eq {n o : Layout} (h : Shrinks n o)
    (hc : wideCount n = wideCount o) : n = o := by
  induction h with
  | nil => rfl
  | @cons n o ns os hhead htail ih =>
      have hle := htail.count_le
      cases n <;> cases o <;> simp_all [width, wideCount]
      omega

theorem pass_count_lt (eligible : Nat → Bool) (layout : Layout)
    (hne : pass eligible layout ≠ layout) : wideCount (pass eligible layout) < wideCount layout := by
  have h := pass_shrinks eligible layout
  have hle := h.count_le
  have hneq : wideCount (pass eligible layout) ≠ wideCount layout := fun hc => hne (h.eq_of_count_eq hc)
  omega

/-- The same snapshot/repeat-until-unchanged driver as Go, returning its final
layout and number of changing passes. Its definition is well founded for any
eligibility oracle; there is one additional unchanged pass to detect exit. -/
def relax (choose : Layout → Nat → Bool) (layout : Layout) : Layout × Nat :=
  let next := pass (choose layout) layout
  if h : next = layout then (layout, 0)
  else
    let result := relax choose next
    (result.1, result.2 + 1)
termination_by wideCount layout
decreasing_by exact pass_count_lt _ _ h

theorem relax_spec (choose : Layout → Nat → Bool) (layout : Layout) :
    Shrinks (relax choose layout).1 layout ∧
    pass (choose (relax choose layout).1) (relax choose layout).1 = (relax choose layout).1 ∧
    (relax choose layout).2 ≤ wideCount layout := by
  fun_induction relax choose layout with
  | case1 layout next h => exact ⟨Shrinks.refl _, h, Nat.zero_le _⟩
  | case2 layout next h result ih =>
      have hs := pass_shrinks (choose layout) layout
      have hc := pass_count_lt (choose layout) layout h
      dsimp only [next, result] at *
      exact ⟨ih.1.trans hs, ih.2.1, by omega⟩

theorem relax_pass_bound (choose : Layout → Nat → Bool) (layout : Layout) :
    (relax choose layout).2 ≤ layout.length :=
  Nat.le_trans (relax_spec choose layout).2.2 (wideCount_le_length layout)

theorem relax_preserves_fits (choose : Layout → Nat → Bool) (layout : Layout)
    {limit source target : Nat} (hf : fits limit layout source target = true) :
    fits limit (relax choose layout).1 source target = true :=
  fits_preserved (relax_spec choose layout).1 hf

/-- Structurally recursive evaluation view for kernel-checked production pins.
The zero-fuel case is only a cutoff; the equivalence theorem requires enough
fuel for all changing passes plus the final unchanged pass. -/
def relaxFuel (choose : Layout → Nat → Bool) : Nat → Layout → Layout × Nat
  | 0, layout => (layout, 0)
  | fuel + 1, layout =>
      let next := pass (choose layout) layout
      if next = layout then (layout, 0)
      else
        let result := relaxFuel choose fuel next
        (result.1, result.2 + 1)

theorem relaxFuel_eq (choose : Layout → Nat → Bool) (fuel : Nat) (layout : Layout)
    (hf : wideCount layout < fuel) : relaxFuel choose fuel layout = relax choose layout := by
  induction fuel generalizing layout with
  | zero => omega
  | succ fuel ih =>
      rw [relaxFuel, relax]
      dsimp only
      split
      next h => rfl
      next h =>
        have hc := pass_count_lt (choose layout) layout h
        rw [ih _ (by omega)]

theorem relax_eq_of_fuel_eq {choose : Layout → Nat → Bool} {layout : Layout}
    {result : Layout × Nat} {fuel : Nat} (hf : wideCount layout < fuel)
    (hr : relaxFuel choose fuel layout = result) : relax choose layout = result :=
  (relaxFuel_eq choose fuel layout hf).symm.trans hr

/-- Bounded production checks supply a descriptor only after the instruction
shape, relocation-pair exclusion, and label lookup have admitted a candidate.
The target is an instruction-boundary index, not its changing byte address. -/
structure Candidate where
  limit : Nat
  target : Nat
  deriving DecidableEq, Repr

def chooseCandidates (candidates : List (Option Candidate)) (layout : Layout) (i : Nat) : Bool :=
  match candidates[i]? with
  | some (some c) => fits c.limit layout i c.target
  | _ => false

end Oak.RiscVRelaxation
