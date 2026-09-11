import ExtractionDecoder
import CertifiedStream

set_option autoImplicit false
namespace OakVerification.Extraction
open Ranges Extracted PropagationState Decimal

/-! The extracted RUP kernel refines the certified propagation chain
(docs/spec/95-extraction.md, roadmap step 3's fourth increment). `rup_check`
is what the compiler extracts from `self_hosted_rup.oak`: four loops over
`UInt32` and `Array` — zeroing the scratch, validating the hints, assuming
the negated target, and walking the hint chain. `PropagationChain.check` is
the proof-producing model `CertifiedStream` publishes under. This file
proves that, on the inputs the stream checker hands the kernel (a pool whose
literals are below the variable count, live hints, the 256-slot tables), the
kernel's acceptance is exactly `(PropagationChain.check ...).isSome`. -/

/-! ## Arrays as lists -/

def toNats (a : Array UInt32) : List Nat := a.toList.map UInt32.toNat

theorem toNats_length (a : Array UInt32) : (toNats a).length = a.size := by
  simp [toNats]

theorem getD_toNats (a : Array UInt32) (i : Nat) :
    (a.getD i 0).toNat = (toNats a).getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [toNats, List.getElem?_map, Array.getElem?_toList]
  cases a[i]? <;> simp

theorem getD_toNats_of_lt (a : Array UInt32) (i : Nat) (h : i < a.size) :
    (toNats a).getD i 0 = (toNats a)[i]'(by rw [toNats_length]; exact h) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
  rfl

/-! ## The scratch relation -/

/-- The kernel's assignment bytes represent a model scratch on the declared
variables: every declared slot holds an encoded `Option Bool` (0, 1, or 2)
and the scratch is unassigned above the variable count. -/
def ScratchRel (variables : Nat) (s : Scratch) (a : Array UInt8) : Prop :=
  (∀ v, v < variables → (a.getD v 0).toNat = encode (s v)) ∧
  (∀ v, variables ≤ v → s v = none)

theorem literal_value_eq (n : UInt32) (fuel : Nat) :
    literal_value n fuel = some (UInt8.ofNat (encode (some (decodeLiteral n.toNat).positive))) := by
  unfold literal_value decodeLiteral encode
  simp only [pure]
  by_cases h : n % 2 = 1
  · have h' : n.toNat % 2 = 1 := by
      have := congrArg UInt32.toNat h
      rwa [UInt32.toNat_mod] at this
    simp [h, h']
  · have h' : ¬ n.toNat % 2 = 1 := by
      intro hm
      apply h
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_mod]
      exact hm
    simp [h, h']

theorem literal_false_value_eq (n : UInt32) (fuel : Nat) :
    literal_false_value n fuel = some (UInt8.ofNat (encode (some (!(decodeLiteral n.toNat).positive)))) := by
  unfold literal_false_value decodeLiteral encode
  simp only [pure]
  by_cases h : n % 2 = 1
  · have h' : n.toNat % 2 = 1 := by
      have := congrArg UInt32.toNat h
      rwa [UInt32.toNat_mod] at this
    simp [h, h']
  · have h' : ¬ n.toNat % 2 = 1 := by
      intro hm
      apply h
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_mod]
      exact hm
    simp [h, h']

theorem toNat_div2 (n : UInt32) : (n / 2).toNat = n.toNat / 2 := by
  rw [UInt32.toNat_div]
  rfl

/-! ## Small facts about the extracted operations -/

theorem getD_set8_ne (a : Array UInt8) (i j : Nat) (v : UInt8) (hij : j ≠ i) :
    (a.setIfInBounds i v).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, hij.symm]

theorem getD_set8_self (a : Array UInt8) (i : Nat) (v : UInt8) (hi : i < a.size) :
    (a.setIfInBounds i v).getD i 0 = v := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem size_set8 (a : Array UInt8) (i : Nat) (v : UInt8) : (a.setIfInBounds i v).size = a.size :=
  Array.size_setIfInBounds

theorem getD8_of_le (a : Array UInt8) (i : Nat) (h : a.size ≤ i) : a.getD i 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

theorem toNat_add32 (a b : UInt32) (h : a.toNat + b.toNat < UInt32.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem toNat_size32 (n : Nat) (h : n < UInt32.size) : n.toUInt32.toNat = n := by
  show (UInt32.ofNat n).toNat = n
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-! ## Clauses stored in the pool -/

/-- The literals of the clause stored at `start` with `count` elements. -/
def clauseAt (pool : Array UInt32) (start count : Nat) : List Nat :=
  ((toNats pool).drop start).take count

theorem clauseAt_length (pool : Array UInt32) (start count : Nat) (h : start + count ≤ pool.size) :
    (clauseAt pool start count).length = count := by
  simp only [clauseAt, List.length_take, List.length_drop, toNats_length]
  omega

theorem clauseAt_getElem (pool : Array UInt32) (start count j : Nat) (hj : j < count)
    (h : start + count ≤ pool.size) :
    (clauseAt pool start count)[j]'(by rw [clauseAt_length pool start count h]; exact hj) =
      (pool.getD (start + j) 0).toNat := by
  simp only [clauseAt, List.getElem_take, List.getElem_drop]
  rw [getD_toNats, getD_toNats_of_lt pool (start + j) (by omega)]

theorem readRange_clauseAt (pool : Array UInt32) (start count : Nat) (h : start + count ≤ pool.size) :
    readRange (toNats pool) start count = some (clauseAt pool start count) := by
  rw [readRange_refines, toNats_length, if_pos h]
  rfl

theorem readRange_none (pool : Array UInt32) (start count : Nat) (h : ¬ start + count ≤ pool.size) :
    readRange (toNats pool) start count = none := by
  rw [readRange_refines, toNats_length, if_neg h]

/-- The window of positions `k` to `j - 1` of a clause, one element at a time. -/
theorem window_cons (cl : List Nat) (k j : Nat) (hk : k < j) (hj : j ≤ cl.length) :
    (cl.drop k).take (j - k) = cl[k]'(by omega) :: (cl.drop (k + 1)).take (j - (k + 1)) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  have : j - k = (j - (k + 1)) + 1 := by omega
  rw [this, List.take_succ_cons]

/-! ## Loop 1: zeroing the scratch -/

/-- With the flag down every loop exits at once. -/
theorem rup_loop1_invalid (a : Array UInt8) (variables i : UInt32) (fuel : Nat) :
    rup_check.loop1 a variables false i (fuel + 1) = some (a, i) := by
  rw [rup_check.loop1]
  simp

theorem rup_loop1_spec (a : Array UInt8) (variables : UInt32) (hv : variables.toNat ≤ 64) :
    ∀ (fuel : Nat) (i : UInt32), i.toNat ≤ variables.toNat → variables.toNat - i.toNat < fuel →
      ∃ (a' : Array UInt8) (i' : UInt32), rup_check.loop1 a variables true i fuel = some (a', i') ∧
        a'.size = a.size ∧
        ∀ v, a'.getD v 0 = if i.toNat ≤ v ∧ v < variables.toNat then 0 else a.getD v 0 := by
  intro fuel
  induction fuel generalizing a with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro i hi hf
    rw [rup_check.loop1]
    by_cases hin : i.toNat < variables.toNat
    · have hlt : decide (i < variables) = true := (lt_iff_toNat i variables).mpr hin
      simp only [hlt, Bool.true_and, ite_true]
      have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ i (by omega)
      obtain ⟨a', i', hrun, hsize, hget⟩ := ih (a.setIfInBounds i.toNat 0) (i + 1) (by omega) (by omega)
      refine ⟨a', i', hrun, by rw [hsize, size_set8], ?_⟩
      intro v
      rw [hget v, hsucc]
      by_cases hvi : v = i.toNat
      · rw [hvi]
        by_cases hlt' : i.toNat < a.size
        · rw [getD_set8_self a i.toNat 0 hlt']
          simp [hin]
        · rw [getD8_of_le _ i.toNat (by rw [size_set8]; omega), getD8_of_le a i.toNat (by omega)]
          simp
      · rw [getD_set8_ne a i.toNat v 0 hvi]
        have hiff : (i.toNat + 1 ≤ v ∧ v < variables.toNat) ↔ (i.toNat ≤ v ∧ v < variables.toNat) := by omega
        simp only [hiff]
    · have hlt : decide (i < variables) = false := by
        have := lt_iff_toNat i variables
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      refine ⟨a, i, rfl, rfl, ?_⟩
      intro v
      have : ¬ (i.toNat ≤ v ∧ v < variables.toNat) := by omega
      simp [this]

/-! ## Loop 6: the duplicate scan -/

theorem rup_loop6_spec (pool : Array UInt32) (start count : UInt32) (hsc : start.toNat + count.toNat ≤ pool.size)
    (hpool : pool.size ≤ 4096) (lit j : UInt32) (hj : j.toNat ≤ count.toNat) :
    ∀ (fuel : Nat) (k : UInt32), k.toNat ≤ j.toNat → j.toNat - k.toNat < fuel →
      ∃ k' : UInt32, rup_check.loop6 pool true start j lit false k fuel =
        some (decide (lit.toNat ∈ ((clauseAt pool start.toNat count.toNat).drop k.toNat).take (j.toNat - k.toNat)), k') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro k hk hf
    rw [rup_check.loop6]
    by_cases hin : k.toNat < j.toNat
    · have hlt : decide (k < j) = true := (lt_iff_toNat k j).mpr hin
      simp only [hlt, Bool.not_false, Bool.and_true, ite_true]
      have hsucc : (k + 1).toNat = k.toNat + 1 := toNat_succ k (by omega)
      have hadd : (start + k).toNat = start.toNat + k.toNat := toNat_add32 start k (by
        show start.toNat + k.toNat < 4294967296
        omega)
      have hlen := clauseAt_length pool start.toNat count.toNat hsc
      have hwin : ((clauseAt pool start.toNat count.toNat).drop k.toNat).take (j.toNat - k.toNat) =
          (pool.getD (start + k).toNat 0).toNat ::
            ((clauseAt pool start.toNat count.toNat).drop (k.toNat + 1)).take (j.toNat - (k.toNat + 1)) := by
        rw [window_cons _ k.toNat j.toNat hin (by rw [hlen]; exact hj),
          clauseAt_getElem pool start.toNat count.toNat k.toNat (by omega) hsc, hadd]
      simp only [hwin, List.mem_cons]
      by_cases heq : pool.getD (start + k).toNat 0 = lit
      · have hb : (pool.getD (start + k).toNat 0 == lit) = true := beq_iff_eq.mpr heq
        simp only [hb]
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, rup_check.loop6]
        simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, pure]
        refine ⟨k + 1, ?_⟩
        simp only [heq, true_or, decide_true]
      · have hb : (pool.getD (start + k).toNat 0 == lit) = false := beq_eq_false_iff_ne.mpr heq
        simp only [hb]
        obtain ⟨k', hk'⟩ := ih (k + 1) (by omega) (by omega)
        rw [hsucc] at hk'
        refine ⟨k', ?_⟩
        rw [hk']
        have hne : ¬ lit.toNat = (pool.getD (start + k).toNat 0).toNat := fun h => heq (UInt32.toNat_inj.mp h).symm
        simp only [hne, false_or]
    · have hlt : decide (k < j) = false := by
        have := lt_iff_toNat k j
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      refine ⟨k, ?_⟩
      have : j.toNat - k.toNat = 0 := by omega
      simp [this]

/-! ## Loop 2: validating the hints -/

/-- The kernel's range check on a clause slot is the model's `rangeSafe`. -/
theorem range_check_eq (pool : Array UInt32) (hpool : pool.size ≤ 4096) (start count : UInt32) :
    (decide (start <= pool.size.toUInt32) && decide (count <= pool.size.toUInt32 - start)) =
      decide (rangeSafe start.toNat count.toNat pool.size) := by
  have hsz : pool.size.toUInt32.toNat = pool.size := toNat_size32 pool.size (by
    show pool.size < 4294967296
    omega)
  show _ = decide (start.toNat ≤ pool.size ∧ count.toNat ≤ pool.size - start.toNat)
  rw [Bool.decide_and, decide_le_toNat, decide_le_toNat, hsz]
  by_cases hs : start.toNat ≤ pool.size
  · rw [toNat_sub_of_le' _ _ (by rw [hsz]; exact hs), hsz]
  · simp [hs]

/-- Whether a hinted slot is below the clause count and stores a safe range. -/
def slotOK (pool starts lengths : Array UInt32) (clause_count : UInt32) (slot : UInt32) : Bool :=
  decide (slot.toNat < clause_count.toNat) &&
    decide (rangeSafe (starts.getD slot.toNat 0).toNat (lengths.getD slot.toNat 0).toNat pool.size)

theorem rup_loop2_invalid (pool starts lengths hints : Array UInt32) (clause_count hint_count i : UInt32) (fuel : Nat) :
    rup_check.loop2 pool starts lengths clause_count hints hint_count false i (fuel + 1) = some (false, i) := by
  rw [rup_check.loop2]
  simp

theorem rup_loop2_spec (pool starts lengths hints : Array UInt32) (hpool : pool.size ≤ 4096)
    (clause_count hint_count : UInt32) (hn : hint_count.toNat ≤ 256) :
    ∀ (fuel : Nat) (i : UInt32), i.toNat ≤ hint_count.toNat → hint_count.toNat - i.toNat < fuel →
      ∃ i' : UInt32, rup_check.loop2 pool starts lengths clause_count hints hint_count true i fuel =
        some ((List.range' i.toNat (hint_count.toNat - i.toNat)).all
          (fun h => slotOK pool starts lengths clause_count (hints.getD h 0)), i') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro i hi hf
    rw [rup_check.loop2]
    by_cases hin : i.toNat < hint_count.toNat
    · have hlt : decide (i < hint_count) = true := (lt_iff_toNat i hint_count).mpr hin
      simp only [hlt, Bool.and_true, ite_true]
      have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ i (by omega)
      have hrange : hint_count.toNat - i.toNat = (hint_count.toNat - (i.toNat + 1)) + 1 := by omega
      rw [hrange, List.range'_succ, List.all_cons]
      by_cases hslot : (hints.getD i.toNat 0).toNat < clause_count.toNat
      · have hd : decide (hints.getD i.toNat 0 < clause_count) = true := (lt_iff_toNat _ _).mpr hslot
        simp only [hd, ite_true, pure, bind, Option.bind, range_check_eq pool hpool]
        by_cases hsafe : rangeSafe (starts.getD (hints.getD i.toNat 0).toNat 0).toNat
            (lengths.getD (hints.getD i.toNat 0).toNat 0).toNat pool.size
        · rw [decide_eq_true hsafe]
          obtain ⟨i', hi'⟩ := ih (i + 1) (by omega) (by omega)
          rw [hsucc] at hi'
          refine ⟨i', ?_⟩
          rw [hi']
          have hok : slotOK pool starts lengths clause_count (hints.getD i.toNat 0) = true := by
            unfold slotOK
            rw [decide_eq_true hslot, decide_eq_true hsafe]
            rfl
          rw [hok, Bool.true_and]
        · rw [decide_eq_false hsafe]
          obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          rw [hfe, rup_loop2_invalid]
          refine ⟨i + 1, ?_⟩
          have hok : slotOK pool starts lengths clause_count (hints.getD i.toNat 0) = false := by
            unfold slotOK
            rw [decide_eq_false hsafe, Bool.and_false]
          rw [hok, Bool.false_and]
      · have hd : decide (hints.getD i.toNat 0 < clause_count) = false := by
          have := lt_iff_toNat (hints.getD i.toNat 0) clause_count
          exact Bool.eq_false_iff.mpr (fun h => hslot (this.mp h))
        simp only [hd, Bool.false_eq_true, ite_false, pure, bind, Option.bind]
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, rup_loop2_invalid]
        refine ⟨i + 1, ?_⟩
        have hok : slotOK pool starts lengths clause_count (hints.getD i.toNat 0) = false := by
          unfold slotOK
          rw [decide_eq_false hslot, Bool.false_and]
        rw [hok, Bool.false_and]
    · have hlt : decide (i < hint_count) = false := by
        have := lt_iff_toNat i hint_count
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      refine ⟨i, ?_⟩
      have : hint_count.toNat - i.toNat = 0 := by omega
      simp [this]

/-! ## The clause walk as a function on lists -/

/-- The kernel's walk over one clause: `seen` are the literals already
scanned (a repeated literal is skipped), `units` the unassigned literals
counted so far, newest first. It stops at the first satisfied literal. -/
def scan (s : Scratch) : List Nat → List Nat → List Nat → Bool × List Nat
  | [], _, units => (false, units)
  | n :: rest, seen, units =>
    if n ∈ seen then scan s rest (n :: seen) units
    else match s (n / 2) with
      | none => scan s rest (n :: seen) (n :: units)
      | some b => if b = decide (n % 2 = 1) then (true, units) else scan s rest (n :: seen) units

/-- A literal `n` of the pool is true under the scratch. -/
def TrueUnder (s : Scratch) (n : Nat) : Prop := s (n / 2) = some (decide (n % 2 = 1))

theorem scan_satisfied (s : Scratch) (l : List Nat) :
    ∀ (seen units : List Nat), (scan s l seen units).1 = true ↔ ∃ n ∈ l, n ∉ seen ∧ TrueUnder s n := by
  induction l with
  | nil => intro seen units; simp [scan]
  | cons n rest ih =>
    intro seen units
    simp only [scan]
    by_cases hseen : n ∈ seen
    · rw [if_pos hseen, ih]
      constructor
      · rintro ⟨m, hm, hns, ht⟩
        exact ⟨m, List.mem_cons_of_mem n hm, fun h => hns (List.mem_cons_of_mem n h), ht⟩
      · rintro ⟨m, hm, hns, ht⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd hseen hns
        · exact ⟨m, hm, fun h => by
            rcases List.mem_cons.mp h with rfl | h
            · exact hns hseen
            · exact hns h, ht⟩
    · rw [if_neg hseen]
      cases hv : s (n / 2) with
      | none =>
        simp only
        rw [ih]
        constructor
        · rintro ⟨m, hm, hns, ht⟩
          exact ⟨m, List.mem_cons_of_mem n hm, fun h => hns (List.mem_cons_of_mem n h), ht⟩
        · rintro ⟨m, hm, hns, ht⟩
          rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd (by unfold TrueUnder at ht; rw [hv] at ht; exact ht) (by simp)
          · refine ⟨m, hm, fun h => ?_, ht⟩
            rcases List.mem_cons.mp h with rfl | h
            · unfold TrueUnder at ht; rw [hv] at ht; cases ht
            · exact hns h
      | some b =>
        simp only
        by_cases hb : b = decide (n % 2 = 1)
        · rw [if_pos hb]
          simp only [true_iff]
          exact ⟨n, List.mem_cons_self, hseen, by unfold TrueUnder; rw [hv, hb]⟩
        · rw [if_neg hb, ih]
          constructor
          · rintro ⟨m, hm, hns, ht⟩
            exact ⟨m, List.mem_cons_of_mem n hm, fun h => hns (List.mem_cons_of_mem n h), ht⟩
          · rintro ⟨m, hm, hns, ht⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · exact absurd (by unfold TrueUnder at ht; rw [hv] at ht; exact Option.some_inj.mp ht) hb
            · refine ⟨m, hm, fun h => ?_, ht⟩
              rcases List.mem_cons.mp h with rfl | h
              · unfold TrueUnder at ht; rw [hv] at ht; exact hb (Option.some_inj.mp ht)
              · exact hns h

theorem scan_units_mem (s : Scratch) (l : List Nat) :
    ∀ (seen units : List Nat), (scan s l seen units).1 = false →
      ∀ m, m ∈ (scan s l seen units).2 ↔ m ∈ units ∨ (m ∈ l ∧ m ∉ seen ∧ s (m / 2) = none) := by
  induction l with
  | nil => intro seen units _ m; simp [scan]
  | cons n rest ih =>
    intro seen units hns m
    simp only [scan] at hns ⊢
    by_cases hseen : n ∈ seen
    · rw [if_pos hseen] at hns ⊢
      rw [ih _ _ hns]
      constructor
      · rintro (h | ⟨hm, hs, hv⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem n hm, fun h => hs (List.mem_cons_of_mem n h), hv⟩
      · rintro (h | ⟨hm, hs, hv⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd hseen hs
          · refine Or.inr ⟨hm, fun h => ?_, hv⟩
            rcases List.mem_cons.mp h with rfl | h
            · exact hs hseen
            · exact hs h
    · rw [if_neg hseen] at hns ⊢
      cases hv : s (n / 2) with
      | none =>
        rw [hv] at hns
        simp only at hns ⊢
        rw [ih _ _ hns, List.mem_cons]
        constructor
        · rintro ((rfl | h) | ⟨hm, hs, hv'⟩)
          · exact Or.inr ⟨List.mem_cons_self, hseen, hv⟩
          · exact Or.inl h
          · exact Or.inr ⟨List.mem_cons_of_mem n hm, fun h => hs (List.mem_cons_of_mem n h), hv'⟩
        · rintro (h | ⟨hm, hs, hv'⟩)
          · exact Or.inl (Or.inr h)
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact Or.inl (Or.inl rfl)
            · by_cases hmn : m = n
              · exact Or.inl (Or.inl hmn)
              · exact Or.inr ⟨hm, fun h => by
                  rcases List.mem_cons.mp h with h | h
                  · exact hmn h
                  · exact hs h, hv'⟩
      | some b =>
        rw [hv] at hns
        simp only at hns ⊢
        by_cases hb : b = decide (n % 2 = 1)
        · rw [if_pos hb] at hns
          cases hns
        · rw [if_neg hb] at hns ⊢
          rw [ih _ _ hns]
          constructor
          · rintro (h | ⟨hm, hs, hv'⟩)
            · exact Or.inl h
            · exact Or.inr ⟨List.mem_cons_of_mem n hm, fun h => hs (List.mem_cons_of_mem n h), hv'⟩
          · rintro (h | ⟨hm, hs, hv'⟩)
            · exact Or.inl h
            · rcases List.mem_cons.mp hm with rfl | hm
              · rw [hv] at hv'; cases hv'
              · refine Or.inr ⟨hm, fun h => ?_, hv'⟩
                rcases List.mem_cons.mp h with rfl | h
                · rw [hv] at hv'; cases hv'
                · exact hs h

theorem scan_units_nodup (s : Scratch) (l : List Nat) :
    ∀ (seen units : List Nat), units.Nodup → (∀ m ∈ units, m ∈ seen) →
      (scan s l seen units).2.Nodup := by
  induction l with
  | nil => intro seen units hn _; simpa [scan] using hn
  | cons n rest ih =>
    intro seen units hn hsub
    simp only [scan]
    by_cases hseen : n ∈ seen
    · rw [if_pos hseen]
      exact ih _ _ hn (fun m hm => List.mem_cons_of_mem n (hsub m hm))
    · rw [if_neg hseen]
      cases hv : s (n / 2) with
      | none =>
        simp only
        apply ih _ _ (List.nodup_cons.mpr ⟨fun h => hseen (hsub n h), hn⟩)
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem n (hsub m hm)
      | some b =>
        simp only
        by_cases hb : b = decide (n % 2 = 1)
        · rw [if_pos hb]; exact hn
        · rw [if_neg hb]
          exact ih _ _ hn (fun m hm => List.mem_cons_of_mem n (hsub m hm))

theorem scan_seen_congr (s : Scratch) (l : List Nat) :
    ∀ (seen seen' units : List Nat), (∀ m, m ∈ seen ↔ m ∈ seen') →
      scan s l seen units = scan s l seen' units := by
  induction l with
  | nil => intro _ _ _ _; rfl
  | cons n rest ih =>
    intro seen seen' units hiff
    simp only [scan]
    have hcons : ∀ m, m ∈ n :: seen ↔ m ∈ n :: seen' := by
      intro m
      simp only [List.mem_cons, hiff]
    by_cases hseen : n ∈ seen
    · rw [if_pos hseen, if_pos ((hiff n).mp hseen)]
      exact ih _ _ _ hcons
    · rw [if_neg hseen, if_neg (fun h => hseen ((hiff n).mpr h))]
      cases s (n / 2) with
      | none => exact ih _ _ _ hcons
      | some b =>
        simp only
        by_cases hb : b = decide (n % 2 = 1)
        · rw [if_pos hb, if_pos hb]
        · rw [if_neg hb, if_neg hb]
          exact ih _ _ _ hcons

/-! ## The walk decides the classifier -/

theorem unique_nodup (c : Clause) : (ClauseClassifier.unique c).Nodup := by
  induction c with
  | nil => simp [ClauseClassifier.unique]
  | cons l rest ih =>
    by_cases h : l ∈ rest
    · simp only [ClauseClassifier.unique, if_pos h]
      exact ih
    · simp only [ClauseClassifier.unique, if_neg h]
      exact List.nodup_cons.mpr ⟨fun hm => h ((ClauseClassifier.mem_unique l rest).mp hm), ih⟩

theorem decodeLiteral_injective : Function.Injective decodeLiteral := by
  intro a b h
  have := congrArg encodeLiteral h
  rwa [Ranges.encode_decode, Ranges.encode_decode] at this

theorem nodup_map_inj {α β : Type} (f : α → β) (hf : Function.Injective f) :
    ∀ l : List α, l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a rest ih =>
    intro h
    obtain ⟨ha, hrest⟩ := List.nodup_cons.mp h
    rw [List.map_cons]
    apply List.nodup_cons.mpr
    refine ⟨fun hm => ?_, ih hrest⟩
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hm
    exact ha (hf hab ▸ hb)

theorem survivors_nodup (s : Scratch) (c : Clause) : (ClauseClassifier.survivors s c).Nodup :=
  unique_nodup _

theorem dec_index (n : Nat) : (decodeLiteral n).index - 1 = n / 2 := by
  simp [decodeLiteral]

theorem dec_positive (n : Nat) : (decodeLiteral n).positive = decide (n % 2 = 1) := rfl

theorem any_true_iff (s : Scratch) (cl : List Nat) :
    (cl.map decodeLiteral).any (fun l => decide (s (l.index - 1) = some l.positive)) = true ↔
      ∃ n ∈ cl, TrueUnder s n := by
  rw [List.any_map, List.any_eq_true]
  simp only [Function.comp, dec_index, dec_positive, decide_eq_true_eq]
  rfl

theorem survivors_mem_unsat (s : Scratch) (cl : List Nat) (hns : ¬ ∃ n ∈ cl, TrueUnder s n) (l : Literal) :
    l ∈ ClauseClassifier.survivors s (cl.map decodeLiteral) ↔ ∃ n ∈ cl, decodeLiteral n = l ∧ s (n / 2) = none := by
  rw [ClauseClassifier.mem_survivors, List.mem_map]
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, hnf⟩
    refine ⟨n, hn, rfl, ?_⟩
    unfold FalseUnder at hnf
    rw [dec_index, dec_positive] at hnf
    cases hv : s (n / 2) with
    | none => rfl
    | some b =>
      exfalso
      by_cases hb : b = decide (n % 2 = 1)
      · exact hns ⟨n, hn, by unfold TrueUnder; rw [hv, hb]⟩
      · apply hnf
        rw [hv]
        congr
        cases b <;> cases hd : decide (n % 2 = 1) <;> simp_all
  · rintro ⟨n, hn, rfl, hv⟩
    refine ⟨⟨n, hn, rfl⟩, ?_⟩
    unfold FalseUnder
    rw [dec_index, hv]
    simp

theorem classify_of_scan (s : Scratch) (cl : List Nat) :
    ((scan s cl [] []).1 = true →
      ClauseClassifier.classify s (cl.map decodeLiteral) = .satisfied) ∧
    ((scan s cl [] []).1 = false → (scan s cl [] []).2 = [] →
      ClauseClassifier.classify s (cl.map decodeLiteral) = .conflict) ∧
    ((scan s cl [] []).1 = false → ∀ n, (scan s cl [] []).2 = [n] →
      ClauseClassifier.classify s (cl.map decodeLiteral) = .unit (decodeLiteral n)) ∧
    ((scan s cl [] []).1 = false → 2 ≤ (scan s cl [] []).2.length →
      ClauseClassifier.classify s (cl.map decodeLiteral) = .unresolved) := by
  have hsat := scan_satisfied s cl [] []
  simp only [List.not_mem_nil, not_false_eq_true, true_and] at hsat
  refine ⟨?_, ?_⟩
  · intro h
    have hany := (any_true_iff s cl).mpr (hsat.mp h)
    unfold ClauseClassifier.classify
    rw [if_pos hany]
  · -- The unsatisfied case: the survivors are the counted literals, decoded.
    have key : (scan s cl [] []).1 = false →
        (ClauseClassifier.survivors s (cl.map decodeLiteral)).Perm ((scan s cl [] []).2.map decodeLiteral) := by
      intro h
      have hns : ¬ ∃ n ∈ cl, TrueUnder s n := fun hx => by
        have := hsat.mpr hx
        rw [h] at this
        cases this
      apply (List.perm_ext_iff_of_nodup (survivors_nodup s (cl.map decodeLiteral))
        (nodup_map_inj decodeLiteral decodeLiteral_injective _
          (scan_units_nodup s cl [] [] List.nodup_nil (by simp)))).mpr
      intro u
      rw [survivors_mem_unsat s cl hns u, List.mem_map]
      constructor
      · rintro ⟨n, hn, rfl, hv⟩
        exact ⟨n, (scan_units_mem s cl [] [] h n).mpr (Or.inr ⟨hn, by simp, hv⟩), rfl⟩
      · rintro ⟨n, hmem, rfl⟩
        rcases (scan_units_mem s cl [] [] h n).mp hmem with hnil | ⟨hn, _, hv⟩
        · cases hnil
        · exact ⟨n, hn, rfl, hv⟩
    have hany : (scan s cl [] []).1 = false →
        (cl.map decodeLiteral).any (fun l => decide (s (l.index - 1) = some l.positive)) = false := by
      intro h
      apply Bool.eq_false_iff.mpr
      intro hx
      have := hsat.mpr ((any_true_iff s cl).mp hx)
      rw [h] at this
      cases this
    refine ⟨?_, ?_, ?_⟩
    · intro h hnil
      have hperm := key h
      rw [hnil] at hperm
      have hsurv : ClauseClassifier.survivors s (cl.map decodeLiteral) = [] :=
        List.Perm.eq_nil (by simpa using hperm)
      unfold ClauseClassifier.classify
      rw [if_neg (by rw [hany h]; exact Bool.false_ne_true), hsurv]
    · intro h n hone
      have hperm := key h
      rw [hone] at hperm
      have hsurv : ClauseClassifier.survivors s (cl.map decodeLiteral) = [decodeLiteral n] :=
        List.Perm.eq_singleton (by simpa using hperm)
      unfold ClauseClassifier.classify
      rw [if_neg (by rw [hany h]; exact Bool.false_ne_true), hsurv]
    · intro h hlen
      have hperm := key h
      have hlen' : 2 ≤ (ClauseClassifier.survivors s (cl.map decodeLiteral)).length := by
        rw [hperm.length_eq, List.length_map]
        exact hlen
      unfold ClauseClassifier.classify
      rw [if_neg (by rw [hany h]; exact Bool.false_ne_true)]
      cases hs : ClauseClassifier.survivors s (cl.map decodeLiteral) with
      | nil => rw [hs] at hlen'; simp at hlen'
      | cons u rest =>
        cases rest with
        | nil => rw [hs] at hlen'; simp at hlen'
        | cons w tail => rfl

/-! ## Loop 5: the clause walk -/

theorem toNat_encode_le (v : Option Bool) : encode v ≤ 2 := by
  cases v with
  | none => decide
  | some b => cases b <;> decide

theorem ofNat8_encode (v : Option Bool) : (UInt8.ofNat (encode v)).toNat = encode v :=
  UInt8.toNat_ofNat_of_lt (by
    have := toNat_encode_le v
    show encode v < 256
    omega)

/-- The scratch byte of a declared variable, compared with zero and with a
literal's encoding. -/
theorem byte_zero_iff (a : Array UInt8) (v : Nat) (s : Scratch) (variables : Nat)
    (hrel : ScratchRel variables s a) (hv : v < variables) :
    ((a.getD v 0 == 0) = true ↔ s v = none) := by
  rw [beq_toNat8, decide_eq_true_eq, hrel.1 v hv]
  cases s v with
  | none => simp [encode]
  | some b => cases b <;> simp [encode]

theorem byte_eq_encode_iff (a : Array UInt8) (v : Nat) (s : Scratch) (variables : Nat)
    (hrel : ScratchRel variables s a) (hv : v < variables) (w : Option Bool) :
    ((a.getD v 0 == UInt8.ofNat (encode w)) = true ↔ s v = w) := by
  rw [beq_toNat8, decide_eq_true_eq, hrel.1 v hv, ofNat8_encode]
  constructor
  · intro h
    have := congrArg decode h
    rwa [PropagationState.decode_encode, PropagationState.decode_encode] at this
  · intro h
    rw [h]

theorem take_succ_mem (cl : List Nat) (j : Nat) (hj : j < cl.length) (m : Nat) :
    m ∈ cl.take (j + 1) ↔ m ∈ cl[j]'hj :: cl.take j := by
  rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton, List.mem_cons]
  exact or_comm

theorem rup_loop5_spec (pool : Array UInt32) (a : Array UInt8) (variables : UInt32) (s : Scratch)
    (hrel : ScratchRel variables.toNat s a) (start count : UInt32)
    (hsc : start.toNat + count.toNat ≤ pool.size) (hpool : pool.size ≤ 4096)
    (hbound : ∀ n ∈ clauseAt pool start.toNat count.toNat, n / 2 < variables.toNat) :
    ∀ (fuel : Nat) (j remaining unit : UInt32) (units : List Nat), j.toNat ≤ count.toNat →
      2 * count.toNat - j.toNat < fuel →
      remaining.toNat = units.length → (∀ n, units.head? = some n → unit.toNat = n) →
      units.length ≤ j.toNat →
      ∃ (remaining' unit' j' : UInt32),
        rup_check.loop5 pool a variables true start count false remaining unit j fuel =
          some (true, (scan s ((clauseAt pool start.toNat count.toNat).drop j.toNat)
            ((clauseAt pool start.toNat count.toNat).take j.toNat) units).1, remaining', unit', j') ∧
        remaining'.toNat = (scan s ((clauseAt pool start.toNat count.toNat).drop j.toNat)
            ((clauseAt pool start.toNat count.toNat).take j.toNat) units).2.length ∧
        (∀ n, (scan s ((clauseAt pool start.toNat count.toNat).drop j.toNat)
            ((clauseAt pool start.toNat count.toNat).take j.toNat) units).2.head? = some n → unit'.toNat = n) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro j remaining unit units hj hf hrem hunit hlen
    have hcl := clauseAt_length pool start.toNat count.toNat hsc
    rw [rup_check.loop5]
    by_cases hin : j.toNat < count.toNat
    · have hlt : decide (j < count) = true := (lt_iff_toNat j count).mpr hin
      simp only [hlt, Bool.and_true, Bool.not_false, ite_true]
      have hsucc : (j + 1).toNat = j.toNat + 1 := toNat_succ j (by omega)
      have hadd : (start + j).toNat = start.toNat + j.toNat := toNat_add32 start j (by
        show start.toNat + j.toNat < 4294967296
        omega)
      have hjl : j.toNat < (clauseAt pool start.toNat count.toNat).length := by rw [hcl]; exact hin
      have helem : (clauseAt pool start.toNat count.toNat)[j.toNat]'hjl = (pool.getD (start + j).toNat 0).toNat := by
        rw [clauseAt_getElem pool start.toNat count.toNat j.toNat hin hsc, hadd]
      have hdrop : (clauseAt pool start.toNat count.toNat).drop j.toNat =
          (pool.getD (start + j).toNat 0).toNat :: (clauseAt pool start.toNat count.toNat).drop (j.toNat + 1) := by
        rw [List.drop_eq_getElem_cons hjl, helem]
      have hmem : (pool.getD (start + j).toNat 0).toNat ∈ clauseAt pool start.toNat count.toNat := by
        rw [← helem]; exact List.getElem_mem hjl
      have hvar : (pool.getD (start + j).toNat 0).toNat / 2 < variables.toNat := hbound _ hmem
      have hvalid : decide (pool.getD (start + j).toNat 0 / 2 < variables) = true := by
        rw [decide_lt_toNat, toNat_div2]
        exact decide_eq_true hvar
      simp only [hvalid]
      -- The duplicate scan over the literals before position j.
      obtain ⟨k', hk'⟩ := rup_loop6_spec pool start count hsc hpool (pool.getD (start + j).toNat 0) j hj fuel 0
        (by simp) (by simp; omega)
      simp only [UInt32.toNat_zero, List.drop_zero, Nat.sub_zero] at hk'
      rw [hk']
      simp only [bind, Option.bind, Bool.true_and]
      -- The seen set after this position, as the model writes it.
      have hseen : ∀ units', scan s ((clauseAt pool start.toNat count.toNat).drop (j.toNat + 1))
          ((pool.getD (start + j).toNat 0).toNat :: (clauseAt pool start.toNat count.toNat).take j.toNat) units' =
          scan s ((clauseAt pool start.toNat count.toNat).drop (j.toNat + 1))
          ((clauseAt pool start.toNat count.toNat).take (j.toNat + 1)) units' := by
        intro units'
        apply scan_seen_congr
        intro m
        rw [take_succ_mem _ j.toNat hjl m, helem]
      rw [hdrop]
      simp only [scan]
      by_cases hdup : (pool.getD (start + j).toNat 0).toNat ∈ (clauseAt pool start.toNat count.toNat).take j.toNat
      · rw [decide_eq_true hdup, if_pos hdup]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, pure]
        obtain ⟨r', u', j', hrun, hr, hu⟩ := ih (j + 1) remaining unit units (by omega) (by omega) hrem hunit (by omega)
        rw [hsucc, ← hseen] at hrun hr hu
        exact ⟨r', u', j', hrun, hr, hu⟩
      · rw [decide_eq_false hdup, if_neg hdup]
        simp only [Bool.not_false, ite_true, literal_value_eq, pure]
        rw [toNat_div2]
        cases hv : s ((pool.getD (start + j).toNat 0).toNat / 2) with
        | none =>
          have hz : (a.getD ((pool.getD (start + j).toNat 0).toNat / 2) 0 == 0) = true :=
            (byte_zero_iff a _ s variables.toNat hrel hvar).mpr hv
          have hnz : (a.getD ((pool.getD (start + j).toNat 0).toNat / 2) 0 != 0) = false := by
            rw [bne, hz]; rfl
          simp only [hnz, Bool.false_and, hz, ite_true]
          have hrem' : (remaining + 1).toNat = ((pool.getD (start + j).toNat 0).toNat :: units).length := by
            rw [toNat_succ remaining (by rw [hrem]; omega), hrem]
            rfl
          obtain ⟨r', u', j', hrun, hr, hu⟩ := ih (j + 1) (remaining + 1) (pool.getD (start + j).toNat 0)
            ((pool.getD (start + j).toNat 0).toNat :: units) (by omega) (by omega) hrem'
            (fun n hn => by rw [List.head?_cons, Option.some_inj] at hn; exact hn) (by simp; omega)
          rw [hsucc, ← hseen] at hrun hr hu
          exact ⟨r', u', j', hrun, hr, hu⟩
        | some b =>
          have hnz' : (a.getD ((pool.getD (start + j).toNat 0).toNat / 2) 0 == 0) = false := by
            apply Bool.eq_false_iff.mpr
            intro h
            have := (byte_zero_iff a _ s variables.toNat hrel hvar).mp h
            rw [hv] at this
            cases this
          have hnz : (a.getD ((pool.getD (start + j).toNat 0).toNat / 2) 0 != 0) = true := by
            rw [bne, hnz']; rfl
          simp only [hnz, Bool.true_and, hnz', Bool.false_eq_true, ite_false]
          by_cases hb : b = decide ((pool.getD (start + j).toNat 0).toNat % 2 = 1)
          · have hsat : (a.getD ((pool.getD (start + j).toNat 0).toNat / 2) 0 ==
                UInt8.ofNat (encode (some (decodeLiteral (pool.getD (start + j).toNat 0).toNat).positive))) = true := by
              rw [byte_eq_encode_iff a _ s variables.toNat hrel hvar, hv, dec_positive, hb]
            simp only [hsat, if_pos hb]
            obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [hfe, rup_check.loop5]
            simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, pure]
            exact ⟨remaining, unit, j + 1, rfl, hrem, hunit⟩
          · have hsat : (a.getD ((pool.getD (start + j).toNat 0).toNat / 2) 0 ==
                UInt8.ofNat (encode (some (decodeLiteral (pool.getD (start + j).toNat 0).toNat).positive))) = false := by
              apply Bool.eq_false_iff.mpr
              intro h
              have := (byte_eq_encode_iff a _ s variables.toNat hrel hvar _).mp h
              rw [hv, dec_positive] at this
              exact hb (Option.some_inj.mp this)
            simp only [hsat, if_neg hb]
            obtain ⟨r', u', j', hrun, hr, hu⟩ := ih (j + 1) remaining unit units (by omega) (by omega) hrem hunit (by omega)
            rw [hsucc, ← hseen] at hrun hr hu
            exact ⟨r', u', j', hrun, hr, hu⟩
    · have hlt : decide (j < count) = false := by
        have := lt_iff_toNat j count
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      have hnil : (clauseAt pool start.toNat count.toNat).drop j.toNat = [] :=
        List.drop_eq_nil_of_le (by rw [hcl]; omega)
      rw [hnil]
      exact ⟨remaining, unit, j, rfl, hrem, hunit⟩

/-! ## Loop 3: assuming the negated target -/

instance (s : Scratch) (n : Nat) : Decidable (TrueUnder s n) :=
  inferInstanceAs (Decidable (s (n / 2) = some (decide (n % 2 = 1))))

/-- The kernel's target walk on lists: each literal's negation is written
unless the literal itself already holds, which is the contradiction. -/
def assume (s : Scratch) : List Nat → Bool × Scratch
  | [] => (false, s)
  | n :: rest =>
    if TrueUnder s n then (true, s)
    else assume (write s (n / 2) (!decide (n % 2 = 1))) rest

theorem write_self (s : Scratch) (v : Nat) (b : Bool) (h : s v = some b) : write s v b = s := by
  funext key
  by_cases hk : key = v
  · subst hk; simp [write, h]
  · simp [write, hk]

theorem negate_dec_index (n : Nat) : (negate (decodeLiteral n)).index - 1 = n / 2 := by
  simp [negate, decodeLiteral]

theorem negate_dec_pos (n : Nat) : 0 < (negate (decodeLiteral n)).index := by
  simp [negate, decodeLiteral]

theorem negate_dec_positive (n : Nat) : (negate (decodeLiteral n)).positive = !decide (n % 2 = 1) := rfl

theorem falseUnder_negate_iff (s : Scratch) (n : Nat) :
    FalseUnder s (negate (decodeLiteral n)) ↔ TrueUnder s n := by
  unfold FalseUnder TrueUnder
  rw [negate_dec_index, negate_dec_positive, Bool.not_not]

/-- `prepare` on the decoded, negated target never fails, clashes exactly when
the walk does, and otherwise hands over the walk's scratch. -/
theorem prepare_spec (cl : List Nat) :
    ∀ s : Scratch,
      ((assume s cl).1 = true ∧ ∃ h, PropagationChain.prepare s ((cl.map decodeLiteral).map negate) = some (.clash h)) ∨
      ((assume s cl).1 = false ∧ ∃ h, PropagationChain.prepare s ((cl.map decodeLiteral).map negate) =
        some (.ready (assume s cl).2 h)) := by
  induction cl with
  | nil =>
    intro s
    right
    exact ⟨rfl, _, rfl⟩
  | cons n rest ih =>
    intro s
    show ((if TrueUnder s n then (true, s) else assume (write s (n / 2) (!decide (n % 2 = 1))) rest).1 = true ∧
        ∃ h, PropagationChain.prepare s (negate (decodeLiteral n) :: (rest.map decodeLiteral).map negate) =
          some (.clash h)) ∨
      ((if TrueUnder s n then (true, s) else assume (write s (n / 2) (!decide (n % 2 = 1))) rest).1 = false ∧
        ∃ h, PropagationChain.prepare s (negate (decodeLiteral n) :: (rest.map decodeLiteral).map negate) =
          some (.ready (if TrueUnder s n then (true, s) else assume (write s (n / 2) (!decide (n % 2 = 1))) rest).2 h))
    rw [PropagationChain.prepare, dif_pos (negate_dec_pos n)]
    by_cases ht : TrueUnder s n
    · left
      rw [dif_pos ((falseUnder_negate_iff s n).mpr ht), if_pos ht]
      exact ⟨rfl, _, rfl⟩
    · rw [dif_neg (fun h => ht ((falseUnder_negate_iff s n).mp h)), if_neg ht]
      have hw : write s (n / 2) (!decide (n % 2 = 1)) =
          write s ((negate (decodeLiteral n)).index - 1) (negate (decodeLiteral n)).positive := by
        rw [negate_dec_index, negate_dec_positive]
      rw [hw]
      rcases ih (write s ((negate (decodeLiteral n)).index - 1) (negate (decodeLiteral n)).positive)
        with ⟨hc, h, hp⟩ | ⟨hc, h, hp⟩
      · left
        rw [hp]
        exact ⟨hc, _, rfl⟩
      · right
        rw [hp]
        exact ⟨hc, _, rfl⟩

/-- The target literals the kernel reads. -/
def targetList (target : Array UInt32) (count : Nat) : List Nat := (toNats target).take count

theorem targetList_length (target : Array UInt32) (count : Nat) (h : count ≤ target.size) :
    (targetList target count).length = count := by
  simp only [targetList, List.length_take, toNats_length]
  omega

theorem targetList_drop (target : Array UInt32) (count i : Nat) (hi : i < count) (h : count ≤ target.size) :
    (targetList target count).drop i = (target.getD i 0).toNat :: (targetList target count).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [targetList_length target count h]; exact hi)]
  congr 1
  simp only [targetList, List.getElem_take]
  rw [getD_toNats, getD_toNats_of_lt target i (by omega)]

theorem scratchRel_write (variables : Nat) (s : Scratch) (a : Array UInt8) (hrel : ScratchRel variables s a)
    (hsize : variables ≤ a.size) (v : Nat) (hv : v < variables) (b : Bool) :
    ScratchRel variables (write s v b) (a.setIfInBounds v (UInt8.ofNat (encode (some b)))) := by
  constructor
  · intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [getD_set8_self a w _ (by omega), ofNat8_encode]
      simp [write]
    · rw [getD_set8_ne a v w _ hwv, hrel.1 w hw]
      simp [write, hwv]
  · intro w hw
    have : w ≠ v := by omega
    simp only [write, if_neg this]
    exact hrel.2 w hw

theorem rup_loop3_invalid (target : Array UInt32) (target_count : UInt32) (a : Array UInt8) (variables i : UInt32)
    (contradictory : Bool) (fuel : Nat) :
    rup_check.loop3 target target_count a variables false i contradictory (fuel + 1) = some (a, false, i, contradictory) := by
  rw [rup_check.loop3]
  simp

theorem rup_loop3_spec (target : Array UInt32) (target_count variables : UInt32)
    (htc : target_count.toNat ≤ target.size) (htsize : target.size ≤ 4096)
    (hbound : ∀ n ∈ targetList target target_count.toNat, n / 2 < variables.toNat) :
    ∀ (fuel : Nat) (i : UInt32) (s : Scratch) (a : Array UInt8), ScratchRel variables.toNat s a →
      variables.toNat ≤ a.size → i.toNat ≤ target_count.toNat → target_count.toNat - i.toNat < fuel →
      ∃ (a' : Array UInt8) (i' : UInt32),
        rup_check.loop3 target target_count a variables true i false fuel =
          some (a', true, i', (assume s ((targetList target target_count.toNat).drop i.toNat)).1) ∧
        a'.size = a.size ∧
        ScratchRel variables.toNat (assume s ((targetList target target_count.toNat).drop i.toNat)).2 a' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro i s a hrel hsize hi hf
    rw [rup_check.loop3]
    by_cases hin : i.toNat < target_count.toNat
    · have hlt : decide (i < target_count) = true := (lt_iff_toNat i target_count).mpr hin
      simp only [hlt, Bool.and_true, Bool.not_false, ite_true]
      have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ i (by omega)
      have hdrop := targetList_drop target target_count.toNat i.toNat hin htc
      have hmem : (target.getD i.toNat 0).toNat ∈ targetList target target_count.toNat := by
        have : (target.getD i.toNat 0).toNat ∈ (targetList target target_count.toNat).drop i.toNat := by
          rw [hdrop]; exact List.mem_cons_self
        exact List.mem_of_mem_drop this
      have hvar : (target.getD i.toNat 0).toNat / 2 < variables.toNat := hbound _ hmem
      have hvalid : decide (target.getD i.toNat 0 / 2 < variables) = true := by
        rw [decide_lt_toNat, toNat_div2]
        exact decide_eq_true hvar
      simp only [hvalid, ite_true, literal_false_value_eq, pure, bind, Option.bind]
      rw [toNat_div2, hdrop]
      simp only [assume]
      cases hv : s ((target.getD i.toNat 0).toNat / 2) with
      | none =>
        have hnt : ¬ TrueUnder s (target.getD i.toNat 0).toNat := by
          unfold TrueUnder; rw [hv]; simp
        rw [if_neg hnt]
        have hz : (a.getD ((target.getD i.toNat 0).toNat / 2) 0 == 0) = true :=
          (byte_zero_iff a _ s variables.toNat hrel hvar).mpr hv
        have hnz : (a.getD ((target.getD i.toNat 0).toNat / 2) 0 != 0) = false := by
          rw [bne, hz]; rfl
        simp only [hnz, Bool.false_and, hz, ite_true]
        obtain ⟨a', i', hrun, hsz, hrel'⟩ := ih (i + 1) (write s ((target.getD i.toNat 0).toNat / 2)
          (!decide ((target.getD i.toNat 0).toNat % 2 = 1)))
          (a.setIfInBounds ((target.getD i.toNat 0).toNat / 2)
            (UInt8.ofNat (encode (some (!(decodeLiteral (target.getD i.toNat 0).toNat).positive)))))
          (by rw [dec_positive]; exact scratchRel_write variables.toNat s a hrel hsize _ hvar _)
          (by rw [size_set8]; exact hsize) (by omega) (by omega)
        rw [hsucc] at hrun hrel'
        exact ⟨a', i', hrun, by rw [hsz, size_set8], hrel'⟩
      | some b =>
        have hnz' : (a.getD ((target.getD i.toNat 0).toNat / 2) 0 == 0) = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          have := (byte_zero_iff a _ s variables.toNat hrel hvar).mp h
          rw [hv] at this
          cases this
        have hnz : (a.getD ((target.getD i.toNat 0).toNat / 2) 0 != 0) = true := by
          rw [bne, hnz']; rfl
        simp only [hnz, Bool.true_and, hnz', Bool.false_eq_true, ite_false]
        by_cases hb : b = decide ((target.getD i.toNat 0).toNat % 2 = 1)
        · -- The literal already holds: a contradiction, and the loop stops.
          have ht : TrueUnder s (target.getD i.toNat 0).toNat := by
            unfold TrueUnder; rw [hv, hb]
          rw [if_pos ht]
          have hne : (a.getD ((target.getD i.toNat 0).toNat / 2) 0 !=
              UInt8.ofNat (encode (some (!(decodeLiteral (target.getD i.toNat 0).toNat).positive)))) = true := by
            rw [bne_iff_ne]
            intro h
            have := (byte_eq_encode_iff a _ s variables.toNat hrel hvar _).mp (beq_iff_eq.mpr h)
            rw [hv, dec_positive, hb] at this
            have := Option.some_inj.mp this
            cases hd : decide ((target.getD i.toNat 0).toNat % 2 = 1) <;> rw [hd] at this <;> cases this
          simp only [hne]
          obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          rw [hfe, rup_check.loop3]
          simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, pure]
          exact ⟨a, i + 1, rfl, rfl, hrel⟩
        · have hnt : ¬ TrueUnder s (target.getD i.toNat 0).toNat := by
            unfold TrueUnder; rw [hv]; intro h; exact hb (Option.some_inj.mp h)
          rw [if_neg hnt]
          have hbv : b = !decide ((target.getD i.toNat 0).toNat % 2 = 1) := by
            cases b <;> cases hd : decide ((target.getD i.toNat 0).toNat % 2 = 1) <;> simp_all
          have heq : (a.getD ((target.getD i.toNat 0).toNat / 2) 0 !=
              UInt8.ofNat (encode (some (!(decodeLiteral (target.getD i.toNat 0).toNat).positive)))) = false := by
            rw [bne_eq_false_iff_eq]
            apply beq_iff_eq.mp
            rw [byte_eq_encode_iff a _ s variables.toNat hrel hvar, hv, dec_positive, hbv]
          simp only [heq]
          have hw : write s ((target.getD i.toNat 0).toNat / 2) (!decide ((target.getD i.toNat 0).toNat % 2 = 1)) = s :=
            write_self s _ _ (by rw [hv, hbv])
          rw [hw]
          obtain ⟨a', i', hrun, hsz, hrel'⟩ := ih (i + 1) s a hrel hsize (by omega) (by omega)
          rw [hsucc] at hrun hrel'
          exact ⟨a', i', hrun, hsz, hrel'⟩
    · have hlt : decide (i < target_count) = false := by
        have := lt_iff_toNat i target_count
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      have hnil : (targetList target target_count.toNat).drop i.toNat = [] :=
        List.drop_eq_nil_of_le (by rw [targetList_length target target_count.toNat htc]; omega)
      rw [hnil]
      exact ⟨a, i, rfl, rfl, hrel⟩

/-! ## Loop 4: the hint chain -/

/-- The chain's acceptance as a Boolean function: the same case analysis as
`PropagationChain.chain`, without the certificates. -/
def walk (variables : Nat) (db : Database) : Scratch → List Nat → Bool
  | _, [] => false
  | s, id :: rest =>
    if id = 0 then false
    else match db id with
      | none => false
      | some clause =>
        if ∀ l ∈ clause, 0 < l.index ∧ l.index ≤ variables then
          match ClauseClassifier.classify s clause with
          | .conflict => decide (rest = [])
          | .unit u => walk variables db (write s (u.index - 1) u.positive) rest
          | _ => false
        else false

theorem chain_walk (variables : Nat) (db : Database) (hints : List Nat) :
    ∀ s : Scratch, (PropagationChain.chain variables db s hints).isSome = walk variables db s hints := by
  induction hints with
  | nil => intro s; rfl
  | cons id rest ih =>
    intro s
    rw [PropagationChain.chain, walk]
    by_cases hid : id = 0
    · simp [hid]
    · rw [if_neg hid, if_neg hid]
      split
      · rename_i hdb
        rw [hdb]
        rfl
      · rename_i clause hdb
        simp only [hdb]
        by_cases hb : ∀ l ∈ clause, 0 < l.index ∧ l.index ≤ variables
        · rw [dif_pos hb, if_pos hb]
          split
          · rename_i hc
            simp only [hc]
            cases rest with
            | nil => rfl
            | cons x xs => rfl
          · rename_i u hc
            simp only [hc]
            rw [← ih (write s (u.index - 1) u.positive)]
            cases PropagationChain.chain variables db (write s (u.index - 1) u.positive) rest <;> rfl
          · rename_i hnc hnu
            cases hc : ClauseClassifier.classify s clause with
            | conflict => exact absurd hc hnc
            | unit u => exact absurd hc (hnu u)
            | satisfied => rfl
            | unresolved => rfl
        · rw [dif_neg hb, if_neg hb]
          rfl

/-- The hint slots the kernel reads. -/
def hintList (hints : Array UInt32) (count : Nat) : List Nat := (toNats hints).take count

theorem hintList_length (hints : Array UInt32) (count : Nat) (h : count ≤ hints.size) :
    (hintList hints count).length = count := by
  simp only [hintList, List.length_take, toNats_length]
  omega

theorem hintList_drop (hints : Array UInt32) (count i : Nat) (hi : i < count) (h : count ≤ hints.size) :
    (hintList hints count).drop i = (hints.getD i 0).toNat :: (hintList hints count).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [hintList_length hints count h]; exact hi)]
  congr 1
  simp only [hintList, List.getElem_take]
  rw [getD_toNats, getD_toNats_of_lt hints i (by omega)]

/-- The kernel's live tables represent a model table on the 256 slots. -/
def TableRel (t : LiveTable.Table) (starts lengths : Array UInt32) (live : Array Bool) : Prop :=
  ∀ slot, slot < 256 → t slot = ⟨(starts.getD slot 0).toNat, (lengths.getD slot 0).toNat, live.getD slot false⟩

theorem clauseAt_mem_bound (pool : Array UInt32) (start count : Nat) (P : Nat → Prop)
    (hp : ∀ i, i < pool.size → P (pool.getD i 0).toNat) : ∀ n ∈ clauseAt pool start count, P n := by
  intro n hn
  have hn' : n ∈ toNats pool := List.mem_of_mem_drop (List.mem_of_mem_take hn)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hn'
  rw [toNats_length] at hi
  rw [← getD_toNats_of_lt pool i hi, ← getD_toNats]
  exact hp i hi

theorem database_slot (pool : Array UInt32) (t : LiveTable.Table) (starts lengths : Array UInt32) (live : Array Bool)
    (htable : TableRel t starts lengths live) (slot : Nat) (hs : slot < 256) (hl : live.getD slot false = true)
    (hsafe : (starts.getD slot 0).toNat + (lengths.getD slot 0).toNat ≤ pool.size) :
    LiveTable.database (toNats pool) t (slot + 1) =
      some ((clauseAt pool (starts.getD slot 0).toNat (lengths.getD slot 0).toNat).map decodeLiteral) := by
  unfold LiveTable.database
  rw [if_neg (Nat.succ_ne_zero slot), Nat.add_sub_cancel, htable slot hs]
  unfold LiveTable.meaning
  simp only [hl, ite_true]
  unfold readClause
  rw [readRange_clauseAt pool _ _ hsafe]
  rfl

theorem rup_loop4_spec (pool starts lengths hints : Array UInt32) (hint_count variables : UInt32)
    (t : LiveTable.Table) (live : Array Bool)
    (hpool : pool.size ≤ 4096) (hpvars : ∀ i, i < pool.size → (pool.getD i 0).toNat / 2 < variables.toNat)
    (hhc : hint_count.toNat ≤ hints.size) (hn : hint_count.toNat ≤ 256)
    (htable : TableRel t starts lengths live)
    (hlive : ∀ i, i < hint_count.toNat → (hints.getD i 0).toNat < 256 ∧ live.getD (hints.getD i 0).toNat false = true)
    (hok : ∀ i, i < hint_count.toNat → slotOK pool starts lengths 256 (hints.getD i 0) = true) :
    ∀ (fuel : Nat) (h : UInt32) (s : Scratch) (a : Array UInt8), ScratchRel variables.toNat s a →
      variables.toNat ≤ a.size → h.toNat ≤ hint_count.toNat →
      8192 + 2 * (hint_count.toNat - h.toNat) + 2 < fuel →
      ∃ (a' : Array UInt8) (valid' conflict' : Bool) (h' : UInt32),
        rup_check.loop4 pool starts lengths hints hint_count a variables true false false h fuel =
          some (a', valid', conflict', h') ∧ a'.size = a.size ∧
        (valid' && conflict') = walk variables.toNat (LiveTable.database (toNats pool) t) s
          (((hintList hints hint_count.toNat).drop h.toNat).map (· + 1)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro h s a hrel hsize hh hf
    rw [rup_check.loop4]
    by_cases hin : h.toNat < hint_count.toNat
    · have hlt : decide (h < hint_count) = true := (lt_iff_toNat h hint_count).mpr hin
      simp only [hlt, Bool.and_true, Bool.not_false, ite_true]
      have hsucc : (h + 1).toNat = h.toNat + 1 := toNat_succ h (by omega)
      -- The hinted slot and its clause.
      obtain ⟨hslot, hl⟩ := hlive h.toNat hin
      have hok' := hok h.toNat hin
      unfold slotOK at hok'
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, rangeSafe_refines] at hok'
      obtain ⟨_, hsafe⟩ := hok'
      have hdb := database_slot pool t starts lengths live htable (hints.getD h.toNat 0).toNat hslot hl hsafe
      have hdrop := hintList_drop hints hint_count.toNat h.toNat hin hhc
      rw [hdrop, List.map_cons, walk, if_neg (Nat.succ_ne_zero _)]
      simp only [hdb]
      have hbound : ∀ n ∈ clauseAt pool (starts.getD (hints.getD h.toNat 0).toNat 0).toNat
          (lengths.getD (hints.getD h.toNat 0).toNat 0).toNat, n / 2 < variables.toNat :=
        clauseAt_mem_bound pool _ _ (fun n => n / 2 < variables.toNat) hpvars
      have hlb : ∀ l ∈ (clauseAt pool (starts.getD (hints.getD h.toNat 0).toNat 0).toNat
          (lengths.getD (hints.getD h.toNat 0).toNat 0).toNat).map decodeLiteral,
          0 < l.index ∧ l.index ≤ variables.toNat := by
        intro l hl
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hl
        exact decoded_bounds n variables.toNat (hbound n hn)
      rw [if_pos hlb]
      -- The clause walk.
      obtain ⟨r', u', j', hrun5, hr, hu⟩ := rup_loop5_spec pool a variables s hrel
        (starts.getD (hints.getD h.toNat 0).toNat 0) (lengths.getD (hints.getD h.toNat 0).toNat 0)
        hsafe hpool hbound fuel 0 0 0 [] (Nat.zero_le _) (by rw [UInt32.toNat_zero]; omega) rfl
        (fun n hn => by cases hn) (Nat.zero_le _)
      simp only [UInt32.toNat_zero, List.drop_zero, List.take_zero] at hrun5 hr hu
      rw [hrun5]
      simp only [bind, Option.bind, Bool.true_and]
      obtain ⟨hcs, hcc, hcu, hcr⟩ := classify_of_scan s (clauseAt pool
        (starts.getD (hints.getD h.toNat 0).toNat 0).toNat (lengths.getD (hints.getD h.toNat 0).toNat 0).toNat)
      cases hsat : (scan s (clauseAt pool (starts.getD (hints.getD h.toNat 0).toNat 0).toNat
          (lengths.getD (hints.getD h.toNat 0).toNat 0).toNat) [] []).1 with
      | true =>
        -- Satisfied: the kernel drops the flag and the next iteration exits.
        rw [hcs hsat]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, pure]
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, rup_check.loop4]
        simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, ite_false, pure]
        exact ⟨a, false, false, h + 1, rfl, rfl, rfl⟩
      | false =>
        simp only [Bool.not_false, ite_true]
        rw [beq_ofNat32 r' 0 (by decide), beq_ofNat32 r' 1 (by decide), hr]
        cases hunits : (scan s (clauseAt pool (starts.getD (hints.getD h.toNat 0).toNat 0).toNat
            (lengths.getD (hints.getD h.toNat 0).toNat 0).toNat) [] []).2 with
        | nil =>
          rw [hcc hsat hunits]
          simp only [List.length_nil, beq_self_eq_true, ite_true, pure]
          rw [beq_toNat32, hsucc]
          by_cases hlast : h.toNat + 1 = hint_count.toNat
          · rw [decide_eq_true hlast]
            obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [hfe, rup_check.loop4]
            simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, pure]
            refine ⟨a, true, true, h + 1, rfl, rfl, ?_⟩
            have hnil : (hintList hints hint_count.toNat).drop (h.toNat + 1) = [] :=
              List.drop_eq_nil_of_le (by rw [hintList_length hints hint_count.toNat hhc]; omega)
            rw [hnil]
            rfl
          · rw [decide_eq_false hlast]
            obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [hfe, rup_check.loop4]
            simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, ite_false, pure]
            refine ⟨a, false, false, h + 1, rfl, rfl, ?_⟩
            have hne : (hintList hints hint_count.toNat).drop (h.toNat + 1) ≠ [] := by
              intro hnil
              have := congrArg List.length hnil
              rw [List.length_drop, hintList_length hints hint_count.toNat hhc] at this
              simp at this
              omega
            rw [decide_eq_false (fun hm => hne (List.map_eq_nil_iff.mp hm))]
            rfl
        | cons n tail =>
          cases tail with
          | nil =>
            rw [hcu hsat n hunits]
            simp only [List.length_singleton, beq_self_eq_true, ite_true, literal_value_eq, pure]
            have hun : u'.toNat = n := hu n (by rw [hunits]; rfl)
            have hnmem : n ∈ clauseAt pool (starts.getD (hints.getD h.toNat 0).toNat 0).toNat
                (lengths.getD (hints.getD h.toNat 0).toNat 0).toNat := by
              have := (scan_units_mem s _ [] [] hsat n).mp (by rw [hunits]; exact List.mem_cons_self)
              rcases this with hx | ⟨hx, _, _⟩
              · cases hx
              · exact hx
            have hnv : n / 2 < variables.toNat := hbound n hnmem
            rw [toNat_div2, hun, dec_index]
            have hrel' := scratchRel_write variables.toNat s a hrel hsize (n / 2) hnv (decodeLiteral n).positive
            obtain ⟨a', v', c', h', hrun, hsz, hw⟩ := ih (h + 1) (write s (n / 2) (decodeLiteral n).positive)
              (a.setIfInBounds (n / 2) (UInt8.ofNat (encode (some (decodeLiteral n).positive)))) hrel'
              (by rw [size_set8]; exact hsize) (by omega) (by omega)
            rw [hsucc] at hw
            exact ⟨a', v', c', h', hrun, by rw [hsz, size_set8], hw⟩
          | cons m rest =>
            rw [hcr hsat (by rw [hunits]; simp)]
            have h0 : ((n :: m :: rest).length == 0) = false := by simp
            have h1 : ((n :: m :: rest).length == 1) = false := by simp
            simp only [h0, h1, Bool.false_eq_true, ite_false, pure]
            obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [hfe, rup_check.loop4]
            simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, ite_false, pure]
            exact ⟨a, false, false, h + 1, rfl, rfl, rfl⟩
    · have hlt : decide (h < hint_count) = false := by
        have := lt_iff_toNat h hint_count
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      have hnil : (hintList hints hint_count.toNat).drop h.toNat = [] :=
        List.drop_eq_nil_of_le (by rw [hintList_length hints hint_count.toNat hhc]; omega)
      rw [hnil]
      exact ⟨a, true, false, h, rfl, rfl, rfl⟩

/-! ## The kernel -/

theorem rup_loop4_invalid (pool starts lengths hints : Array UInt32) (hint_count : UInt32) (a : Array UInt8)
    (variables : UInt32) (contradictory conflict : Bool) (h : UInt32) (fuel : Nat) :
    rup_check.loop4 pool starts lengths hints hint_count a variables false contradictory conflict h (fuel + 1) =
      some (a, false, conflict, h) := by
  rw [rup_check.loop4]
  simp

theorem rup_loop4_contradictory (pool starts lengths hints : Array UInt32) (hint_count : UInt32) (a : Array UInt8)
    (variables : UInt32) (valid conflict : Bool) (h : UInt32) (fuel : Nat) :
    rup_check.loop4 pool starts lengths hints hint_count a variables valid true conflict h (fuel + 1) =
      some (a, valid, conflict, h) := by
  rw [rup_check.loop4]
  simp

/-- On a live slot below 256, the kernel's slot check is the model's lookup. -/
theorem slotOK_db (pool starts lengths : Array UInt32) (t : LiveTable.Table) (live : Array Bool)
    (htable : TableRel t starts lengths live) (slot : UInt32) (hs : slot.toNat < 256)
    (hl : live.getD slot.toNat false = true) :
    slotOK pool starts lengths 256 slot = (LiveTable.database (toNats pool) t (slot.toNat + 1)).isSome := by
  unfold slotOK LiveTable.database
  rw [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, htable slot.toNat hs]
  unfold LiveTable.meaning
  simp only [hl, ite_true]
  unfold readClause
  have h256 : (256 : UInt32).toNat = 256 := by decide
  rw [h256, decide_eq_true hs, Bool.true_and]
  by_cases hsafe : rangeSafe (starts.getD slot.toNat 0).toNat (lengths.getD slot.toNat 0).toNat pool.size
  · rw [decide_eq_true hsafe, readRange_clauseAt pool _ _ ((rangeSafe_refines _ _ _).mp hsafe)]
    rfl
  · rw [decide_eq_false hsafe, readRange_none pool _ _ (fun h => hsafe ((rangeSafe_refines _ _ _).mpr h))]
    rfl

theorem mem_hintList (hints : Array UInt32) (n : Nat) (hn : n ≤ hints.size) (x : Nat) :
    x ∈ hintList hints n ↔ ∃ h, h < n ∧ x = (hints.getD h 0).toNat := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [hintList_length hints n hn] at hh
    refine ⟨h, hh, ?_⟩
    simp only [hintList, List.getElem_take]
    rw [getD_toNats, getD_toNats_of_lt hints h (by omega)]
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h, by rw [hintList_length hints n hn]; exact hh, ?_⟩
    simp only [hintList, List.getElem_take]
    rw [getD_toNats, getD_toNats_of_lt hints h (by omega)]

/-- The hint validation loop decides the model's hint guard. -/
theorem hints_all_eq (pool starts lengths hints : Array UInt32) (hint_count : UInt32) (t : LiveTable.Table)
    (live : Array Bool) (htable : TableRel t starts lengths live) (hhints : hint_count.toNat ≤ hints.size)
    (hlive : ∀ i, i < hint_count.toNat → (hints.getD i 0).toNat < 256 ∧ live.getD (hints.getD i 0).toNat false = true) :
    (List.range' 0 hint_count.toNat).all (fun h => slotOK pool starts lengths 256 (hints.getD h 0)) =
      ((hintList hints hint_count.toNat).map (· + 1)).all
        (fun id => decide (0 < id) && (LiveTable.database (toNats pool) t id).isSome) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro hall id hid
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hid
    obtain ⟨h, hh, rfl⟩ := (mem_hintList hints _ hhints x).mp hx
    obtain ⟨hs, hl⟩ := hlive h hh
    have := hall h (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
    rw [slotOK_db pool starts lengths t live htable _ hs hl] at this
    rw [this]
    simp
  · intro hall h hh
    have hh' : h < hint_count.toNat := by
      have := List.mem_range'_1.mp hh
      omega
    obtain ⟨hs, hl⟩ := hlive h hh'
    rw [slotOK_db pool starts lengths t live htable _ hs hl]
    have := hall ((hints.getD h 0).toNat + 1) (List.mem_map.mpr ⟨_, (mem_hintList hints _ hhints _).mpr ⟨h, hh', rfl⟩, rfl⟩)
    exact (Bool.and_eq_true _ _).mp this |>.2

theorem target_all (target : Array UInt32) (count variables : Nat)
    (hvars : ∀ n ∈ targetList target count, n / 2 < variables) :
    ((targetList target count).map decodeLiteral).all (fun l => decide (0 < l.index ∧ l.index ≤ variables)) = true := by
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hl
  exact decide_eq_true (decoded_bounds n variables (hvars n hn))

theorem check_isSome_chain (variables : Nat) (db : Database) (target : Clause) (hints : List Nat)
    (s : Scratch) (h : ∀ a, Extends a (fun _ => none) → Assigned a (target.map negate) → Extends a s)
    (hv : ¬ (variables = 0 ∨ 64 < variables))
    (ht : target.all (fun l => decide (0 < l.index ∧ l.index ≤ variables)) = true)
    (hh : (hints.all fun id => decide (0 < id) && (db id).isSome) = true)
    (hp : PropagationChain.prepare (fun _ => none) (target.map negate) = some (.ready s h)) :
    (PropagationChain.check variables db target hints).isSome = (PropagationChain.chain variables db s hints).isSome := by
  unfold PropagationChain.check
  rw [if_neg hv, if_neg (by rw [ht]; exact not_not_intro rfl), hh]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, hp]
  cases PropagationChain.chain variables db s hints <;> rfl

theorem check_isSome_clash (variables : Nat) (db : Database) (target : Clause) (hints : List Nat)
    (h : ∀ a, Extends a (fun _ => none) → ¬ Assigned a (target.map negate))
    (hv : ¬ (variables = 0 ∨ 64 < variables))
    (ht : target.all (fun l => decide (0 < l.index ∧ l.index ≤ variables)) = true)
    (hh : (hints.all fun id => decide (0 < id) && (db id).isSome) = true)
    (hp : PropagationChain.prepare (fun _ => none) (target.map negate) = some (.clash h)) :
    (PropagationChain.check variables db target hints).isSome = true := by
  unfold PropagationChain.check
  rw [if_neg hv, if_neg (by rw [ht]; exact not_not_intro rfl), hh]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, hp]
  rfl

theorem check_isSome_hints (variables : Nat) (db : Database) (target : Clause) (hints : List Nat)
    (hh : (hints.all fun id => decide (0 < id) && (db id).isSome) = false) :
    (PropagationChain.check variables db target hints).isSome = false := by
  unfold PropagationChain.check
  rw [hh]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem check_isSome_variables (variables : Nat) (db : Database) (target : Clause) (hints : List Nat)
    (hv : variables = 0 ∨ 64 < variables) :
    (PropagationChain.check variables db target hints).isSome = false := by
  unfold PropagationChain.check
  rw [if_pos hv]
  rfl

/-- The RUP kernel theorem: on the inputs the stream checker hands it, the
extracted `rup_check` accepts exactly when `PropagationChain.check` produces
a certificate for the decoded target under the live table's database. -/
theorem rup_check_spec (pool starts lengths target hints : Array UInt32) (assignments : Array UInt8)
    (target_count hint_count variables : UInt32) (t : LiveTable.Table) (live : Array Bool) (fuel : Nat)
    (hpool : pool.size ≤ 4096) (hpvars : ∀ i, i < pool.size → (pool.getD i 0).toNat / 2 < variables.toNat)
    (hstarts : starts.size = 256) (hlengths : lengths.size = 256) (hassign : assignments.size = 64)
    (htarget : target_count.toNat ≤ target.size) (htsize : target.size ≤ 4096)
    (htvars : ∀ n ∈ targetList target target_count.toNat, n / 2 < variables.toNat)
    (hhints : hint_count.toNat ≤ hints.size) (hhsize : hints.size ≤ 4096) (hn : hint_count.toNat ≤ 256)
    (hlive : ∀ i, i < hint_count.toNat → (hints.getD i 0).toNat < 256 ∧ live.getD (hints.getD i 0).toNat false = true)
    (htable : TableRel t starts lengths live) (hfuel : 8800 < fuel) :
    ∃ a' : Array UInt8,
      rup_check pool starts lengths 256 target target_count hints hint_count assignments variables fuel =
        some ((PropagationChain.check variables.toNat (LiveTable.database (toNats pool) t)
          ((targetList target target_count.toNat).map decodeLiteral)
          ((hintList hints hint_count.toNat).map (· + 1))).isSome, a') ∧ a'.size = assignments.size := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  unfold rup_check
  -- The entry guards other than the variable bound all hold.
  have h256 : (256 : UInt32).toNat = 256 := by decide
  have h64 : (64 : UInt32).toNat = 64 := by decide
  have hg1 : decide ((256 : UInt32) <= starts.size.toUInt32) = true := by
    rw [hstarts]; decide
  have hg2 : decide ((256 : UInt32) <= lengths.size.toUInt32) = true := by
    rw [hlengths]; decide
  have hg3 : decide (target_count <= target.size.toUInt32) = true := by
    rw [decide_le_toNat, toNat_size32 target.size (by show target.size < 4294967296; omega)]
    exact decide_eq_true htarget
  have hg4 : decide (hint_count <= hints.size.toUInt32) = true := by
    rw [decide_le_toNat, toNat_size32 hints.size (by show hints.size < 4294967296; omega)]
    exact decide_eq_true hhints
  have hg5 : decide (variables <= assignments.size.toUInt32) = decide (variables.toNat ≤ 64) := by
    rw [hassign, decide_le_toNat, toNat_size32 64 (by decide)]
  have hg0 : decide (variables > (0 : UInt32)) = decide (0 < variables.toNat) := by
    show decide ((0 : UInt32) < variables) = _
    rw [decide_lt_toNat, UInt32.toNat_zero]
  have hg6 : decide (variables <= (64 : UInt32)) = decide (variables.toNat ≤ 64) := by
    rw [decide_le_toNat, h64]
  simp only [hg1, hg2, hg3, hg4, hg5, hg0, hg6, Bool.and_true]
  by_cases hv : 0 < variables.toNat ∧ variables.toNat ≤ 64
  · obtain ⟨hv0, hv64⟩ := hv
    simp only [decide_eq_true hv0, decide_eq_true hv64, Bool.and_self]
    -- Loop 1 zeroes the declared variables.
    obtain ⟨a1, i1, hrun1, hsize1, hget1⟩ := rup_loop1_spec assignments variables hv64 (f + 1) 0 (Nat.zero_le _)
      (by rw [UInt32.toNat_zero]; omega)
    rw [hrun1]
    simp only [bind, Option.bind]
    have hrel1 : ScratchRel variables.toNat (fun _ => none) a1 := by
      constructor
      · intro v hvv
        rw [hget1 v]
        simp [hvv, encode]
      · intro _ _
        rfl
    -- Loop 2 validates the hints.
    obtain ⟨i2, hrun2⟩ := rup_loop2_spec pool starts lengths hints hpool 256 hint_count hn (f + 1) 0
      (Nat.zero_le _) (by rw [UInt32.toNat_zero]; omega)
    rw [UInt32.toNat_zero, Nat.sub_zero] at hrun2
    rw [hrun2]
    simp only
    rw [hints_all_eq pool starts lengths hints hint_count t live htable hhints hlive]
    have hnv : ¬ (variables.toNat = 0 ∨ 64 < variables.toNat) := by omega
    have hta := target_all target target_count.toNat variables.toNat htvars
    cases hall : ((hintList hints hint_count.toNat).map (· + 1)).all
        (fun id => decide (0 < id) && (LiveTable.database (toNats pool) t id).isSome) with
    | false =>
      rw [rup_loop3_invalid]
      simp only
      rw [rup_loop4_invalid]
      simp only [Bool.false_and, pure]
      exact ⟨a1, by rw [check_isSome_hints _ _ _ _ hall], hsize1⟩
    | true =>
      -- Loop 3 assumes the negated target.
      obtain ⟨a3, i3, hrun3, hsize3, hrel3⟩ := rup_loop3_spec target target_count variables htarget htsize htvars
        (f + 1) 0 (fun _ => none) a1 hrel1 (by rw [hsize1, hassign]; exact hv64) (Nat.zero_le _)
        (by rw [UInt32.toNat_zero]; omega)
      rw [UInt32.toNat_zero, List.drop_zero] at hrun3 hrel3
      rw [hrun3]
      simp only
      rcases prepare_spec (targetList target target_count.toNat) (fun _ => none) with ⟨hc, hp, hpre⟩ | ⟨hc, hp, hpre⟩
      · -- A contradiction among the assumptions: the chain is never walked.
        rw [hc, rup_loop4_contradictory]
        simp only [Bool.true_or, Bool.and_true, pure]
        exact ⟨a3, by rw [check_isSome_clash _ _ _ _ hp hnv hta hall hpre], by rw [hsize3, hsize1]⟩
      · rw [hc]
        obtain ⟨a4, v4, c4, h4, hrun4, hsize4, hwalk⟩ := rup_loop4_spec pool starts lengths hints hint_count variables t live
          hpool hpvars hhints hn htable hlive
          (fun i hi => by
            have := List.all_eq_true.mp hall ((hints.getD i 0).toNat + 1)
              (List.mem_map.mpr ⟨_, (mem_hintList hints _ hhints _).mpr ⟨i, hi, rfl⟩, rfl⟩)
            rw [slotOK_db pool starts lengths t live htable _ (hlive i hi).1 (hlive i hi).2]
            exact ((Bool.and_eq_true _ _).mp this).2)
          (f + 1) 0 _ a3 hrel3 (by rw [hsize3, hsize1, hassign]; exact hv64) (Nat.zero_le _)
          (by rw [UInt32.toNat_zero]; omega)
        rw [UInt32.toNat_zero, List.drop_zero] at hwalk
        rw [hrun4]
        simp only [Bool.false_or, pure]
        refine ⟨a4, ?_, by rw [hsize4, hsize3, hsize1]⟩
        rw [hwalk, ← chain_walk, check_isSome_chain _ _ _ _ _ hp hnv hta hall hpre]
  · -- Outside the variable bound every loop exits at once.
    have hfalse : (decide (0 < variables.toNat) && decide (variables.toNat ≤ 64)) = false := by
      rcases Bool.eq_false_or_eq_true (decide (0 < variables.toNat) && decide (variables.toNat ≤ 64)) with h | h
      · exfalso
        apply hv
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
        exact h
      · exact h
    rw [hfalse, Bool.false_and, rup_loop1_invalid]
    simp only [bind, Option.bind]
    rw [rup_loop2_invalid]
    simp only
    rw [rup_loop3_invalid]
    simp only
    rw [rup_loop4_invalid]
    simp only [Bool.false_and, pure]
    exact ⟨assignments, by rw [check_isSome_variables _ _ _ _ (by omega)], rfl⟩

#print axioms rup_check_spec
end OakVerification.Extraction
