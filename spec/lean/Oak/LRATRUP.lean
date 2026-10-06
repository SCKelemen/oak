import Oak.LRATRUPExtracted

/-!
Implementation-linked state lemmas for the production RUP checker. Extraction
of `lrat_rup` and all its callees is pinned by `TestLRATKernelRUPExtract`.
This module proves the actual rollback loop, including its machine counter,
and its exact effect on scratch. Propagation soundness and the complete parser
refinement remain separate obligations; extraction alone is not that proof.
-/

namespace Oak.LRATRUP

def clearList (assign : Array UInt8) (indices : List Nat) : Array UInt8 :=
  indices.foldl (fun a v => a.setIfInBounds v 0) assign

def trailIndices (trail : Array UInt32) (start count : Nat) : List Nat :=
  (List.range' start count).map (fun k => (trail.getD k 0).toNat)

theorem counter_succ (i used : UInt32) (h : i < used) :
    (i + 1).toNat = i.toNat + 1 := by
  have := used.toNat_lt
  rw [UInt32.lt_iff_toNat_lt] at h
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt (by change i.toNat + 1 < 4294967296; omega)

/-- The extracted loop clears precisely the remaining trail interval. Fuel
is needed only for termination; the counter cannot wrap before `used`. -/
theorem undo_loop_spec (fuel : Nat) (assign : Array UInt8) (trail : Array UInt32)
    (used i : UInt32) (hi : i ≤ used) (hf : used.toNat - i.toNat < fuel) :
    lrat_undo.loop1 assign trail used i fuel =
      some (clearList assign (trailIndices trail i.toNat (used.toNat - i.toNat)), used) := by
  induction fuel generalizing assign i with
  | zero => omega
  | succ fuel ih =>
    rw [lrat_undo.loop1]
    by_cases h : i < used
    · simp only [decide_eq_true h, ite_true, Option.pure_def]
      have hs := counter_succ i used h
      have hn : i.toNat < used.toNat := (UInt32.lt_iff_toNat_lt).mp h
      have he : used.toNat - i.toNat = (used.toNat - (i + 1).toNat) + 1 := by omega
      rw [ih _ (i + 1) (by rw [UInt32.le_iff_toNat_le, hs]; omega) (by omega)]
      rw [he]
      simp only [trailIndices, List.range'_succ, List.map_cons,
        clearList, List.foldl_cons, LRAT_UNASSIGNED, hs]
    · have he : i = used := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.le_iff_toNat_le] at hi
        rw [UInt32.lt_iff_toNat_lt] at h
        omega
      subst i
      simp [h, clearList, trailIndices]

theorem clearList_size (assign : Array UInt8) (indices : List Nat) :
    (clearList assign indices).size = assign.size := by
  induction indices generalizing assign with
  | nil => rfl
  | cons v rest ih =>
    exact (ih (assign.setIfInBounds v 0)).trans Array.size_setIfInBounds

theorem set_getD (assign : Array UInt8) (at_ v : Nat) (value : UInt8)
    (hv : v < assign.size) :
    (assign.setIfInBounds at_ value).getD v 0 =
      if at_ = v then value else assign.getD v 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : at_ = v
  · subst at_
    simp [hv]
  · simp [h]

/-- Rollback clears even repeated trail entries and preserves every other
assignment. The result's size is unchanged. -/
theorem clearList_getD (assign : Array UInt8) (indices : List Nat)
    (v : Nat) (hv : v < assign.size) :
    (clearList assign indices).getD v 0 =
      if v ∈ indices then 0 else assign.getD v 0 := by
  induction indices generalizing assign with
  | nil => simp [clearList]
  | cons at_ rest ih =>
    change (clearList (assign.setIfInBounds at_ 0) rest).getD v 0 = _
    rw [ih _ (by simpa using hv), set_getD assign at_ v 0 hv]
    by_cases ha : at_ = v <;> by_cases hr : v ∈ rest <;> simp_all [eq_comm]

/-- The caller's trail invariant justifies every read and write made by the
rollback loop. `counter_succ` connects these natural indices to its counter. -/
theorem undo_accesses_safe (assign : Array UInt8) (trail : Array UInt32) (used : UInt32)
    (ht : used.toNat ≤ trail.size)
    (ha : ∀ k, k < used.toNat → (trail.getD k 0).toNat < assign.size) :
    ∀ k, k < used.toNat → k < trail.size ∧ (trail.getD k 0).toNat < assign.size := by
  intro k hk
  exact ⟨by omega, ha k hk⟩

/-- `lrat_undo` returns the original trail and clears exactly its used prefix
in the extracted semantics. Memory-access safety is `undo_accesses_safe`. -/
theorem undo_spec (assign : Array UInt8) (trail : Array UInt32) (used : UInt32)
    (fuel : Nat) (hf : used.toNat < fuel) :
    ∃ result, lrat_undo assign trail used fuel = some ((), result, trail) ∧
      result.size = assign.size ∧
      ∀ v, v < assign.size → result.getD v 0 =
        if v ∈ trailIndices trail 0 used.toNat then 0 else assign.getD v 0 := by
  refine ⟨clearList assign (trailIndices trail 0 used.toNat), ?_, clearList_size _ _, ?_⟩
  · simp only [lrat_undo,
      undo_loop_spec fuel assign trail used 0 (by simp) (by simpa using hf)]
    rfl
  · exact clearList_getD assign (trailIndices trail 0 used.toNat)

/-- If every nonzero assignment is tracked, rollback restores all-zero
scratch, the required starting state of the next RUP call. -/
theorem undo_restores_zero (assign : Array UInt8) (trail : Array UInt32) (used : UInt32)
    (fuel : Nat) (hf : used.toNat < fuel)
    (tracked : ∀ v, v < assign.size → assign.getD v 0 ≠ 0 →
      v ∈ trailIndices trail 0 used.toNat) :
    ∃ result, lrat_undo assign trail used fuel = some ((), result, trail) ∧
      result.size = assign.size ∧ ∀ v, v < result.size → result.getD v 0 = 0 := by
  obtain ⟨result, run, size, values⟩ := undo_spec assign trail used fuel hf
  refine ⟨result, run, size, ?_⟩
  intro v hv
  rw [size] at hv
  rw [values v hv]
  split
  · rfl
  · rename_i absent
    by_cases hz : assign.getD v 0 = 0
    · exact (Array.getElem_eq_getD (xs := assign) (i := v) (h := hv) 0).trans hz
    · exact False.elim (absent (tracked v hv hz))

end Oak.LRATRUP
