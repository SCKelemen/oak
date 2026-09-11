import ExtractionRUP

set_option autoImplicit false
namespace OakVerification.Extraction
open Ranges Extracted PropagationState CertifiedStream Decimal

/-! The extracted stream checker refines the certified stream
(docs/spec/95-extraction.md, roadmap step 3's fourth increment, second
half). `rup_stream_check` is what the compiler extracts from
`self_hosted_stream.oak`: the resource guards, the literal check, the
initial table, and the command loop with its hint mapping, clause copy,
kernel call, publication, and deletions. `CertifiedStream.check` is the
proof-producing model whose acceptance is unsatisfiability
(`check_sound`). This file proves that on every layout the extracted
decoder can hand over (`LayoutRel`), the extracted stream checker returns
exactly the model's decision. -/

/-! ## The model's initial state -/

theorem findEmpty_isSome (db : Database) (ids : List Nat) :
    (findEmpty db ids).isSome = ids.any (fun id => decide (db id = some [])) := by
  induction ids with
  | nil => rfl
  | cons id rest ih =>
    simp only [findEmpty, List.any_cons]
    by_cases h : db id = some []
    · rw [dif_pos h, decide_eq_true h]
      rfl
    · rw [dif_neg h, decide_eq_false h, Bool.false_or, ih]

theorem initialState_fields (raw : Layout) :
    (CertifiedStream.initialState raw).table = LiveTable.initialTable (raw.starts.zip raw.sizes) ∧
    (CertifiedStream.initialState raw).last = raw.starts.length ∧
    (CertifiedStream.initialState raw).refuted =
      ((List.range raw.starts.length).map (· + 1)).any (fun id => decide (origin raw id = some [])) := by
  rw [← findEmpty_isSome]
  unfold CertifiedStream.initialState
  split
  · rename_i h
    rw [h]
    exact ⟨rfl, rfl, rfl⟩
  · rename_i found h
    rw [h]
    exact ⟨rfl, rfl, rfl⟩

/-! ## Loop 1: the empty table -/

theorem getD_setB_ne (a : Array Bool) (i j : Nat) (v : Bool) (hij : j ≠ i) :
    (a.setIfInBounds i v).getD j false = a.getD j false := by
  simp [Array.getD_eq_getD_getElem?, hij.symm]

theorem getD_setB_self (a : Array Bool) (i : Nat) (v : Bool) (hi : i < a.size) :
    (a.setIfInBounds i v).getD i false = v := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem size_setB (a : Array Bool) (i : Nat) (v : Bool) : (a.setIfInBounds i v).size = a.size :=
  Array.size_setIfInBounds

theorem stream_loop1_spec (starts lengths : Array UInt32) (live : Array Bool) :
    ∀ (fuel : Nat) (i : UInt32), i.toNat ≤ 256 → 256 - i.toNat < fuel →
      ∃ (starts' lengths' : Array UInt32) (live' : Array Bool) (i' : UInt32),
        rup_stream_check.loop1 starts lengths live i fuel = some (starts', lengths', live', i') ∧
        starts'.size = starts.size ∧ lengths'.size = lengths.size ∧ live'.size = live.size ∧
        (∀ v, starts'.getD v 0 = if i.toNat ≤ v ∧ v < 256 then 0 else starts.getD v 0) ∧
        (∀ v, lengths'.getD v 0 = if i.toNat ≤ v ∧ v < 256 then 0 else lengths.getD v 0) ∧
        (∀ v, live'.getD v false = if i.toNat ≤ v ∧ v < 256 then false else live.getD v false) := by
  intro fuel
  induction fuel generalizing starts lengths live with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro i hi hf
    rw [rup_stream_check.loop1]
    have h256 : (256 : UInt32).toNat = 256 := by decide
    by_cases hin : i.toNat < 256
    · have hlt : decide (i < 256) = true := by rw [decide_lt_toNat, h256]; exact decide_eq_true hin
      simp only [hlt, ite_true]
      have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ i (by omega)
      obtain ⟨s', l', v', i', hrun, hs, hl, hv, hgs, hgl, hgv⟩ :=
        ih (starts.setIfInBounds i.toNat 0) (lengths.setIfInBounds i.toNat 0) (live.setIfInBounds i.toNat false)
          (i + 1) (by omega) (by omega)
      refine ⟨s', l', v', i', hrun, by rw [hs, size_set], by rw [hl, size_set], by rw [hv, Array.size_setIfInBounds],
        ?_, ?_, ?_⟩
      · intro v
        rw [hgs v, hsucc]
        by_cases hvi : v = i.toNat
        · rw [hvi]
          by_cases hlt' : i.toNat < starts.size
          · rw [getD_set_self starts i.toNat 0 hlt']
            simp [hin]
          · have hz : starts.getD i.toNat 0 = 0 := by
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
              rfl
            have hz' : (starts.setIfInBounds i.toNat 0).getD i.toNat 0 = 0 := by
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_set]; omega)]
              rfl
            rw [hz', hz]
            simp
        · rw [getD_set_ne starts i.toNat v 0 hvi]
          have hiff : (i.toNat + 1 ≤ v ∧ v < 256) ↔ (i.toNat ≤ v ∧ v < 256) := by omega
          simp only [hiff]
      · intro v
        rw [hgl v, hsucc]
        by_cases hvi : v = i.toNat
        · rw [hvi]
          by_cases hlt' : i.toNat < lengths.size
          · rw [getD_set_self lengths i.toNat 0 hlt']
            simp [hin]
          · have hz : lengths.getD i.toNat 0 = 0 := by
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
              rfl
            have hz' : (lengths.setIfInBounds i.toNat 0).getD i.toNat 0 = 0 := by
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_set]; omega)]
              rfl
            rw [hz', hz]
            simp
        · rw [getD_set_ne lengths i.toNat v 0 hvi]
          have hiff : (i.toNat + 1 ≤ v ∧ v < 256) ↔ (i.toNat ≤ v ∧ v < 256) := by omega
          simp only [hiff]
      · intro v
        rw [hgv v, hsucc]
        by_cases hvi : v = i.toNat
        · rw [hvi]
          by_cases hlt' : i.toNat < live.size
          · rw [getD_setB_self live i.toNat false hlt']
            simp [hin]
          · have hz : live.getD i.toNat false = false := by
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
              rfl
            have hz' : (live.setIfInBounds i.toNat false).getD i.toNat false = false := by
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_setIfInBounds]; omega)]
              rfl
            rw [hz', hz]
            simp
        · rw [getD_setB_ne live i.toNat v false hvi]
          have hiff : (i.toNat + 1 ≤ v ∧ v < 256) ↔ (i.toNat ≤ v ∧ v < 256) := by omega
          simp only [hiff]
    · have hlt : decide (i < 256) = false := by
        rw [decide_lt_toNat, h256]; exact decide_eq_false hin
      simp only [hlt, Bool.false_eq_true, ite_false, pure]
      refine ⟨starts, lengths, live, i, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> intro v <;>
        have : ¬ (i.toNat ≤ v ∧ v < 256) := by omega
      all_goals simp [this]

/-! ## Arrays that represent the layout's lists -/

theorem toNats_eq_of_rel (a : Array UInt32) (l : List Nat) (hsize : a.size = l.length)
    (hget : ∀ i, i < l.length → (a.getD i 0).toNat = l.getD i 0) : toNats a = l := by
  apply List.ext_getElem
  · rw [toNats_length, hsize]
  · intro i h1 h2
    rw [← getD_toNats_of_lt a i (by rw [hsize]; exact h2), ← getD_toNats, hget i h2,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-! ## Loop 2: every literal below the variable count -/

theorem stream_loop2_invalid (pool : Array UInt32) (variables i : UInt32) (fuel : Nat) :
    rup_stream_check.loop2 pool variables false i (fuel + 1) = some (false, i) := by
  rw [rup_stream_check.loop2]
  simp

theorem stream_loop2_spec (pool : Array UInt32) (variables : UInt32) (hpool : pool.size ≤ 4096) :
    ∀ (fuel : Nat) (i : UInt32), i.toNat ≤ pool.size → pool.size - i.toNat < fuel →
      ∃ i' : UInt32, rup_stream_check.loop2 pool variables true i fuel =
        some ((List.range' i.toNat (pool.size - i.toNat)).all
          (fun k => decide ((pool.getD k 0).toNat / 2 < variables.toNat)), i') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro i hi hf
    rw [rup_stream_check.loop2]
    have hsz : pool.size.toUInt32.toNat = pool.size := toNat_size32 pool.size (by show pool.size < 4294967296; omega)
    by_cases hin : i.toNat < pool.size
    · have hlt : decide (i < pool.size.toUInt32) = true := by
        rw [decide_lt_toNat, hsz]; exact decide_eq_true hin
      simp only [hlt, Bool.and_true, ite_true]
      have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ i (by omega)
      have hrange : pool.size - i.toNat = (pool.size - (i.toNat + 1)) + 1 := by omega
      rw [hrange, List.range'_succ, List.all_cons, decide_lt_toNat, toNat_div2]
      by_cases hv : (pool.getD i.toNat 0).toNat / 2 < variables.toNat
      · rw [decide_eq_true hv, Bool.true_and]
        obtain ⟨i', hi'⟩ := ih (i + 1) (by omega) (by omega)
        rw [hsucc] at hi'
        exact ⟨i', hi'⟩
      · rw [decide_eq_false hv, Bool.false_and]
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, stream_loop2_invalid]
        exact ⟨i + 1, rfl⟩
    · have hlt : decide (i < pool.size.toUInt32) = false := by
        rw [decide_lt_toNat, hsz]; exact decide_eq_false hin
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      refine ⟨i, ?_⟩
      have : pool.size - i.toNat = 0 := by omega
      simp [this]

/-- The literal check over the whole pool is the model's guard. -/
theorem pool_all_eq (pool : Array UInt32) (variables : UInt32) :
    (List.range' 0 pool.size).all (fun k => decide ((pool.getD k 0).toNat / 2 < variables.toNat)) =
      (toNats pool).all (fun n => decide (n / 2 < variables.toNat)) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h n hn
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hn
    rw [toNats_length] at hi
    rw [← getD_toNats_of_lt pool i hi, ← getD_toNats]
    exact h i (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  · intro h k hk
    have hk' : k < pool.size := by have := List.mem_range'_1.mp hk; omega
    have := h ((toNats pool)[k]'(by rw [toNats_length]; exact hk')) (List.getElem_mem _)
    rwa [← getD_toNats_of_lt pool k hk', ← getD_toNats] at this

/-! ## Loop 6: copying the proposed clause -/

theorem stream_loop6_spec (pool proposed : Array UInt32) (cmd : RUPCommand)
    (hsc : cmd.start.toNat + cmd.count.toNat ≤ pool.size) (hpool : pool.size ≤ 4096)
    (hprop : cmd.count.toNat ≤ proposed.size) :
    ∀ (fuel : Nat) (p : UInt32), p.toNat ≤ cmd.count.toNat → cmd.count.toNat - p.toNat < fuel →
      ∃ (proposed' : Array UInt32) (p' : UInt32),
        rup_stream_check.loop6 pool proposed true cmd p fuel = some (proposed', p') ∧
        proposed'.size = proposed.size ∧
        ∀ q, proposed'.getD q 0 = if p.toNat ≤ q ∧ q < cmd.count.toNat then pool.getD (cmd.start.toNat + q) 0
          else proposed.getD q 0 := by
  intro fuel
  induction fuel generalizing proposed with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro p hp hf
    rw [rup_stream_check.loop6]
    by_cases hin : p.toNat < cmd.count.toNat
    · have hlt : decide (p < cmd.count) = true := (lt_iff_toNat _ _).mpr hin
      simp only [hlt, Bool.and_true, ite_true]
      have hsucc : (p + 1).toNat = p.toNat + 1 := toNat_succ p (by omega)
      have hadd : (cmd.start + p).toNat = cmd.start.toNat + p.toNat := toNat_add32 _ _ (by
        show cmd.start.toNat + p.toNat < 4294967296; omega)
      obtain ⟨pr', p', hrun, hsize, hget⟩ := ih (proposed.setIfInBounds p.toNat (pool.getD (cmd.start + p).toNat 0))
        (by rw [size_set]; exact hprop) (p + 1) (by omega) (by omega)
      refine ⟨pr', p', hrun, by rw [hsize, size_set], ?_⟩
      intro q
      rw [hget q, hsucc]
      by_cases hq : q = p.toNat
      · rw [hq, getD_set_self proposed p.toNat _ (by omega), hadd]
        simp [hin]
      · rw [getD_set_ne proposed p.toNat q _ hq]
        have hiff : (p.toNat + 1 ≤ q ∧ q < cmd.count.toNat) ↔ (p.toNat ≤ q ∧ q < cmd.count.toNat) := by omega
        simp only [hiff]
    · have hlt : decide (p < cmd.count) = false := by
        have := lt_iff_toNat p cmd.count
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      refine ⟨proposed, p, rfl, rfl, ?_⟩
      intro q
      have : ¬ (p.toNat ≤ q ∧ q < cmd.count.toNat) := by omega
      simp [this]

theorem stream_loop6_invalid (pool proposed : Array UInt32) (cmd : RUPCommand) (p : UInt32) (fuel : Nat) :
    rup_stream_check.loop6 pool proposed false cmd p (fuel + 1) = some (proposed, p) := by
  rw [rup_stream_check.loop6]
  simp

/-- The copied clause, read back as the kernel's target, is the pool's clause. -/
theorem targetList_copy (pool proposed : Array UInt32) (start count : Nat)
    (hsc : start + count ≤ pool.size) (hprop : count ≤ proposed.size)
    (hget : ∀ q, q < count → proposed.getD q 0 = pool.getD (start + q) 0) :
    targetList proposed count = clauseAt pool start count := by
  apply List.ext_getElem
  · rw [targetList_length proposed count hprop, clauseAt_length pool start count hsc]
  · intro i h1 h2
    rw [clauseAt_getElem pool start count i (by rw [clauseAt_length pool start count hsc] at h2; exact h2) hsc]
    have hi : i < count := by rw [targetList_length proposed count hprop] at h1; exact h1
    simp only [targetList, List.getElem_take]
    rw [← getD_toNats_of_lt proposed i (by omega), ← getD_toNats, hget i hi]

/-! ## Loop 5: mapping the hints -/

/-- A hint id the stream accepts: one-based, at most 256, and live. -/
def refOK (live : Array Bool) (id : UInt32) : Bool :=
  decide (0 < id.toNat) && decide (id.toNat ≤ 256) && live.getD (id.toNat - 1) false

theorem stream_loop5_invalid (refs : Array UInt32) (live : Array Bool) (mapped : Array UInt32) (cmd : RUPCommand)
    (h : UInt32) (fuel : Nat) :
    rup_stream_check.loop5 refs live mapped false cmd h (fuel + 1) = some (mapped, false, h) := by
  rw [rup_stream_check.loop5]
  simp

theorem stream_loop5_spec (refs : Array UInt32) (live : Array Bool) (cmd : RUPCommand)
    (hrs : cmd.refs_start.toNat + cmd.refs_count.toNat ≤ refs.size) (hrefs : refs.size ≤ 4096)
    (hn : cmd.refs_count.toNat ≤ 256) :
    ∀ (fuel : Nat) (mapped : Array UInt32) (h : UInt32), h.toNat ≤ cmd.refs_count.toNat →
      cmd.refs_count.toNat - h.toNat < fuel → cmd.refs_count.toNat ≤ mapped.size →
      ∃ (mapped' : Array UInt32) (h' : UInt32),
        rup_stream_check.loop5 refs live mapped true cmd h fuel =
          some (mapped', (List.range' h.toNat (cmd.refs_count.toNat - h.toNat)).all
            (fun k => refOK live (refs.getD (cmd.refs_start.toNat + k) 0)), h') ∧
        mapped'.size = mapped.size ∧
        ((List.range' h.toNat (cmd.refs_count.toNat - h.toNat)).all
            (fun k => refOK live (refs.getD (cmd.refs_start.toNat + k) 0)) = true →
          ∀ k, mapped'.getD k 0 = if h.toNat ≤ k ∧ k < cmd.refs_count.toNat
            then refs.getD (cmd.refs_start.toNat + k) 0 - 1 else mapped.getD k 0) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ fuel ih =>
    intro mapped h hh hf hm
    rw [rup_stream_check.loop5]
    by_cases hin : h.toNat < cmd.refs_count.toNat
    · have hlt : decide (h < cmd.refs_count) = true := (lt_iff_toNat _ _).mpr hin
      simp only [hlt, Bool.and_true, ite_true]
      have hsucc : (h + 1).toNat = h.toNat + 1 := toNat_succ h (by omega)
      have hadd : (cmd.refs_start + h).toNat = cmd.refs_start.toNat + h.toNat := toNat_add32 _ _ (by
        show cmd.refs_start.toNat + h.toNat < 4294967296; omega)
      have hrange : cmd.refs_count.toNat - h.toNat = (cmd.refs_count.toNat - (h.toNat + 1)) + 1 := by omega
      rw [hrange, List.range'_succ, List.all_cons, hadd]
      have h256 : (256 : UInt32).toNat = 256 := by decide
      have hg0 : decide (refs.getD (cmd.refs_start.toNat + h.toNat) 0 > 0) =
          decide (0 < (refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat) := by
        show decide ((0 : UInt32) < _) = _
        rw [decide_lt_toNat, UInt32.toNat_zero]
      have hg1 : decide (refs.getD (cmd.refs_start.toNat + h.toNat) 0 <= 256) =
          decide ((refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat ≤ 256) := by
        rw [decide_le_toNat, h256]
      rw [hg0, hg1]
      by_cases hpos : 0 < (refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat ∧
          (refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat ≤ 256
      · rw [decide_eq_true hpos.1, decide_eq_true hpos.2]
        simp only [Bool.and_self, ite_true, pure, bind, Option.bind]
        have hsub : (refs.getD (cmd.refs_start.toNat + h.toNat) 0 - 1).toNat =
            (refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat - 1 :=
          toNat_sub_of_le' _ _ (by rw [UInt32.toNat_one]; exact hpos.1)
        rw [hsub]
        have hok : refOK live (refs.getD (cmd.refs_start.toNat + h.toNat) 0) =
            live.getD ((refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat - 1) false := by
          unfold refOK
          rw [decide_eq_true hpos.1, decide_eq_true hpos.2]
          rfl
        rw [hok]
        cases hl : live.getD ((refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat - 1) false with
        | true =>
          rw [Bool.true_and]
          obtain ⟨m', h', hrun, hsize, hget⟩ := ih
            (mapped.setIfInBounds h.toNat (refs.getD (cmd.refs_start.toNat + h.toNat) 0 - 1)) (h + 1)
            (by omega) (by omega) (by rw [size_set]; exact hm)
          rw [hsucc] at hrun hget
          refine ⟨m', h', hrun, by rw [hsize, size_set], ?_⟩
          intro hall k
          rw [hget hall k]
          by_cases hk : k = h.toNat
          · rw [hk, getD_set_self mapped h.toNat _ (by omega)]
            simp [hin]
          · rw [getD_set_ne mapped h.toNat k _ hk]
            have hiff : (h.toNat + 1 ≤ k ∧ k < cmd.refs_count.toNat) ↔ (h.toNat ≤ k ∧ k < cmd.refs_count.toNat) := by
              omega
            simp only [hiff]
        | false =>
          rw [Bool.false_and]
          obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          rw [hfe, stream_loop5_invalid]
          refine ⟨_, h + 1, rfl, size_set _ _ _, ?_⟩
          intro hfalse
          cases hfalse
      · have hfalse : (decide (0 < (refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat) &&
            decide ((refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat ≤ 256)) = false := by
          rcases Bool.eq_false_or_eq_true (decide (0 < (refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat) &&
              decide ((refs.getD (cmd.refs_start.toNat + h.toNat) 0).toNat ≤ 256)) with hb | hb
          · exfalso
            apply hpos
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
            exact hb
          · exact hb
        have hok : refOK live (refs.getD (cmd.refs_start.toNat + h.toNat) 0) = false := by
          unfold refOK
          rw [hfalse, Bool.false_and]
        rw [hfalse, hok, Bool.false_and]
        simp only [Bool.false_eq_true, ite_false, pure, bind, Option.bind]
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, stream_loop5_invalid]
        refine ⟨mapped, h + 1, rfl, rfl, ?_⟩
        intro hfalse'
        cases hfalse'
    · have hlt : decide (h < cmd.refs_count) = false := by
        have := lt_iff_toNat h cmd.refs_count
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      have hz : cmd.refs_count.toNat - h.toNat = 0 := by omega
      rw [hz]
      refine ⟨mapped, h, rfl, rfl, ?_⟩
      intro _ k
      have : ¬ (h.toNat ≤ k ∧ k < cmd.refs_count.toNat) := by omega
      simp [this]

/-! ## Loop 7: deletions -/

/-- The kernel's deletion walk on lists: exactly `rup_stream_check.loop7`'s
effect on the liveness array, including the write it makes before
noticing a dead slot. -/
def clearAll (live : Array Bool) : List Nat → Bool × Array Bool
  | [] => (true, live)
  | id :: rest =>
    if 0 < id ∧ id ≤ 256 then
      if live.getD (id - 1) false then clearAll (live.setIfInBounds (id - 1) false) rest
      else (false, live.setIfInBounds (id - 1) false)
    else (false, live)

theorem clearAll_size (ids : List Nat) : ∀ live : Array Bool, (clearAll live ids).2.size = live.size := by
  induction ids with
  | nil => intro live; rfl
  | cons id rest ih =>
    intro live
    simp only [clearAll]
    by_cases hp : 0 < id ∧ id ≤ 256
    · rw [if_pos hp]
      by_cases hl : live.getD (id - 1) false = true
      · rw [if_pos hl, ih, size_setB]
      · rw [if_neg hl]
        exact size_setB _ _ _
    · rw [if_neg hp]

theorem stream_loop7_invalid (refs : Array UInt32) (live : Array Bool) (cmd : RUPCommand) (d : UInt32) (fuel : Nat) :
    rup_stream_check.loop7 refs live false cmd d (fuel + 1) = some (live, false, d) := by
  rw [rup_stream_check.loop7]
  simp

theorem stream_loop7_spec (refs : Array UInt32) (cmd : RUPCommand)
    (hrs : cmd.refs_start.toNat + cmd.refs_count.toNat ≤ refs.size) (hrefs : refs.size ≤ 4096) :
    ∀ (fuel : Nat) (live : Array Bool) (d : UInt32), d.toNat ≤ cmd.refs_count.toNat →
      cmd.refs_count.toNat - d.toNat < fuel →
      ∃ d' : UInt32, rup_stream_check.loop7 refs live true cmd d fuel =
        some ((clearAll live ((clauseAt refs cmd.refs_start.toNat cmd.refs_count.toNat).drop d.toNat)).2,
          (clearAll live ((clauseAt refs cmd.refs_start.toNat cmd.refs_count.toNat).drop d.toNat)).1, d') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ fuel ih =>
    intro live d hd hf
    rw [rup_stream_check.loop7]
    have hcl := clauseAt_length refs cmd.refs_start.toNat cmd.refs_count.toNat hrs
    by_cases hin : d.toNat < cmd.refs_count.toNat
    · have hlt : decide (d < cmd.refs_count) = true := (lt_iff_toNat _ _).mpr hin
      simp only [hlt, Bool.and_true, ite_true]
      have hsucc : (d + 1).toNat = d.toNat + 1 := toNat_succ d (by omega)
      have hadd : (cmd.refs_start + d).toNat = cmd.refs_start.toNat + d.toNat := toNat_add32 _ _ (by
        show cmd.refs_start.toNat + d.toNat < 4294967296; omega)
      have hdl : d.toNat < (clauseAt refs cmd.refs_start.toNat cmd.refs_count.toNat).length := by
        rw [hcl]; exact hin
      have hdrop : (clauseAt refs cmd.refs_start.toNat cmd.refs_count.toNat).drop d.toNat =
          (refs.getD (cmd.refs_start + d).toNat 0).toNat ::
            (clauseAt refs cmd.refs_start.toNat cmd.refs_count.toNat).drop (d.toNat + 1) := by
        rw [List.drop_eq_getElem_cons hdl, clauseAt_getElem refs _ _ d.toNat hin hrs, hadd]
      rw [hdrop]
      simp only [clearAll]
      have h256 : (256 : UInt32).toNat = 256 := by decide
      have hg0 : decide (refs.getD (cmd.refs_start + d).toNat 0 > 0) =
          decide (0 < (refs.getD (cmd.refs_start + d).toNat 0).toNat) := by
        show decide ((0 : UInt32) < _) = _
        rw [decide_lt_toNat, UInt32.toNat_zero]
      have hg1 : decide (refs.getD (cmd.refs_start + d).toNat 0 <= 256) =
          decide ((refs.getD (cmd.refs_start + d).toNat 0).toNat ≤ 256) := by
        rw [decide_le_toNat, h256]
      rw [hg0, hg1]
      by_cases hpos : 0 < (refs.getD (cmd.refs_start + d).toNat 0).toNat ∧
          (refs.getD (cmd.refs_start + d).toNat 0).toNat ≤ 256
      · rw [decide_eq_true hpos.1, decide_eq_true hpos.2, if_pos hpos]
        simp only [Bool.and_self, ite_true, pure, bind, Option.bind]
        have hsub : (refs.getD (cmd.refs_start + d).toNat 0 - 1).toNat =
            (refs.getD (cmd.refs_start + d).toNat 0).toNat - 1 :=
          toNat_sub_of_le' _ _ (by rw [UInt32.toNat_one]; exact hpos.1)
        rw [hsub]
        cases hl : live.getD ((refs.getD (cmd.refs_start + d).toNat 0).toNat - 1) false with
        | true =>
          rw [if_pos rfl]
          obtain ⟨d', hd'⟩ := ih (live.setIfInBounds ((refs.getD (cmd.refs_start + d).toNat 0).toNat - 1) false)
            (d + 1) (by omega) (by omega)
          rw [hsucc] at hd'
          exact ⟨d', hd'⟩
        | false =>
          rw [if_neg Bool.false_ne_true]
          obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          rw [hfe, stream_loop7_invalid]
          exact ⟨d + 1, rfl⟩
      · have hfalse : (decide (0 < (refs.getD (cmd.refs_start + d).toNat 0).toNat) &&
            decide ((refs.getD (cmd.refs_start + d).toNat 0).toNat ≤ 256)) = false := by
          rcases Bool.eq_false_or_eq_true (decide (0 < (refs.getD (cmd.refs_start + d).toNat 0).toNat) &&
              decide ((refs.getD (cmd.refs_start + d).toNat 0).toNat ≤ 256)) with hb | hb
          · exfalso
            apply hpos
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
            exact hb
          · exact hb
        rw [hfalse, if_neg hpos]
        simp only [Bool.false_eq_true, ite_false, pure, bind, Option.bind]
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, stream_loop7_invalid]
        exact ⟨d + 1, rfl⟩
    · have hlt : decide (d < cmd.refs_count) = false := by
        have := lt_iff_toNat d cmd.refs_count
        exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      have hnil : (clauseAt refs cmd.refs_start.toNat cmd.refs_count.toNat).drop d.toNat = [] :=
        List.drop_eq_nil_of_le (by rw [hcl]; omega)
      rw [hnil]
      exact ⟨d, rfl⟩

/-- Clearing a slot keeps the table relation with the cleared array. -/
theorem tableRel_clear (t : LiveTable.Table) (starts lengths : Array UInt32) (live : Array Bool)
    (htable : TableRel t starts lengths live) (hsize : live.size = 256) (slot : Nat) (hs : slot < 256) :
    TableRel (LiveTable.clear t slot) starts lengths (live.setIfInBounds slot false) := by
  intro key hk
  unfold LiveTable.clear
  by_cases hks : key = slot
  · rw [if_pos hks, hks, htable slot hs, getD_setB_self live slot false (by omega)]
  · rw [if_neg hks, htable key hk, getD_setB_ne live slot key false hks]

/-- The model's sequential deletion is the kernel's walk. -/
theorem deleteIDs_clearAll {pool : List Nat} {initial : Database} (ids : List Nat) :
    ∀ (s : State pool initial) (starts lengths : Array UInt32) (live : Array Bool),
      TableRel s.table starts lengths live → live.size = 256 →
      (deleteIDs s ids).isSome = (clearAll live ids).1 ∧
      ∀ s', deleteIDs s ids = some s' →
        TableRel s'.table starts lengths (clearAll live ids).2 ∧ s'.last = s.last ∧ s'.refuted = s.refuted := by
  induction ids with
  | nil =>
    intro s starts lengths live htable _
    refine ⟨rfl, ?_⟩
    intro s' hs'
    cases hs'
    exact ⟨htable, rfl, rfl⟩
  | cons id rest ih =>
    intro s starts lengths live htable hsize
    simp only [deleteIDs, clearAll]
    by_cases hp : 0 < id ∧ id ≤ 256
    · rw [dif_pos hp, if_pos hp]
      have hl : (s.table (id - 1)).live = live.getD (id - 1) false := by
        rw [htable (id - 1) (by omega)]
      rw [hl]
      cases hlv : live.getD (id - 1) false with
      | true =>
        rw [if_pos rfl, if_pos rfl]
        have := ih (eraseOne s id hp.1) starts lengths (live.setIfInBounds (id - 1) false)
          (tableRel_clear s.table starts lengths live htable hsize (id - 1) (by omega)) (by rw [size_setB]; exact hsize)
        refine ⟨this.1, ?_⟩
        intro s' hs'
        obtain ⟨ht, hlast, href⟩ := this.2 s' hs'
        exact ⟨ht, by rw [hlast, deletion_keeps_last], by rw [href, deletion_keeps_refutation]⟩
      | false =>
        rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
        refine ⟨rfl, ?_⟩
        intro s' hs'
        cases hs'
    · rw [dif_neg hp, if_neg hp]
      refine ⟨rfl, ?_⟩
      intro s' hs'
      cases hs'

/-! ## Loop 3: the initial clauses -/

theorem stream_loop3_invalid (pool initial sizes starts lengths : Array UInt32) (live : Array Bool) (i : UInt32)
    (refuted : Bool) (fuel : Nat) :
    rup_stream_check.loop3 pool initial sizes starts lengths live false i refuted (fuel + 1) =
      some (starts, lengths, live, false, i, refuted) := by
  rw [rup_stream_check.loop3]
  simp

/-- The initial range checks from position `i`. -/
def initialOK (pool initial sizes : Array UInt32) (i n : Nat) : Bool :=
  (List.range' i (n - i)).all (fun k => decide (rangeSafe (initial.getD k 0).toNat (sizes.getD k 0).toNat pool.size))

theorem beq_zero_eq (x : UInt32) : (x == 0) = decide (x.toNat = 0) := by
  rw [beq_ofNat32 x 0 (by decide), Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]

theorem stream_loop3_spec (pool initial sizes : Array UInt32) (hpool : pool.size ≤ 4096) (hn : initial.size ≤ 256) :
    ∀ (fuel : Nat) (starts lengths : Array UInt32) (live : Array Bool) (i : UInt32) (refuted : Bool),
      initial.size ≤ starts.size → initial.size ≤ lengths.size → initial.size ≤ live.size →
      i.toNat ≤ initial.size → initial.size - i.toNat < fuel →
      ∃ (starts' lengths' : Array UInt32) (live' : Array Bool) (i' : UInt32) (refuted' : Bool),
        rup_stream_check.loop3 pool initial sizes starts lengths live true i refuted fuel =
          some (starts', lengths', live', initialOK pool initial sizes i.toNat initial.size, i', refuted') ∧
        starts'.size = starts.size ∧ lengths'.size = lengths.size ∧ live'.size = live.size ∧
        (initialOK pool initial sizes i.toNat initial.size = true →
          (∀ v, starts'.getD v 0 = if i.toNat ≤ v ∧ v < initial.size then initial.getD v 0 else starts.getD v 0) ∧
          (∀ v, lengths'.getD v 0 = if i.toNat ≤ v ∧ v < initial.size then sizes.getD v 0 else lengths.getD v 0) ∧
          (∀ v, live'.getD v false = if i.toNat ≤ v ∧ v < initial.size then true else live.getD v false) ∧
          refuted' = (refuted || (List.range' i.toNat (initial.size - i.toNat)).any
            (fun k => decide ((sizes.getD k 0).toNat = 0)))) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro starts lengths live i refuted hss hls hvs hi hf
    rw [rup_stream_check.loop3]
    have hsz : initial.size.toUInt32.toNat = initial.size := toNat_size32 initial.size (by
      show initial.size < 4294967296; omega)
    by_cases hin : i.toNat < initial.size
    · have hlt : decide (i < initial.size.toUInt32) = true := by
        rw [decide_lt_toNat, hsz]; exact decide_eq_true hin
      simp only [hlt, Bool.and_true, ite_true, range_check_eq pool hpool]
      have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ i (by omega)
      have hrange : initial.size - i.toNat = (initial.size - (i.toNat + 1)) + 1 := by omega
      have hok : initialOK pool initial sizes i.toNat initial.size =
          (decide (rangeSafe (initial.getD i.toNat 0).toNat (sizes.getD i.toNat 0).toNat pool.size) &&
            initialOK pool initial sizes (i.toNat + 1) initial.size) := by
        unfold initialOK
        rw [hrange, List.range'_succ, List.all_cons]
      rw [hok]
      by_cases hsafe : rangeSafe (initial.getD i.toNat 0).toNat (sizes.getD i.toNat 0).toNat pool.size
      · rw [decide_eq_true hsafe, Bool.true_and]
        simp only [ite_true, pure, bind, Option.bind]
        obtain ⟨s', l', v', i', r', hrun, hs, hl, hv, hrest⟩ := ih (starts.setIfInBounds i.toNat (initial.getD i.toNat 0))
          (lengths.setIfInBounds i.toNat (sizes.getD i.toNat 0)) (live.setIfInBounds i.toNat true) (i + 1)
          (refuted || (sizes.getD i.toNat 0 == 0)) (by rw [size_set]; exact hss) (by rw [size_set]; exact hls)
          (by rw [size_setB]; exact hvs) (by omega) (by omega)
        rw [hsucc] at hrun hrest
        refine ⟨s', l', v', i', r', hrun, by rw [hs, size_set], by rw [hl, size_set], by rw [hv, size_setB], ?_⟩
        intro hall
        obtain ⟨hgs, hgl, hgv, hr⟩ := hrest hall
        have hiff : ∀ v, (i.toNat + 1 ≤ v ∧ v < initial.size) ↔ (v ≠ i.toNat ∧ (i.toNat ≤ v ∧ v < initial.size)) := by
          intro v; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro v
          rw [hgs v]
          by_cases hvi : v = i.toNat
          · rw [hvi, getD_set_self starts i.toNat _ (by omega)]
            simp [hin]
          · rw [getD_set_ne starts i.toNat v _ hvi]
            simp only [hiff v, ne_eq, hvi, not_false_eq_true, true_and]
        · intro v
          rw [hgl v]
          by_cases hvi : v = i.toNat
          · rw [hvi, getD_set_self lengths i.toNat _ (by omega)]
            simp [hin]
          · rw [getD_set_ne lengths i.toNat v _ hvi]
            simp only [hiff v, ne_eq, hvi, not_false_eq_true, true_and]
        · intro v
          rw [hgv v]
          by_cases hvi : v = i.toNat
          · rw [hvi, getD_setB_self live i.toNat _ (by omega)]
            simp [hin]
          · rw [getD_setB_ne live i.toNat v _ hvi]
            simp only [hiff v, ne_eq, hvi, not_false_eq_true, true_and]
        · rw [hr, hrange, List.range'_succ, List.any_cons, beq_zero_eq, Bool.or_assoc]
      · rw [decide_eq_false hsafe, Bool.false_and]
        simp only [Bool.false_eq_true, ite_false, pure, bind, Option.bind]
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, stream_loop3_invalid]
        refine ⟨starts, lengths, live, i + 1, refuted, rfl, rfl, rfl, rfl, ?_⟩
        intro hfalse
        cases hfalse
    · have hlt : decide (i < initial.size.toUInt32) = false := by
        rw [decide_lt_toNat, hsz]; exact decide_eq_false hin
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      have hz : initial.size - i.toNat = 0 := by omega
      have hok : initialOK pool initial sizes i.toNat initial.size = true := by
        unfold initialOK; rw [hz]; rfl
      rw [hok]
      refine ⟨starts, lengths, live, i, refuted, rfl, rfl, rfl, rfl, ?_⟩
      intro _
      have hno : ∀ v, ¬ (i.toNat ≤ v ∧ v < initial.size) := by intro v; omega
      refine ⟨fun v => by simp [hno v], fun v => by simp [hno v], fun v => by simp [hno v], ?_⟩
      rw [hz]
      simp

/-! ## The model's command, case by case -/

section CommandCases
variable (raw : Layout) {initial : Database} (s : State raw.pool initial) (c : Command)

theorem command_id_big (h : c.id > 2147483647) : command raw s c = none := by
  unfold command
  rw [if_pos h]

theorem command_refs_none (h : ¬ c.id > 2147483647) (hr : readRange raw.refs c.refsStart c.refsCount = none) :
    command raw s c = none := by
  unfold command
  rw [if_neg h, hr]

theorem command_add_stale (h : ¬ c.id > 2147483647) (refs : List Nat)
    (hr : readRange raw.refs c.refsStart c.refsCount = some refs) (ha : c.addition = true)
    (hf : ¬ (s.last < c.id ∧ c.id ≤ 256)) : command raw s c = none := by
  unfold command
  rw [if_neg h, hr]
  simp only [ha, ite_true]
  rw [dif_neg hf]

theorem command_add_many (h : ¬ c.id > 2147483647) (refs : List Nat)
    (hr : readRange raw.refs c.refsStart c.refsCount = some refs) (ha : c.addition = true)
    (hf : s.last < c.id ∧ c.id ≤ 256) (hm : c.refsCount > 256) : command raw s c = none := by
  unfold command
  rw [if_neg h, hr]
  simp only [ha, ite_true]
  rw [dif_pos hf, if_pos hm]

theorem command_add_dead (h : ¬ c.id > 2147483647) (refs : List Nat)
    (hr : readRange raw.refs c.refsStart c.refsCount = some refs) (ha : c.addition = true)
    (hf : s.last < c.id ∧ c.id ≤ 256) (hm : ¬ c.refsCount > 256)
    (hl : (refs.all fun id => decide (0 < id ∧ id ≤ 256) && (s.table (id - 1)).live) = false) :
    command raw s c = none := by
  unfold command
  rw [if_neg h, hr]
  simp only [ha, ite_true]
  rw [dif_pos hf, if_neg hm, hl]
  rfl

theorem command_add_noclause (h : ¬ c.id > 2147483647) (refs : List Nat)
    (hr : readRange raw.refs c.refsStart c.refsCount = some refs) (ha : c.addition = true)
    (hf : s.last < c.id ∧ c.id ≤ 256) (hm : ¬ c.refsCount > 256)
    (hl : (refs.all fun id => decide (0 < id ∧ id ≤ 256) && (s.table (id - 1)).live) = true)
    (hc : readClause raw.pool c.start c.count = none) : command raw s c = none := by
  unfold command
  rw [if_neg h, hr]
  simp only [ha, ite_true]
  rw [dif_pos hf, if_neg hm, hl]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  split
  · rfl
  · rename_i clause hc'
    rw [hc] at hc'
    cases hc'

theorem publishCertified_fields {pool : List Nat} {initial : Database} (s : State pool initial)
    (id start count : Nat) (positive : 0 < id) (clause : Clause)
    (decoded : readClause pool start count = some clause)
    (certificate : PropagationChain.CertifiedClause (LiveTable.database pool s.table) clause) :
    (publishCertified s id start count positive clause decoded certificate).table =
        LiveTable.publish s.table (id - 1) start count ∧
      (publishCertified s id start count positive clause decoded certificate).last = id ∧
      (publishCertified s id start count positive clause decoded certificate).refuted =
        (s.refuted || decide (clause = [])) := by
  unfold publishCertified
  by_cases he : clause = []
  · simp [he]
  · simp [he]

theorem command_add_check (h : ¬ c.id > 2147483647) (refs : List Nat)
    (hr : readRange raw.refs c.refsStart c.refsCount = some refs) (ha : c.addition = true)
    (hf : s.last < c.id ∧ c.id ≤ 256) (hm : ¬ c.refsCount > 256)
    (hl : (refs.all fun id => decide (0 < id ∧ id ≤ 256) && (s.table (id - 1)).live) = true)
    (clause : Clause) (hc : readClause raw.pool c.start c.count = some clause) :
    (command raw s c).isSome =
        (PropagationChain.check raw.variables (LiveTable.database raw.pool s.table) clause refs).isSome ∧
      ∀ s', command raw s c = some s' →
        s'.table = LiveTable.publish s.table (c.id - 1) c.start c.count ∧ s'.last = c.id ∧
        s'.refuted = (s.refuted || decide (clause = [])) := by
  unfold command
  rw [if_neg h, hr]
  simp only [ha, ite_true]
  rw [dif_pos hf, if_neg hm, hl]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  split
  · rename_i hc'
    rw [hc] at hc'
    cases hc'
  · rename_i clause' hc'
    rw [hc] at hc'
    cases hc'
    split
    · rename_i hchk
      exact ⟨by rw [hchk]; rfl, fun s' hs' => by cases hs'⟩
    · rename_i cert hchk
      refine ⟨by rw [hchk]; rfl, ?_⟩
      intro s' hs'
      cases hs'
      exact publishCertified_fields s c.id c.start c.count _ clause hc cert

theorem command_delete (h : ¬ c.id > 2147483647) (refs : List Nat)
    (hr : readRange raw.refs c.refsStart c.refsCount = some refs) (ha : c.addition = false) :
    command raw s c = if c.id < s.last then none else deleteIDs s refs := by
  unfold command
  rw [if_neg h, hr]
  simp only [ha, Bool.false_eq_true, ite_false]

end CommandCases

/-- Publishing a slot keeps the table relation with the updated arrays. -/
theorem tableRel_publish (t : LiveTable.Table) (starts lengths : Array UInt32) (live : Array Bool)
    (htable : TableRel t starts lengths live) (hss : starts.size = 256) (hls : lengths.size = 256)
    (hvs : live.size = 256) (slot : Nat) (start count : UInt32) :
    TableRel (LiveTable.publish t slot start.toNat count.toNat)
      (starts.setIfInBounds slot start) (lengths.setIfInBounds slot count) (live.setIfInBounds slot true) := by
  intro key hk
  unfold LiveTable.publish
  by_cases hks : key = slot
  · rw [if_pos hks, hks, getD_set_self starts slot start (by omega), getD_set_self lengths slot count (by omega),
      getD_setB_self live slot true (by omega)]
  · rw [if_neg hks, htable key hk, getD_set_ne starts slot key start hks, getD_set_ne lengths slot key count hks,
      getD_setB_ne live slot key true hks]

/-- The liveness test the model runs over the hint ids is the kernel's `refOK`. -/
theorem refOK_eq (t : LiveTable.Table) (starts lengths : Array UInt32) (live : Array Bool)
    (htable : TableRel t starts lengths live) (id : UInt32) :
    refOK live id = (decide (0 < id.toNat ∧ id.toNat ≤ 256) && (t (id.toNat - 1)).live) := by
  unfold refOK
  rw [Bool.decide_and]
  by_cases hp : 0 < id.toNat ∧ id.toNat ≤ 256
  · rw [htable (id.toNat - 1) (by omega)]
  · have : (decide (0 < id.toNat) && decide (id.toNat ≤ 256)) = false := by
      rcases Bool.eq_false_or_eq_true (decide (0 < id.toNat) && decide (id.toNat ≤ 256)) with hb | hb
      · exfalso; apply hp; rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb; exact hb
      · exact hb
    rw [this, Bool.false_and, Bool.false_and]

/-- The mapped hints, read back one-based, are the reference slice. -/
theorem hintList_mapped_eq (refs mapped : Array UInt32) (start count : Nat)
    (hrs : start + count ≤ refs.size) (hm : count ≤ mapped.size)
    (hget : ∀ k, k < count → mapped.getD k 0 = refs.getD (start + k) 0 - 1)
    (hpos : ∀ k, k < count → 0 < (refs.getD (start + k) 0).toNat) :
    (hintList mapped count).map (· + 1) = clauseAt refs start count := by
  apply List.ext_getElem
  · rw [List.length_map, hintList_length mapped count hm, clauseAt_length refs start count hrs]
  · intro i h1 h2
    rw [List.getElem_map, clauseAt_getElem refs start count i
      (by rw [clauseAt_length refs start count hrs] at h2; exact h2) hrs]
    have hi : i < count := by rw [List.length_map, hintList_length mapped count hm] at h1; exact h1
    simp only [hintList, List.getElem_take]
    rw [← getD_toNats_of_lt mapped i (by omega), ← getD_toNats, hget i hi,
      toNat_sub_of_le' _ _ (by rw [UInt32.toNat_one]; exact hpos i hi), UInt32.toNat_one]
    have := hpos i hi
    omega

/-- Every id of the reference slice the hint loop accepted is positive. -/
theorem refs_all_pos (live : Array Bool) (refs : Array UInt32) (start count : Nat)
    (hall : (List.range' 0 count).all (fun k => refOK live (refs.getD (start + k) 0)) = true) :
    ∀ k, k < count → 0 < (refs.getD (start + k) 0).toNat := by
  intro k hk
  have := List.all_eq_true.mp hall k (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  unfold refOK at this
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

/-! ## Loop 4: the commands -/

/-- The stream loop's state represents a model state. -/
def StreamRel {pool : List Nat} {initial : Database} (s : State pool initial) (starts lengths : Array UInt32)
    (live : Array Bool) (last : UInt32) (refuted : Bool) : Prop :=
  TableRel s.table starts lengths live ∧ s.last = last.toNat ∧ s.refuted = refuted

theorem refs_all_eq (t : LiveTable.Table) (starts lengths : Array UInt32) (live : Array Bool)
    (htable : TableRel t starts lengths live) (refs : Array UInt32) (rs n : Nat) (hrs : rs + n ≤ refs.size) :
    (List.range' 0 n).all (fun k => refOK live (refs.getD (rs + k) 0)) =
      (clauseAt refs rs n).all (fun id => decide (0 < id ∧ id ≤ 256) && (t (id - 1)).live) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  have hlen := clauseAt_length refs rs n hrs
  constructor
  · intro h id hid
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hid
    rw [hlen] at hk
    rw [clauseAt_getElem refs rs n k hk hrs, ← refOK_eq t starts lengths live htable]
    exact h k (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  · intro h k hk
    have hk' : k < n := by have := List.mem_range'_1.mp hk; omega
    rw [refOK_eq t starts lengths live htable, ← clauseAt_getElem refs rs n k hk' hrs]
    exact h _ (List.getElem_mem _)

theorem stream_loop4_invalid (pool refs : Array UInt32) (commands : Array RUPCommand) (variables : UInt32)
    (starts lengths : Array UInt32) (live : Array Bool) (mapped proposed : Array UInt32) (scratch : Array UInt8)
    (refuted : Bool) (last c : UInt32) (fuel : Nat) :
    rup_stream_check.loop4 pool refs commands variables starts lengths live mapped proposed scratch false refuted
      last c (fuel + 1) = some (starts, lengths, live, mapped, proposed, scratch, false, refuted, last, c) := by
  rw [rup_stream_check.loop4]
  simp

theorem clause_empty_iff (pool : Array UInt32) (start count : Nat) (h : start + count ≤ pool.size) :
    decide ((clauseAt pool start count).map decodeLiteral = []) = decide (count = 0) := by
  apply decide_eq_decide.mpr
  rw [List.map_eq_nil_iff, List.length_eq_zero_iff.symm, clauseAt_length pool start count h]

theorem stream_loop4_spec (raw : Layout) (variables : UInt32) (pool refs : Array UInt32) (commands : Array RUPCommand)
    (hvar : variables.toNat = raw.variables) (hpool : toNats pool = raw.pool) (hrefs : toNats refs = raw.refs)
    (hcmds : commands.size = raw.commands.length)
    (hcmd : ∀ i (h : i < raw.commands.length), CmdRel (commands.getD i default) (raw.commands[i]'h))
    (hpsize : pool.size ≤ 4096) (hrsize : refs.size ≤ 4096) (hcsize : commands.size ≤ 256)
    (hpvars : ∀ i, i < pool.size → (pool.getD i 0).toNat / 2 < variables.toNat) :
    ∀ (fuel : Nat) (c : UInt32) (s : State raw.pool (origin raw)) (starts lengths mapped proposed : Array UInt32)
      (live : Array Bool) (scratch : Array UInt8) (last : UInt32) (refuted : Bool),
      StreamRel s starts lengths live last refuted → starts.size = 256 → lengths.size = 256 → live.size = 256 →
      mapped.size = 256 → proposed.size = 4096 → scratch.size = 64 →
      c.toNat ≤ commands.size → 8801 + (commands.size - c.toNat) < fuel →
      ∃ (starts' lengths' mapped' proposed' : Array UInt32) (live' : Array Bool) (scratch' : Array UInt8)
        (valid' refuted' : Bool) (last' c' : UInt32),
        rup_stream_check.loop4 pool refs commands variables starts lengths live mapped proposed scratch true refuted
          last c fuel = some (starts', lengths', live', mapped', proposed', scratch', valid', refuted', last', c') ∧
        (valid' && refuted') = (match CertifiedStream.commands raw s (raw.commands.drop c.toNat) with
          | none => false
          | some s' => s'.refuted) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro c s starts lengths mapped proposed live scratch last refuted hrel hss hls hvs hms hps hcs hc hf
    obtain ⟨htable, hlast, href⟩ := hrel
    rw [rup_stream_check.loop4]
    have hcsz : commands.size.toUInt32.toNat = commands.size := toNat_size32 commands.size (by
      show commands.size < 4294967296; omega)
    by_cases hin : c.toNat < commands.size
    · have hlt : decide (c < commands.size.toUInt32) = true := by
        rw [decide_lt_toNat, hcsz]; exact decide_eq_true hin
      simp only [hlt, Bool.and_true, ite_true]
      have hsucc : (c + 1).toNat = c.toNat + 1 := toNat_succ c (by omega)
      have hcl : c.toNat < raw.commands.length := by rw [← hcmds]; exact hin
      obtain ⟨hadd, hid, hstart, hcount, hrs, hrc⟩ := hcmd c.toNat hcl
      have hdrop : raw.commands.drop c.toNat = raw.commands[c.toNat] :: raw.commands.drop (c.toNat + 1) :=
        List.drop_eq_getElem_cons hcl
      rw [hdrop]
      simp only [CertifiedStream.commands]
      -- The exits with the flag down all take the same shape.
      have exit_false : ∀ (starts₁ lengths₁ mapped₁ proposed₁ : Array UInt32) (live₁ : Array Bool)
          (scratch₁ : Array UInt8) (refuted₁ : Bool) (last₁ : UInt32),
          ∃ (starts' lengths' mapped' proposed' : Array UInt32) (live' : Array Bool) (scratch' : Array UInt8)
            (valid' refuted' : Bool) (last' c' : UInt32),
            rup_stream_check.loop4 pool refs commands variables starts₁ lengths₁ live₁ mapped₁ proposed₁ scratch₁
              false refuted₁ last₁ (c + 1) fuel =
              some (starts', lengths', live', mapped', proposed', scratch', valid', refuted', last', c') ∧
            (valid' && refuted') = false := by
        intro starts₁ lengths₁ mapped₁ proposed₁ live₁ scratch₁ refuted₁ last₁
        obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        rw [hfe, stream_loop4_invalid]
        exact ⟨_, _, _, _, _, _, false, refuted₁, last₁, c + 1, rfl, rfl⟩
      -- The id bound.
      have hg1 : decide ((commands.getD c.toNat default).id_ <= 2147483647) =
          decide (¬ raw.commands[c.toNat].id > 2147483647) := by
        rw [decide_le_toNat, toNat_ofNat32 2147483647 (by decide), hid]
        exact decide_eq_decide.mpr (by omega)
      rw [hg1]
      by_cases h1 : raw.commands[c.toNat].id > 2147483647
      · rw [decide_eq_false (not_not_intro h1), Bool.false_and, Bool.false_and]
        simp only [Bool.false_eq_true, ite_false, pure, bind, Option.bind]
        rw [command_id_big raw s _ h1]
        exact exit_false _ _ _ _ _ _ _ _
      rw [decide_eq_true h1, Bool.true_and]
      -- The reference range.
      have hg2 := range_check_eq refs hrsize (commands.getD c.toNat default).refs_start
        (commands.getD c.toNat default).refs_count
      rw [Bool.and_assoc, hg2, hrs, hrc]
      by_cases h2 : raw.commands[c.toNat].refsStart + raw.commands[c.toNat].refsCount ≤ refs.size
      · have hsafe : rangeSafe raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount refs.size :=
          (rangeSafe_refines _ _ _).mpr h2
        rw [decide_eq_true hsafe]
        simp only [ite_true, bind, Option.bind]
        have hread : readRange raw.refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount =
            some (clauseAt refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount) := by
          rw [← hrefs]; exact readRange_clauseAt refs _ _ h2
        rw [hadd]
        cases haddm : raw.commands[c.toNat].addition with
        | true =>
          simp only [ite_true]
          -- The addition guards.
          have hg3 : decide ((commands.getD c.toNat default).id_ > last) = decide (last.toNat < raw.commands[c.toNat].id) := by
            show decide (last < _) = _
            rw [decide_lt_toNat, hid]
          have hg4 : decide ((commands.getD c.toNat default).id_ <= 256) = decide (raw.commands[c.toNat].id ≤ 256) := by
            rw [decide_le_toNat, toNat_ofNat32 256 (by decide), hid]
          have hg5 := range_check_eq pool hpsize (commands.getD c.toNat default).start (commands.getD c.toNat default).count
          have hg6 : decide ((commands.getD c.toNat default).refs_count <= 256) = decide (raw.commands[c.toNat].refsCount ≤ 256) := by
            rw [decide_le_toNat, toNat_ofNat32 256 (by decide), hrc]
          have hg5' : (decide ((commands.getD c.toNat default).start <= pool.size.toUInt32) &&
                (decide ((commands.getD c.toNat default).count <= pool.size.toUInt32 - (commands.getD c.toNat default).start) &&
                  decide ((commands.getD c.toNat default).refs_count <= 256))) =
              (decide (rangeSafe raw.commands[c.toNat].start raw.commands[c.toNat].count pool.size) &&
                decide (raw.commands[c.toNat].refsCount ≤ 256)) := by
            rw [← Bool.and_assoc, hg5, hstart, hcount, hg6]
          rw [hg3, hg4]
          simp only [Bool.and_assoc]
          rw [hg5', ← Bool.and_assoc (decide (last.toNat < raw.commands[c.toNat].id)),
            ← Bool.decide_and (last.toNat < raw.commands[c.toNat].id) (raw.commands[c.toNat].id ≤ 256)]
          by_cases hA : last.toNat < raw.commands[c.toNat].id ∧ raw.commands[c.toNat].id ≤ 256
          · rw [decide_eq_true hA, Bool.true_and]
            have hA' : s.last < raw.commands[c.toNat].id ∧ raw.commands[c.toNat].id ≤ 256 := by rw [hlast]; exact hA
            by_cases hC : raw.commands[c.toNat].refsCount ≤ 256
            · rw [decide_eq_true hC, Bool.and_true]
              by_cases hB : rangeSafe raw.commands[c.toNat].start raw.commands[c.toNat].count pool.size
              · rw [decide_eq_true hB]
                have hB' := (rangeSafe_refines _ _ _).mp hB
                -- The hint mapping.
                obtain ⟨mapped', h', hrun5, hms', hget5⟩ := stream_loop5_spec refs live (commands.getD c.toNat default)
                  (by rw [hrs, hrc]; exact h2) hrsize (by rw [hrc]; exact hC) fuel mapped 0 (Nat.zero_le _)
                  (by rw [UInt32.toNat_zero]; omega) (by rw [hrc, hms]; exact hC)
                simp only [UInt32.toNat_zero, Nat.sub_zero] at hrun5 hget5
                rw [hrun5]
                simp only []
                rw [hrs, hrc, refs_all_eq s.table starts lengths live htable refs _ _ h2] at hrun5 hget5 ⊢
                cases hall : (clauseAt refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount).all
                    (fun id => decide (0 < id ∧ id ≤ 256) && (s.table (id - 1)).live) with
                | false =>
                  obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
                  rw [hfe, stream_loop6_invalid]
                  simp only [Bool.false_eq_true, ite_false, pure]
                  rw [← hfe, command_add_dead raw s _ h1 _ hread haddm hA' (by omega) hall]
                  exact exit_false _ _ _ _ _ _ _ _
                | true =>
                  have hget5' := hget5 hall
                  -- The clause copy.
                  obtain ⟨proposed', p', hrun6, hps', hget6⟩ := stream_loop6_spec pool proposed (commands.getD c.toNat default)
                    (by rw [hstart, hcount]; exact hB') hpsize (by rw [hcount, hps]; omega) fuel 0 (Nat.zero_le _)
                    (by rw [UInt32.toNat_zero]; omega)
                  simp only [UInt32.toNat_zero, Nat.zero_le, true_and] at hget6
                  rw [hrun6]
                  simp only [ite_true]
                  -- The kernel.
                  have htl : targetList proposed' (commands.getD c.toNat default).count.toNat =
                      clauseAt pool raw.commands[c.toNat].start raw.commands[c.toNat].count := by
                    rw [hcount, ← hstart]
                    apply targetList_copy pool proposed' _ _ (by rw [hstart]; exact hB') (by rw [hps', hps]; omega)
                    intro q hq
                    rw [hget6 q, if_pos (by rw [hcount]; exact hq)]
                  have hpos := refs_all_pos live refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount
                    (by rw [refs_all_eq s.table starts lengths live htable refs _ _ h2]; exact hall)
                  have hhl : (hintList mapped' (commands.getD c.toNat default).refs_count.toNat).map (· + 1) =
                      clauseAt refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount := by
                    rw [hrc]
                    apply hintList_mapped_eq refs mapped' _ _ h2 (by rw [hms', hms]; exact hC)
                    · intro k hk
                      rw [hget5' k]
                      simp [hk]
                    · exact hpos
                  have hclause : readClause raw.pool raw.commands[c.toNat].start raw.commands[c.toNat].count =
                      some ((clauseAt pool raw.commands[c.toNat].start raw.commands[c.toNat].count).map decodeLiteral) := by
                    unfold readClause
                    rw [← hpool, readRange_clauseAt pool _ _ hB']
                    rfl
                  obtain ⟨scratch', hrunk, hcs'⟩ := rup_check_spec pool starts lengths proposed' mapped' scratch
                    (commands.getD c.toNat default).count (commands.getD c.toNat default).refs_count variables s.table live
                    fuel hpsize hpvars hss hls hcs (by rw [hps', hps, hcount]; omega) (by rw [hps', hps]; exact Nat.le_refl _)
                    (by rw [htl]; exact clauseAt_mem_bound pool _ _ (fun n => n / 2 < variables.toNat) hpvars)
                    (by rw [hms', hms, hrc]; exact hC) (by rw [hms', hms]; omega) (by rw [hrc]; exact hC)
                    (by
                      intro i hi
                      have hi' : i < raw.commands[c.toNat].refsCount := by rw [← hrc]; exact hi
                      rw [hget5' i, if_pos ⟨Nat.zero_le _, hi'⟩]
                      have hok := List.all_eq_true.mp hall (refs.getD (raw.commands[c.toNat].refsStart + i) 0).toNat (by
                        rw [← clauseAt_getElem refs _ _ i hi' h2]
                        exact List.getElem_mem _)
                      rw [Bool.and_eq_true, decide_eq_true_eq] at hok
                      rw [toNat_sub_of_le' _ _ (by rw [UInt32.toNat_one]; exact hpos i hi'), UInt32.toNat_one]
                      refine ⟨by omega, ?_⟩
                      have := htable ((refs.getD (raw.commands[c.toNat].refsStart + i) 0).toNat - 1) (by omega)
                      rw [this] at hok
                      exact hok.2)
                    htable (by omega)
                  rw [hrunk]
                  simp only [pure]
                  rw [htl, hhl, hpool, hvar]
                  obtain ⟨hiso, hfields⟩ := command_add_check raw s _ h1 _ hread haddm hA' (by omega) hall _ hclause
                  rw [← hiso]
                  cases hcmdr : command raw s raw.commands[c.toNat] with
                  | none =>
                    simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
                    exact exit_false _ _ _ _ _ _ _ _
                  | some s' =>
                    simp only [Option.isSome_some, ite_true]
                    obtain ⟨ht', hl', hr'⟩ := hfields s' hcmdr
                    have hslot : ((commands.getD c.toNat default).id_ - 1).toNat = raw.commands[c.toNat].id - 1 := by
                      rw [toNat_sub_of_le' _ _ (by rw [UInt32.toNat_one, hid]; omega), UInt32.toNat_one, hid]
                    have hrel' : StreamRel s' (starts.setIfInBounds ((commands.getD c.toNat default).id_ - 1).toNat
                        (commands.getD c.toNat default).start)
                        (lengths.setIfInBounds ((commands.getD c.toNat default).id_ - 1).toNat
                          (commands.getD c.toNat default).count)
                        (live.setIfInBounds ((commands.getD c.toNat default).id_ - 1).toNat true)
                        (commands.getD c.toNat default).id_
                        (refuted || ((commands.getD c.toNat default).count == 0)) := by
                      refine ⟨?_, by rw [hl', hid], ?_⟩
                      · rw [ht', hslot, ← hstart, ← hcount]
                        exact tableRel_publish s.table starts lengths live htable hss hls hvs _ _ _
                      · rw [hr', href, clause_empty_iff pool _ _ hB', beq_zero_eq, hcount]
                    obtain ⟨st2, le2, ma2, pr2, li2, sc2, v2, r2, la2, c2, hrun2, hres2⟩ := ih (c + 1) s' _ _ mapped' proposed' _
                      scratch' _ _ hrel' (by rw [size_set]; exact hss) (by rw [size_set]; exact hls)
                      (by rw [size_setB]; exact hvs) (by rw [hms', hms]) (by rw [hps', hps]) (by rw [hcs', hcs])
                      (by omega) (by omega)
                    rw [hsucc] at hres2
                    exact ⟨st2, le2, ma2, pr2, li2, sc2, v2, r2, la2, c2, hrun2, hres2⟩
              · rw [decide_eq_false hB]
                obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
                rw [hfe, stream_loop5_invalid]
                simp only []
                rw [stream_loop6_invalid]
                simp only [Bool.false_eq_true, ite_false, pure]
                have hnone : command raw s raw.commands[c.toNat] = none := by
                  have hc' : readClause raw.pool raw.commands[c.toNat].start raw.commands[c.toNat].count = none := by
                    unfold readClause
                    rw [← hpool, readRange_none pool _ _ (fun h => hB ((rangeSafe_refines _ _ _).mpr h))]
                    rfl
                  cases hall : (clauseAt refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount).all
                      (fun id => decide (0 < id ∧ id ≤ 256) && (s.table (id - 1)).live) with
                  | false => exact command_add_dead raw s _ h1 _ hread haddm hA' (by omega) hall
                  | true => exact command_add_noclause raw s _ h1 _ hread haddm hA' (by omega) hall hc'
                rw [← hfe, hnone]
                exact exit_false _ _ _ _ _ _ _ _
            · rw [decide_eq_false hC, Bool.and_false]
              obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
              rw [hfe, stream_loop5_invalid]
              simp only []
              rw [stream_loop6_invalid]
              simp only [Bool.false_eq_true, ite_false, pure]
              rw [← hfe, command_add_many raw s _ h1 _ hread haddm hA' (by omega)]
              exact exit_false _ _ _ _ _ _ _ _
          · rw [decide_eq_false hA, Bool.false_and]
            obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [hfe, stream_loop5_invalid]
            simp only []
            rw [stream_loop6_invalid]
            simp only [Bool.false_eq_true, ite_false, pure]
            rw [← hfe, command_add_stale raw s _ h1 _ hread haddm (by rw [hlast]; exact hA)]
            exact exit_false _ _ _ _ _ _ _ _
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          rw [command_delete raw s _ h1 _ hread haddm]
          have hg7 : decide ((commands.getD c.toNat default).id_ >= last) = decide (¬ raw.commands[c.toNat].id < s.last) := by
            show decide (last <= _) = _
            rw [decide_le_toNat, hid, hlast]
            exact decide_eq_decide.mpr (by omega)
          rw [hg7]
          by_cases hD : raw.commands[c.toNat].id < s.last
          · rw [decide_eq_false (not_not_intro hD), if_pos hD]
            obtain ⟨f, hfe⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [hfe, stream_loop7_invalid]
            simp only [pure]
            rw [← hfe]
            exact exit_false _ _ _ _ _ _ _ _
          · rw [decide_eq_true hD, if_neg hD]
            obtain ⟨d', hrun7⟩ := stream_loop7_spec refs (commands.getD c.toNat default) (by rw [hrs, hrc]; exact h2)
              hrsize fuel live 0 (Nat.zero_le _) (by rw [UInt32.toNat_zero]; omega)
            simp only [UInt32.toNat_zero, List.drop_zero] at hrun7
            rw [hrun7, hrs, hrc]
            simp only [pure]
            obtain ⟨hiso, hfields⟩ := deleteIDs_clearAll (clauseAt refs raw.commands[c.toNat].refsStart
              raw.commands[c.toNat].refsCount) s starts lengths live htable hvs
            cases hdel : deleteIDs s (clauseAt refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount) with
            | none =>
              rw [hdel] at hiso
              simp only [Option.isSome_none] at hiso
              rw [← hiso]
              exact exit_false _ _ _ _ _ _ _ _
            | some s' =>
              rw [hdel] at hiso
              simp only [Option.isSome_some] at hiso
              rw [← hiso]
              obtain ⟨ht', hl', hr'⟩ := hfields s' hdel
              have hrel' : StreamRel s' starts lengths
                  (clearAll live (clauseAt refs raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount)).2
                  last refuted := ⟨ht', by rw [hl', hlast], by rw [hr', href]⟩
              obtain ⟨st2, le2, ma2, pr2, li2, sc2, v2, r2, la2, c2, hrun2, hres2⟩ := ih (c + 1) s' starts lengths mapped
                proposed _ scratch last refuted hrel' hss hls (by rw [clearAll_size]; exact hvs) hms hps hcs
                (by omega) (by omega)
              rw [hsucc] at hres2
              exact ⟨st2, le2, ma2, pr2, li2, sc2, v2, r2, la2, c2, hrun2, hres2⟩
      · have hsafe : ¬ rangeSafe raw.commands[c.toNat].refsStart raw.commands[c.toNat].refsCount refs.size :=
          fun h => h2 ((rangeSafe_refines _ _ _).mp h)
        rw [decide_eq_false hsafe]
        simp only [Bool.false_eq_true, ite_false, pure, bind, Option.bind]
        rw [command_refs_none raw s _ h1 (by rw [← hrefs]; exact readRange_none refs _ _ h2)]
        exact exit_false _ _ _ _ _ _ _ _
    · have hlt : decide (c < commands.size.toUInt32) = false := by
        rw [decide_lt_toNat, hcsz]; exact decide_eq_false hin
      simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
      have hnil : raw.commands.drop c.toNat = [] := List.drop_eq_nil_of_le (by rw [← hcmds]; omega)
      rw [hnil]
      simp only [CertifiedStream.commands]
      exact ⟨starts, lengths, mapped, proposed, live, scratch, true, refuted, last, c, rfl, href.symm⟩

/-! ## The initial table, as the model builds it -/

theorem initialOK_eq (pool initial sizes : Array UInt32) (hlen : initial.size = sizes.size) :
    initialOK pool initial sizes 0 initial.size =
      ((toNats initial).zip (toNats sizes)).all (fun r => (readRange (toNats pool) r.1 r.2).isSome) := by
  apply Bool.eq_iff_iff.mpr
  unfold initialOK
  rw [Nat.sub_zero, List.all_eq_true, List.all_eq_true]
  have hz : ((toNats initial).zip (toNats sizes)).length = initial.size := by
    rw [List.length_zip, toNats_length, toNats_length, hlen, Nat.min_self]
  constructor
  · intro h r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    rw [hz] at hk
    have := h k (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
    rw [decide_eq_true_eq, rangeSafe_refines] at this
    rw [List.getElem_zip, ← getD_toNats_of_lt initial k hk, ← getD_toNats,
      ← getD_toNats_of_lt sizes k (by omega), ← getD_toNats, readRange_clauseAt pool _ _ this]
    rfl
  · intro h k hk
    have hk' : k < initial.size := by have := List.mem_range'_1.mp hk; omega
    have := h (((toNats initial).zip (toNats sizes))[k]'(by rw [hz]; exact hk')) (List.getElem_mem _)
    rw [List.getElem_zip, ← getD_toNats_of_lt initial k hk', ← getD_toNats,
      ← getD_toNats_of_lt sizes k (by omega), ← getD_toNats] at this
    rw [decide_eq_true_eq, rangeSafe_refines]
    apply Classical.byContradiction
    intro hbig
    rw [readRange_none pool _ _ hbig] at this
    cases this

theorem tableRel_initial (initial sizes starts lengths : Array UInt32) (live : Array Bool)
    (hlen : initial.size = sizes.size)
    (hgs : ∀ v, starts.getD v 0 = if v < initial.size then initial.getD v 0 else 0)
    (hgl : ∀ v, lengths.getD v 0 = if v < initial.size then sizes.getD v 0 else 0)
    (hgv : ∀ v, live.getD v false = if v < initial.size then true else false) :
    TableRel (LiveTable.initialTable ((toNats initial).zip (toNats sizes))) starts lengths live := by
  intro slot _
  unfold LiveTable.initialTable
  rw [hgs slot, hgl slot, hgv slot]
  by_cases hs : slot < initial.size
  · rw [List.getElem?_eq_getElem (by rw [List.length_zip, toNats_length, toNats_length, hlen, Nat.min_self]; omega)]
    simp only [List.getElem_zip, hs, ite_true]
    rw [← getD_toNats_of_lt initial slot hs, ← getD_toNats, ← getD_toNats_of_lt sizes slot (by omega), ← getD_toNats]
  · rw [List.getElem?_eq_none (by rw [List.length_zip, toNats_length, toNats_length, hlen, Nat.min_self]; omega)]
    simp only [hs, ite_false]
    rfl

theorem initial_refuted_eq (pool initial sizes : Array UInt32) (hlen : initial.size = sizes.size)
    (hok : initialOK pool initial sizes 0 initial.size = true) :
    (List.range' 0 initial.size).any (fun k => decide ((sizes.getD k 0).toNat = 0)) =
      ((List.range initial.size).map (· + 1)).any (fun id =>
        decide (LiveTable.database (toNats pool) (LiveTable.initialTable ((toNats initial).zip (toNats sizes))) id = some [])) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  unfold initialOK at hok
  rw [Nat.sub_zero, List.all_eq_true] at hok
  have key : ∀ k, k < initial.size →
      (LiveTable.database (toNats pool) (LiveTable.initialTable ((toNats initial).zip (toNats sizes))) (k + 1) = some [] ↔
        (sizes.getD k 0).toNat = 0) := by
    intro k hk
    have hsafe := hok k (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
    rw [decide_eq_true_eq, rangeSafe_refines] at hsafe
    unfold LiveTable.database
    rw [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
    unfold LiveTable.initialTable
    rw [List.getElem?_eq_getElem (by rw [List.length_zip, toNats_length, toNats_length, hlen, Nat.min_self]; omega)]
    simp only [List.getElem_zip]
    rw [← getD_toNats_of_lt initial k hk, ← getD_toNats, ← getD_toNats_of_lt sizes k (by omega), ← getD_toNats]
    unfold LiveTable.meaning
    simp only [ite_true]
    unfold readClause
    rw [readRange_clauseAt pool _ _ hsafe, Option.map_some, Option.some_inj, List.map_eq_nil_iff,
      ← List.length_eq_zero_iff, clauseAt_length pool _ _ hsafe]
  constructor
  · rintro ⟨k, hk, hz⟩
    have hk' : k < initial.size := by have := List.mem_range'_1.mp hk; omega
    refine ⟨k + 1, List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩, ?_⟩
    rw [decide_eq_true_eq, key k hk']
    exact decide_eq_true_eq.mp hz
  · rintro ⟨id, hid, hz⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hid
    have hk' := List.mem_range.mp hk
    refine ⟨k, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, ?_⟩
    rw [decide_eq_true_eq]
    exact (key k hk').mp (decide_eq_true_eq.mp hz)

/-! ## The stream checker -/

/-- The stream theorem: on every layout the decoder can hand over, with the
arrays inside the fixed capacities and fuel above 9100, the extracted
`rup_stream_check` returns exactly the certified model's decision. -/
theorem rup_stream_check_spec (raw : Layout) (variables : UInt32) (pool initial sizes refs : Array UInt32)
    (commands : Array RUPCommand) (fuel : Nat)
    (hrel : LayoutRel raw variables pool initial sizes refs commands)
    (hpsize : pool.size ≤ 4096) (hisize : initial.size ≤ 256) (hssize : sizes.size ≤ 256)
    (hrsize : refs.size ≤ 4096) (hcsize : commands.size ≤ 256) (hfuel : 9100 < fuel) :
    rup_stream_check pool initial sizes refs commands variables fuel = some (CertifiedStream.check raw) := by
  obtain ⟨hvar, hplen, hpget, hilen, higet, hslen, hsget, hrlen, hrget, hclen, hcmd⟩ := hrel
  have hpool : toNats pool = raw.pool := toNats_eq_of_rel pool raw.pool hplen hpget
  have hinit : toNats initial = raw.starts := toNats_eq_of_rel initial raw.starts hilen higet
  have hsizes : toNats sizes = raw.sizes := toNats_eq_of_rel sizes raw.sizes hslen hsget
  have hrefs : toNats refs = raw.refs := toNats_eq_of_rel refs raw.refs hrlen hrget
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  unfold rup_stream_check
  -- The resource guards.
  have hg0 : decide (variables > (0 : UInt32)) = decide (0 < variables.toNat) := by
    show decide ((0 : UInt32) < variables) = _
    rw [decide_lt_toNat, UInt32.toNat_zero]
  have hg1 : decide (variables <= (64 : UInt32)) = decide (variables.toNat ≤ 64) := by
    rw [decide_le_toNat, toNat_ofNat32 64 (by decide)]
  have hg2 : decide (pool.size.toUInt32 <= (4096 : UInt32)) = true := by
    rw [decide_le_toNat, toNat_size32 pool.size (by show pool.size < 4294967296; omega), toNat_ofNat32 4096 (by decide)]
    exact decide_eq_true hpsize
  have hg3 : decide (refs.size.toUInt32 <= (4096 : UInt32)) = true := by
    rw [decide_le_toNat, toNat_size32 refs.size (by show refs.size < 4294967296; omega), toNat_ofNat32 4096 (by decide)]
    exact decide_eq_true hrsize
  have hg4 : (initial.size.toUInt32 == sizes.size.toUInt32) = decide (initial.size = sizes.size) := by
    rw [beq_toNat32, toNat_size32 initial.size (by show initial.size < 4294967296; omega),
      toNat_size32 sizes.size (by show sizes.size < 4294967296; omega)]
  have hg5 : decide (initial.size.toUInt32 <= (256 : UInt32)) = true := by
    rw [decide_le_toNat, toNat_size32 initial.size (by show initial.size < 4294967296; omega), toNat_ofNat32 256 (by decide)]
    exact decide_eq_true hisize
  have hg6 : decide (commands.size.toUInt32 <= (256 : UInt32)) = true := by
    rw [decide_le_toNat, toNat_size32 commands.size (by show commands.size < 4294967296; omega),
      toNat_ofNat32 256 (by decide)]
    exact decide_eq_true hcsize
  rw [hg0, hg1, hg2, hg3, hg4, hg5, hg6]
  simp only [Bool.and_true]
  -- Loop 1 builds the empty table.
  obtain ⟨s1, l1, v1, i1, hrun1, hs1, hl1, hv1, hgs1, hgl1, hgv1⟩ := stream_loop1_spec (Array.replicate 256 0)
    (Array.replicate 256 0) (Array.replicate 256 false) (f + 1) 0 (Nat.zero_le _) (by rw [UInt32.toNat_zero]; omega)
  rw [hrun1]
  simp only [bind, Option.bind]
  rw [Array.size_replicate] at hs1 hl1 hv1
  simp only [UInt32.toNat_zero, Nat.zero_le, true_and] at hgs1 hgl1 hgv1
  have hdead : ∀ v, s1.getD v 0 = 0 ∧ l1.getD v 0 = 0 ∧ v1.getD v false = false := by
    intro v
    rw [hgs1 v, hgl1 v, hgv1 v]
    by_cases hv : v < 256
    · simp [hv]
    · simp only [hv, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_replicate]; omega)]; rfl
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_replicate]; omega)]; rfl
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_replicate]; omega)]; rfl
  -- The model's guard.
  have hguard : (0 < raw.variables ∧ raw.variables ≤ 64 ∧ raw.pool.length ≤ 4096 ∧ raw.refs.length ≤ 4096 ∧
      raw.starts.length = raw.sizes.length ∧ raw.starts.length ≤ 256 ∧ raw.commands.length ≤ 256) ↔
      (0 < variables.toNat ∧ variables.toNat ≤ 64 ∧ initial.size = sizes.size) := by
    rw [hvar, ← hplen, ← hrlen, ← hilen, ← hslen, ← hclen]
    constructor
    · intro h; exact ⟨h.1, h.2.1, h.2.2.2.2.1⟩
    · intro h; exact ⟨h.1, h.2.1, hpsize, hrsize, h.2.2, hisize, hcsize⟩
  unfold CertifiedStream.check CertifiedStream.run
  by_cases hv : 0 < variables.toNat ∧ variables.toNat ≤ 64 ∧ initial.size = sizes.size
  · obtain ⟨hv0, hv64, hlen⟩ := hv
    rw [if_neg (not_not_intro (hguard.mpr ⟨hv0, hv64, hlen⟩))]
    rw [decide_eq_true hv0, decide_eq_true hv64, decide_eq_true hlen]
    simp only [Bool.and_self]
    -- Loop 2 checks the literals.
    obtain ⟨i2, hrun2⟩ := stream_loop2_spec pool variables hpsize (f + 1) 0 (Nat.zero_le _)
      (by rw [UInt32.toNat_zero]; omega)
    rw [UInt32.toNat_zero, Nat.sub_zero, pool_all_eq, hpool, hvar] at hrun2
    rw [hrun2]
    simp only []
    cases hall : raw.pool.all (fun n => decide (n / 2 < raw.variables)) with
    | false =>
      rw [stream_loop3_invalid]
      simp only []
      rw [stream_loop4_invalid]
      simp only [Bool.false_and, pure, Bool.not_false, ite_true]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      -- Loop 3 installs the initial clauses.
      obtain ⟨s3, l3, v3, i3, r3, hrun3, hs3, hl3, hv3, hrest3⟩ := stream_loop3_spec pool initial sizes hpsize hisize
        (f + 1) s1 l1 v1 0 false (by rw [hs1]; exact hisize) (by rw [hl1]; exact hisize) (by rw [hv1]; exact hisize)
        (Nat.zero_le _) (by rw [UInt32.toNat_zero]; omega)
      rw [UInt32.toNat_zero] at hrun3 hrest3
      rw [hrun3]
      simp only []
      rw [initialOK_eq pool initial sizes hlen, hinit, hsizes, hpool] at hrun3 hrest3 ⊢
      cases hok : (raw.starts.zip raw.sizes).all (fun r => (readRange raw.pool r.1 r.2).isSome) with
      | false =>
        rw [stream_loop4_invalid]
        simp only [Bool.false_and, pure, Bool.not_false, ite_true]
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        obtain ⟨hgs3, hgl3, hgv3, hr3⟩ := hrest3 hok
        simp only [Nat.zero_le, true_and, Nat.sub_zero] at hgs3 hgl3 hgv3 hr3
        -- The loop's state represents the model's initial state.
        obtain ⟨hit, hil, hir⟩ := initialState_fields raw
        have hrel0 : StreamRel (CertifiedStream.initialState raw) s3 l3 v3 initial.size.toUInt32 r3 := by
          refine ⟨?_, ?_, ?_⟩
          · rw [hit, ← hinit, ← hsizes]
            apply tableRel_initial initial sizes s3 l3 v3 hlen
            · intro v; rw [hgs3 v]; by_cases hv : v < initial.size <;> simp [hv, (hdead v).1]
            · intro v; rw [hgl3 v]; by_cases hv : v < initial.size <;> simp [hv, (hdead v).2.1]
            · intro v; rw [hgv3 v]; by_cases hv : v < initial.size <;> simp [hv, (hdead v).2.2]
          · rw [hil, toNat_size32 initial.size (by show initial.size < 4294967296; omega), hilen]
          · have hre := initial_refuted_eq pool initial sizes hlen (by
              rw [initialOK_eq pool initial sizes hlen, hinit, hsizes, hpool]; exact hok)
            rw [hir, hr3, Bool.false_or, ← hilen]
            unfold origin
            rw [← hinit, ← hsizes, ← hpool]
            exact hre.symm
        -- Loop 4 runs the commands.
        obtain ⟨s4, l4, m4, p4, v4, sc4, valid4, r4, la4, c4, hrun4, hres4⟩ := stream_loop4_spec raw variables pool refs
          commands hvar hpool hrefs hclen hcmd hpsize hrsize hcsize
          (by
            intro i hi
            have hmem : (pool.getD i 0).toNat ∈ raw.pool := by
              rw [← hpool, getD_toNats, getD_toNats_of_lt pool i hi]
              exact List.getElem_mem _
            have := List.all_eq_true.mp hall _ hmem
            rw [decide_eq_true_eq, ← hvar] at this
            exact this)
          (f + 1) 0 (CertifiedStream.initialState raw) s3 l3 (Array.replicate 256 0) (Array.replicate 4096 0) v3
          (Array.replicate 64 0) initial.size.toUInt32 r3 hrel0 (by rw [hs3, hs1]) (by rw [hl3, hl1]) (by rw [hv3, hv1])
          (Array.size_replicate) (Array.size_replicate) (Array.size_replicate) (Nat.zero_le _)
          (by rw [UInt32.toNat_zero]; omega)
        rw [UInt32.toNat_zero, List.drop_zero] at hres4
        rw [hrun4]
        simp only [pure]
        rw [hres4]
        cases CertifiedStream.commands raw (CertifiedStream.initialState raw) raw.commands <;> rfl
  · rw [if_pos (fun h => hv (hguard.mp h))]
    have hfalse : (decide (0 < variables.toNat) && decide (variables.toNat ≤ 64) && decide (initial.size = sizes.size)) = false := by
      rcases Bool.eq_false_or_eq_true (decide (0 < variables.toNat) && decide (variables.toNat ≤ 64) &&
          decide (initial.size = sizes.size)) with hb | hb
      · exfalso
        apply hv
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hb
        exact ⟨hb.1.1, hb.1.2, hb.2⟩
      · exact hb
    rw [hfalse, stream_loop2_invalid]
    simp only []
    rw [stream_loop3_invalid]
    simp only []
    rw [stream_loop4_invalid]
    simp only [Bool.false_and, pure]

/-! ## End to end -/

/-- The extracted text checker accepts only refutations: whenever
`rup_text_check` returns `true` on a pair of texts below the `UInt32` range
with enough fuel, the model's layout of those texts exists and its initial
database is unsatisfiable (`CertifiedStream.check_sound`). -/
theorem rup_text_check_sound (cnf proof : Array UInt8) (hc : cnf.size < UInt32.size) (hp : proof.size < UInt32.size)
    (fuel : Nat) (hf : 2 * cnf.size + 2 * proof.size + 9101 < fuel)
    (haccept : rup_text_check cnf proof fuel = some true) :
    ∃ raw : Layout, layoutBytes (toBytes cnf) (toBytes proof) = some raw ∧ Unsatisfiable (origin raw) := by
  obtain ⟨valid, variables, pool, initial, sizes, refs, commands, hrun, _, hyes, hpb, hib, hsb, hrb, hcb⟩ :=
    rup_text_check_spec cnf proof hc hp fuel (by omega)
  cases valid with
  | false =>
    rw [hrun] at haccept
    simp at haccept
  | true =>
    obtain ⟨raw, hlayout, hrel⟩ := hyes rfl
    refine ⟨raw, hlayout, ?_⟩
    rw [hrun, if_pos rfl, rup_stream_check_spec raw variables pool initial sizes refs commands fuel hrel hpb hib hsb hrb
      hcb (by omega)] at haccept
    exact CertifiedStream.check_sound raw (Option.some_inj.mp haccept)

#print axioms rup_stream_check_spec
#print axioms rup_text_check_sound
end OakVerification.Extraction
