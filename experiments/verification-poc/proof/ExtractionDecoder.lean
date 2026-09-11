import OakText
import ExtractionScanner

set_option autoImplicit false
namespace OakVerification.Extraction
open Scanner Ranges CertificateFile Extracted

/-! The extracted decoder refines the hand-written transliteration
(docs/spec/95-extraction.md, roadmap step 3's third increment). `OakText`
restates `rup_text_check` structure for structure over lists; the compiler's
extraction `Extracted.rup_text_check` computes over `UInt32` and `Array`.
This file relates the two, phase by phase, on top of `rup_token_scan`: the
DIMACS loop against `cnfLoop`, so that `OakTextRefinement.check_refines`
reaches the extraction without a second corpus hop. -/

/-! ## Small facts about the extracted operations -/

theorem toNat_sub_of_le' (a b : UInt32) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt32.toNat_sub_of_le]
  exact UInt32.le_iff_toNat_le.mpr h

theorem le_iff_toNat (a b : UInt32) : (decide (a <= b) = true) ↔ a.toNat ≤ b.toNat := by
  rw [decide_eq_true_iff, UInt32.le_iff_toNat_le]

theorem lt_iff_toNat (a b : UInt32) : (decide (a < b) = true) ↔ a.toNat < b.toNat := by
  rw [decide_eq_true_iff, UInt32.lt_iff_toNat_lt]

theorem decide_le_toNat (a b : UInt32) : decide (a <= b) = decide (a.toNat ≤ b.toNat) :=
  decide_eq_decide.mpr UInt32.le_iff_toNat_le

theorem decide_lt_toNat (a b : UInt32) : decide (a < b) = decide (a.toNat < b.toNat) :=
  decide_eq_decide.mpr UInt32.lt_iff_toNat_lt

theorem beq_toNat8 (a b : UInt8) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [beq_eq_false_iff_ne.mpr hab, decide_eq_false (fun h => hab (UInt8.toNat_inj.mp h))]

theorem bne_ofNat32 (a : UInt32) (n : Nat) (hn : n < UInt32.size) :
    (a != (OfNat.ofNat n : UInt32)) = !(a.toNat == n) := by
  rw [bne, beq_ofNat32 a n hn]

/-- Every token the scanner returns has a magnitude within the decimal limit. -/
theorem scan_magnitude_le (bytes : List Nat) (pos : Nat) :
    (scan bytes pos).magnitude ≤ Decimal.limit := by
  unfold scan scanTail tokenAt
  split
  · simp
  · rename_i b bs
    split
    · simp
    · simp only
      unfold numeric
      split
      rename_i tag ds heq
      split
      · simp
      · simp only
        exact (walk_bounds 0 ds (Nat.zero_le _)).2.1

/-- `rup_word` decides the model's `Word`, given the scanner state of a token
in range: start and stop are the token's, and a one-byte token whose byte is
`ch` is exactly `Word`. -/
theorem rup_word_spec (text : Array UInt8) (state : Array UInt32) (ch : UInt8) (fuel : Nat)
    (t : Token)
    (hstart : (state.getD 1 0).toNat = t.start) (hstop : (state.getD 2 0).toNat = t.stop)
    (hrange : t.start ≤ t.stop ∧ t.stop ≤ text.size) :
    rup_word text state ch fuel = some (decide (Word (toBytes text) t ch.toNat)) := by
  unfold rup_word
  simp only [pure, Option.some.injEq]
  have hsub : ((state.getD 2 0) - (state.getD 1 0)).toNat = t.stop - t.start := by
    rw [toNat_sub_of_le' _ _ (by omega), hstart, hstop]
  rw [beq_toNat32, hsub, toNat_ofNat32 1 (by decide)]
  by_cases hone : t.stop - t.start = 1
  · rw [decide_eq_true hone, Bool.true_and, beq_toNat8, getD_toBytes, hstart]
    have hin : t.start < text.size := by omega
    rw [getD_toBytes_of_lt text t.start hin]
    have hidx : (toBytes text)[t.start]? = some ((toBytes text)[t.start]'(by rw [toBytes_length]; exact hin)) :=
      List.getElem?_eq_getElem _
    apply decide_eq_decide.mpr
    constructor
    · intro hb
      exact ⟨by omega, by rw [hidx, hb]⟩
    · intro ⟨_, hw⟩
      rw [hidx] at hw
      exact Option.some.inj hw
  · rw [decide_eq_false hone, Bool.false_and]
    symm
    apply decide_eq_false
    intro ⟨hw, _⟩
    omega

/-- `rup_encoded` is the model's packed literal, within `UInt32`, for the
magnitudes the decimal limit admits and a magnitude of at least one. -/
theorem rup_encoded_spec (magnitude sign : UInt32) (fuel : Nat)
    (hm : 1 ≤ magnitude.toNat) (hlimit : magnitude.toNat ≤ Decimal.limit) :
    ∃ e : UInt32, rup_encoded magnitude sign fuel = some e ∧
      e.toNat = OakText.encoded magnitude.toNat sign.toNat := by
  unfold rup_encoded
  have hlim : Decimal.limit = 2147483647 := rfl
  have hsub : (magnitude - 1).toNat = magnitude.toNat - 1 := by
    rw [toNat_sub_of_le' _ _ (by rw [toNat_ofNat32 1 (by decide)]; exact hm), toNat_ofNat32 1 (by decide)]
  have hmul : ((magnitude - 1) * 2).toNat = (magnitude.toNat - 1) * 2 := by
    rw [UInt32.toNat_mul, hsub, toNat_ofNat32 2 (by decide)]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hsign : sign = 1
  · subst hsign
    refine ⟨(magnitude - 1) * 2 + 1, ?_, ?_⟩
    · simp
    · rw [UInt32.toNat_add, hmul, toNat_ofNat32 1 (by decide), Nat.mod_eq_of_lt (by omega)]
      simp [OakText.encoded]
  · refine ⟨(magnitude - 1) * 2, ?_, ?_⟩
    · have hne : (sign == 1) = false := beq_eq_false_iff_ne.mpr hsign
      simp [hne]
    · rw [hmul]
      have : sign.toNat ≠ 1 := fun h => hsign (UInt32.toNat_inj.mp (by rw [h, toNat_ofNat32 1 (by decide)]))
      simp [OakText.encoded, this]


/-- Writes into the bounded arrays, read back through `getD`. -/
theorem getD_set_ne (a : Array UInt32) (i j : Nat) (v : UInt32) (hij : j ≠ i) :
    (a.setIfInBounds i v).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, hij.symm]

theorem getD_set_self (a : Array UInt32) (i : Nat) (v : UInt32) (hi : i < a.size) :
    (a.setIfInBounds i v).getD i 0 = v := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem size_set (a : Array UInt32) (i : Nat) (v : UInt32) : (a.setIfInBounds i v).size = a.size :=
  Array.size_setIfInBounds

/-- The model's lists grow by one at the end. -/
theorem list_getD_append_lt (l : List Nat) (x : Nat) (i : Nat) (hi : i < l.length) :
    (l ++ [x]).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem list_getD_append_self (l : List Nat) (x : Nat) : (l ++ [x]).getD l.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

/-- A byte of the text against a literal, as the model reads it. -/
theorem byte_eq (text : Array UInt8) (i : Nat) (n : Nat) (hn : n < 256) (hi : i < text.size) :
    (text.getD i 0 == (OfNat.ofNat n : UInt8)) = decide ((toBytes text)[i]? = some n) := by
  rw [beq_ofNat _ n hn, getD_toBytes, getD_toBytes_of_lt text i hi, beq_nat_decide]
  apply decide_eq_decide.mpr
  rw [List.getElem?_eq_getElem (by rw [toBytes_length]; exact hi)]
  constructor
  · intro h; rw [h]
  · intro h; exact Option.some.inj h

theorem bne_zero_decide (a : UInt32) (n : Nat) (h : a.toNat = n) : (a != 0) = decide (n ≠ 0) := by
  rw [bne_ofNat32 a 0 (by decide), h, beq_nat_decide, decide_not]

/-! ## The DIMACS phase -/

/-- The extracted DIMACS loop's state, bundled. -/
structure CnfExt where
  pool : Array UInt32
  initial : Array UInt32
  sizes : Array UInt32
  scan : Array UInt32
  valid : Bool
  stage : UInt32
  variables : UInt32
  expected : UInt32
  clauses : UInt32
  literals : UInt32
  pending : UInt32
  first : Bool
  comment : Bool
  done : Bool

/-- One run of the extracted loop from a bundled state. -/
def CnfExt.run (cnf : Array UInt8) (s : CnfExt) (fuel : Nat) :=
  rup_text_check.loop3 cnf s.pool s.initial s.sizes s.scan s.valid s.stage s.variables s.expected
    s.clauses s.literals s.pending s.first s.comment s.done fuel

/-- The loop's result tuple, as a bundled state. -/
def CnfExt.tuple (s : CnfExt) :=
  (s.pool, s.initial, s.sizes, s.scan, s.valid, s.stage, s.variables, s.expected, s.clauses,
    s.literals, s.pending, s.first, s.comment, s.done)

/-- The extracted state represents the model's `Cnf` at cursor `pos`: every
scalar agrees through `toNat`, the bounded arrays agree with the lists on the
prefix the counters name, and the bounds the writes rely on hold. -/
def CnfRel (cnf : Array UInt8) (s : CnfExt) (pos : Nat) (c : OakText.Cnf) : Prop :=
  s.scan.size = 5 ∧ (s.scan.getD 0 0).toNat = pos ∧
  s.pool.size = 4096 ∧ s.initial.size = 256 ∧ s.sizes.size = 256 ∧
  s.valid = c.valid ∧ s.stage.toNat = c.stage ∧ s.variables.toNat = c.variables ∧
  s.expected.toNat = c.expected ∧ s.clauses.toNat = c.clauses ∧
  s.literals.toNat = c.pool.length ∧ s.pending.toNat = c.pending ∧
  s.first = c.first ∧ s.comment = c.comment ∧
  c.pending ≤ c.pool.length ∧ c.pool.length ≤ 4096 ∧
  c.initial.length = c.clauses ∧ c.sizes.length = c.clauses ∧
  c.expected ≤ Decimal.limit ∧
  (c.valid = true → 4 ≤ c.stage → c.expected ≤ 256) ∧
  (∀ i, i < c.pool.length → (s.pool.getD i 0).toNat = c.pool.getD i 0) ∧
  (∀ i, i < c.clauses → (s.initial.getD i 0).toNat = c.initial.getD i 0 ∧
    (s.sizes.getD i 0).toNat = c.sizes.getD i 0) ∧
  pos ≤ cnf.size


/-- The scanner theorem, restated over the bundled state: the extracted
`rup_token` returns the model's token at the relation's cursor. -/
theorem scan_step (cnf : Array UInt8) (hs : cnf.size ≤ 65536) (s : CnfExt) (pos : Nat)
    (c : OakText.Cnf) (fuel : Nat) (hrel : CnfRel cnf s pos c) (hf : cnf.size < fuel) :
    ∃ (kind : UInt32) (state' : Array UInt32), rup_token cnf s.scan fuel = some (kind, state') ∧
      state'.size = 5 ∧
      kind.toNat = (scan (toBytes cnf) pos).kind ∧
      (state'.getD 0 0).toNat = (scan (toBytes cnf) pos).next ∧
      (state'.getD 1 0).toNat = (scan (toBytes cnf) pos).start ∧
      (state'.getD 2 0).toNat = (scan (toBytes cnf) pos).stop ∧
      (state'.getD 3 0).toNat = (scan (toBytes cnf) pos).magnitude ∧
      (state'.getD 4 0).toNat = (scan (toBytes cnf) pos).sign := by
  obtain ⟨h5, hpos, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hle⟩ := hrel
  have := rup_token_scan cnf s.scan fuel hs h5 (by rw [hpos]; exact hle) hf
  rw [hpos] at this
  exact this

/-- One iteration of the extracted DIMACS loop, from a live state, is one
`cnfStep` of the model: the loop recurses on a state that represents the
step's result at the token's `next`, and the extracted `done` is the
step's stop flag. -/
theorem cnf_step (cnf : Array UInt8) (hs : cnf.size ≤ 65536) (s : CnfExt) (pos : Nat)
    (c : OakText.Cnf) (fuel : Nat) (hrel : CnfRel cnf s pos c) (hdone : s.done = false)
    (hvalid : c.valid = true) (hf : cnf.size < fuel) :
    ∃ s' : CnfExt, s.run cnf (fuel + 1) = s'.run cnf fuel ∧
      CnfRel cnf s' (scan (toBytes cnf) pos).next
        (OakText.cnfStep (toBytes cnf) (scan (toBytes cnf) pos) c).1 ∧
      s'.done = (OakText.cnfStep (toBytes cnf) (scan (toBytes cnf) pos) c).2 := by
  obtain ⟨kind, state', h1, hsz, hk, hnext, hstart, hstop, hmag, hsign⟩ := scan_step cnf hs s pos c fuel hrel hf
  have hrel' := hrel
  obtain ⟨h5, hpos, hpool5, hinit5, hsizes5, hv, hstage, hvars, hexp, hcl, hlit, hpend, hfirst, hcomment,
    hpendle, hpoolle, hinitlen, hsizeslen, hexplim, hexp256, hpoolpre, hclpre, hle⟩ := hrel
  have hrange := scan_range (toBytes cnf) pos (by rw [toBytes_length]; exact hle)
  rw [toBytes_length] at hrange
  obtain ⟨hps, hsn, hns, hstopn, hkind0⟩ := hrange
  have hsvalid : s.valid = true := by rw [hv, hvalid]
  -- Unfold one iteration: the head test passes, the scanner runs.
  unfold CnfExt.run
  rw [rup_text_check.loop3]
  simp only [hdone, hsvalid, Bool.not_false, Bool.true_and, ite_true, h1, bind, Option.bind]
  -- The token's kind as the model sees it.
  generalize ht : scan (toBytes cnf) pos = t at hk hnext hstart hstop hmag hsign hps hsn hns hstopn hkind0 ⊢
  have hk2 : (kind != 2) = decide (t.kind ≠ 2) := by
    rw [bne_ofNat32 kind 2 (by decide), hk, beq_nat_decide]
    by_cases h : t.kind = 2 <;> simp [h]
  have hk0 : (kind == 0) = decide (t.kind = 0) := by
    rw [beq_ofNat32 kind 0 (by decide), hk, beq_nat_decide]
  have hstage_eq : ∀ n : Nat, n < UInt32.size → (s.stage == (OfNat.ofNat n : UInt32)) = decide (c.stage = n) := by
    intro n hn
    rw [beq_ofNat32 s.stage n hn, hstage, beq_nat_decide]
  by_cases hnot2 : t.kind ≠ 2
  · -- A newline or the end of the text: close the stage, stop at EOF.
    have hb : (kind != 2) = true := by rw [hk2, decide_eq_true hnot2]
    simp only [hb, ite_true, pure]
    have hstep : OakText.cnfStep (toBytes cnf) t c =
        ({ c with
            valid := decide (c.stage = 0 ∨ c.stage ≥ 4)
            stage := if c.stage = 4 then 5 else c.stage
            first := true
            comment := false }, decide (t.kind = 0)) := by
      unfold OakText.cnfStep
      rw [if_pos hnot2]
    rw [hstep]
    have hvalid' : (s.stage == 0 || decide (s.stage ≥ 4)) = decide (c.stage = 0 ∨ c.stage ≥ 4) := by
      rw [hstage_eq 0 (by decide), Bool.decide_or]
      congr 1
      show decide (4 ≤ s.stage) = decide (4 ≤ c.stage)
      rw [decide_le_toNat, hstage, toNat_ofNat32 4 (by decide)]
    by_cases hst4 : c.stage = 4
    · have hb4 : (s.stage == 4) = true := by rw [hstage_eq 4 (by decide), decide_eq_true hst4]
      simp only [hb4, ite_true, if_pos hst4]
      refine ⟨{ s with
          scan := state'
          valid := (s.stage == 0 || decide (s.stage ≥ 4))
          stage := 5
          first := true
          comment := false
          done := (kind == 0) }, rfl, ?_, ?_⟩
      · unfold CnfRel
        refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, hvalid', rfl, hvars, hexp, hcl, hlit, hpend,
          rfl, rfl, hpendle, hpoolle, hinitlen, hsizeslen, hexplim, ?_, hpoolpre, hclpre, hns⟩
        intro _ _
        exact hexp256 hvalid (by omega)
      · exact hk0
    · have hb4 : (s.stage == 4) = false := by rw [hstage_eq 4 (by decide), decide_eq_false hst4]
      simp only [hb4, Bool.false_eq_true, ite_false, if_neg hst4]
      refine ⟨{ s with
          scan := state'
          valid := (s.stage == 0 || decide (s.stage ≥ 4))
          first := true
          comment := false
          done := (kind == 0) }, rfl, ?_, ?_⟩
      · unfold CnfRel
        refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, hvalid', hstage, hvars, hexp, hcl, hlit, hpend,
          rfl, rfl, hpendle, hpoolle, hinitlen, hsizeslen, hexplim, ?_, hpoolpre, hclpre, hns⟩
        intro _ h4
        exact hexp256 hvalid h4
      · exact hk0
  · -- A word: the comment test, then the stage machine.
    have hb : (kind != 2) = false := by rw [hk2, decide_eq_false hnot2]
    simp only [hb, Bool.false_eq_true, ite_false]
    have hstop' : t.stop = t.next := hstopn
    have hw99 := rup_word_spec cnf state' 99 fuel t hstart hstop ⟨by omega, by omega⟩
    rw [hw99]
    simp only []
    have hcom : (s.first && decide (Word (toBytes cnf) t (99 : UInt8).toNat)) =
        (c.first && decide (Word (toBytes cnf) t 99)) := by rw [hfirst]; rfl
    -- The model's step, with the comment flag named.
    have hmodel : OakText.cnfStep (toBytes cnf) t c =
        (let comment := c.comment || (c.first && decide (Word (toBytes cnf) t 99))
        if comment then ({ c with first := false, comment := comment }, false)
        else if c.stage = 0 then
          ({ c with valid := decide (Word (toBytes cnf) t 112), stage := 1, first := false, comment := comment }, false)
        else if c.stage = 1 then
          ({ c with
              valid := decide (t.stop - t.start = 3) && decide ((toBytes cnf)[t.start]? = some 99 ∧
                (toBytes cnf)[t.start + 1]? = some 110 ∧ (toBytes cnf)[t.start + 2]? = some 102)
              stage := 2
              first := false
              comment := comment }, false)
        else if c.stage = 2 then
          ({ c with
              valid := decide (t.sign ≠ 0) && decide (t.sign = 1 ∧ t.magnitude > 0 ∧ t.magnitude ≤ 64)
              variables := t.magnitude
              stage := 3
              first := false
              comment := comment }, false)
        else if c.stage = 3 then
          ({ c with
              valid := decide (t.sign ≠ 0) && decide ((t.sign = 1 ∨ t.magnitude = 0) ∧ t.magnitude ≤ 256)
              expected := t.magnitude
              stage := 4
              first := false
              comment := comment }, false)
        else if t.magnitude = 0 then
          if decide (t.sign ≠ 0) && decide (c.stage = 5) && decide (c.clauses < c.expected) then
            ({ c with
                valid := true
                initial := c.initial ++ [c.pending]
                sizes := c.sizes ++ [c.pool.length - c.pending]
                clauses := c.clauses + 1
                pending := c.pool.length
                first := false
                comment := comment }, false)
          else ({ c with valid := false, first := false, comment := comment }, false)
        else
          if decide (t.sign ≠ 0) && decide (c.stage = 5) && decide (t.magnitude ≤ c.variables ∧ c.pool.length < 4096) then
            ({ c with
                valid := true
                pool := c.pool ++ [OakText.encoded t.magnitude t.sign]
                first := false
                comment := comment }, false)
          else ({ c with valid := false, first := false, comment := comment }, false)) := by
      unfold OakText.cnfStep
      rw [if_neg hnot2]
    rw [hmodel]
    by_cases hfw : (c.first && decide (Word (toBytes cnf) t 99)) = true
    · -- A comment line: nothing else happens on it.
      have hfw' : (s.first && decide (Word (toBytes cnf) t (99 : UInt8).toNat)) = true := by rw [hcom, hfw]
      have hcm : (c.comment || (c.first && decide (Word (toBytes cnf) t 99))) = true := by rw [hfw, Bool.or_true]
      simp only [hfw', ite_true, hcm, Bool.not_true, Bool.false_eq_true, ite_false, pure]
      refine ⟨{ s with
          scan := state'
          valid := true
          first := false
          comment := true
          done := false }, rfl, ?_, ?_⟩
      · unfold CnfRel
        refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, hvalid.symm, hstage, hvars, hexp, hcl, hlit, hpend,
          rfl, rfl, hpendle, hpoolle, hinitlen, hsizeslen, hexplim, hexp256, hpoolpre, hclpre, hns⟩
      · rfl
    · have hfw' : (s.first && decide (Word (toBytes cnf) t (99 : UInt8).toNat)) = false := by
        rw [hcom]; exact Bool.eq_false_iff.mpr hfw
      have hcm : (c.comment || (c.first && decide (Word (toBytes cnf) t 99))) = c.comment := by
        rw [Bool.eq_false_iff.mpr hfw, Bool.or_false]
      simp only [hfw', Bool.false_eq_true, ite_false, hcm, pure]
      by_cases hcc : c.comment = true
      · -- Inside a comment line already.
        have hsc : (!s.comment) = false := by rw [hcomment, hcc]; rfl
        simp only [hcc, ite_true, hsc, Bool.false_eq_true, ite_false]
        refine ⟨{ s with
            scan := state'
            valid := true
            first := false
            done := false }, rfl, ?_, ?_⟩
        · unfold CnfRel
          refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, hvalid.symm, hstage, hvars, hexp, hcl, hlit, hpend,
            rfl, by rw [hcomment, hcc], hpendle, hpoolle, hinitlen, hsizeslen, hexplim, hexp256, hpoolpre, hclpre, hns⟩
        · rfl
      · have hcf : c.comment = false := Bool.eq_false_iff.mpr hcc
        have hsc : (!s.comment) = true := by rw [hcomment, hcf]; rfl
        simp only [hcf, Bool.false_eq_true, ite_false, hsc, ite_true]
        -- Stage 0: the `p` of the header.
        by_cases hst0 : c.stage = 0
        · have hb0 : (s.stage == 0) = true := by rw [hstage_eq 0 (by decide), decide_eq_true hst0]
          have hw112 := rup_word_spec cnf state' 112 fuel t hstart hstop ⟨by omega, by omega⟩
          simp only [hb0, ite_true, if_pos hst0, hw112]
          refine ⟨{ s with
              scan := state'
              valid := decide (Word (toBytes cnf) t (112 : UInt8).toNat)
              stage := 1
              first := false
              comment := s.comment
              done := false }, rfl, ?_, ?_⟩
          · unfold CnfRel
            refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, rfl, rfl, hvars, hexp, hcl, hlit, hpend,
              rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hexplim, ?_, hpoolpre, hclpre, hns⟩
            intro _ (h : 4 ≤ 1); omega
          · rfl
        · have hb0 : (s.stage == 0) = false := by rw [hstage_eq 0 (by decide), decide_eq_false hst0]
          simp only [hb0, Bool.false_eq_true, ite_false, if_neg hst0]
          -- Stage 1: the `cnf` of the header.
          by_cases hst1 : c.stage = 1
          · have hb1 : (s.stage == 1) = true := by rw [hstage_eq 1 (by decide), decide_eq_true hst1]
            simp only [hb1, ite_true, if_pos hst1]
            have hheader : (state'.getD 2 0 - state'.getD 1 0 == 3 && cnf.getD (state'.getD 1 0).toNat 0 == 99 &&
                cnf.getD (state'.getD 1 0 + 1).toNat 0 == 110 && cnf.getD (state'.getD 1 0 + 2).toNat 0 == 102) =
                (decide (t.stop - t.start = 3) && decide ((toBytes cnf)[t.start]? = some 99 ∧
                  (toBytes cnf)[t.start + 1]? = some 110 ∧ (toBytes cnf)[t.start + 2]? = some 102)) := by
              have hsub : (state'.getD 2 0 - state'.getD 1 0).toNat = t.stop - t.start := by
                rw [toNat_sub_of_le' _ _ (by omega), hstart, hstop]
              rw [beq_toNat32, hsub, toNat_ofNat32 3 (by decide)]
              by_cases h3 : t.stop - t.start = 3
              · have hin0 : t.start < cnf.size := by omega
                have hin1 : t.start + 1 < cnf.size := by omega
                have hin2 : t.start + 2 < cnf.size := by omega
                have hp1 : (state'.getD 1 0 + 1).toNat = t.start + 1 := by
                  rw [UInt32.toNat_add, hstart, toNat_ofNat32 1 (by decide)]; exact Nat.mod_eq_of_lt (by omega)
                have hp2 : (state'.getD 1 0 + 2).toNat = t.start + 2 := by
                  rw [UInt32.toNat_add, hstart, toNat_ofNat32 2 (by decide)]; exact Nat.mod_eq_of_lt (by omega)
                rw [decide_eq_true h3, hstart, hp1, hp2, byte_eq cnf t.start 99 (by decide) hin0,
                  byte_eq cnf (t.start + 1) 110 (by decide) hin1, byte_eq cnf (t.start + 2) 102 (by decide) hin2]
                simp only [Bool.true_and, Bool.decide_and, Bool.and_assoc]
              · rw [decide_eq_false h3]
                simp
            rw [hheader]
            refine ⟨{ s with
                scan := state'
                valid := decide (t.stop - t.start = 3) && decide ((toBytes cnf)[t.start]? = some 99 ∧
                  (toBytes cnf)[t.start + 1]? = some 110 ∧ (toBytes cnf)[t.start + 2]? = some 102)
                stage := 2
                first := false
                comment := s.comment
                done := false }, rfl, ?_, ?_⟩
            · unfold CnfRel
              refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, rfl, rfl, hvars, hexp, hcl, hlit, hpend,
                rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hexplim, ?_, hpoolpre, hclpre, hns⟩
              intro _ (h : 4 ≤ 2); omega
            · rfl
          · have hb1 : (s.stage == 1) = false := by rw [hstage_eq 1 (by decide), decide_eq_false hst1]
            simp only [hb1, Bool.false_eq_true, ite_false, if_neg hst1]
            -- The numeric atoms of the remaining stages.
            have hsign0 : (state'.getD 4 0 != 0) = decide (t.sign ≠ 0) := bne_zero_decide _ _ hsign
            have hsign1 : (state'.getD 4 0 == 1) = decide (t.sign = 1) := by
              rw [beq_ofNat32 _ 1 (by decide), hsign, beq_nat_decide]
            have hmag0 : (state'.getD 3 0 == 0) = decide (t.magnitude = 0) := by
              rw [beq_ofNat32 _ 0 (by decide), hmag, beq_nat_decide]
            have hgt0 : decide (state'.getD 3 0 > 0) = decide (t.magnitude > 0) := by
              show decide ((0 : UInt32) < state'.getD 3 0) = decide (0 < t.magnitude)
              rw [decide_lt_toNat, hmag, toNat_ofNat32 0 (by decide)]
            have hle64 : decide (state'.getD 3 0 ≤ 64) = decide (t.magnitude ≤ 64) := by
              rw [decide_le_toNat, hmag, toNat_ofNat32 64 (by decide)]
            have hle256 : decide (state'.getD 3 0 ≤ 256) = decide (t.magnitude ≤ 256) := by
              rw [decide_le_toNat, hmag, toNat_ofNat32 256 (by decide)]
            have hlimit : t.magnitude ≤ Decimal.limit := by rw [← ht]; exact scan_magnitude_le _ _
            -- Stage 2: the variable count.
            by_cases hst2 : c.stage = 2
            · have hb2 : (s.stage == 2) = true := by rw [hstage_eq 2 (by decide), decide_eq_true hst2]
              simp only [hb2, ite_true, if_pos hst2]
              have hvalid2 : (state'.getD 4 0 != 0 && state'.getD 4 0 == 1 && decide (state'.getD 3 0 > 0) &&
                  decide (state'.getD 3 0 ≤ 64)) =
                  (decide (t.sign ≠ 0) && decide (t.sign = 1 ∧ t.magnitude > 0 ∧ t.magnitude ≤ 64)) := by
                rw [hsign0, hsign1, hgt0, hle64]
                simp only [Bool.decide_and, Bool.and_assoc]
              rw [hvalid2]
              refine ⟨{ s with
                  scan := state'
                  valid := decide (t.sign ≠ 0) && decide (t.sign = 1 ∧ t.magnitude > 0 ∧ t.magnitude ≤ 64)
                  stage := 3
                  variables := state'.getD 3 0
                  first := false
                  comment := s.comment
                  done := false }, rfl, ?_, ?_⟩
              · unfold CnfRel
                refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, rfl, rfl, hmag, hexp, hcl, hlit, hpend,
                  rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hexplim, ?_, hpoolpre, hclpre, hns⟩
                intro _ (h : 4 ≤ 3); omega
              · rfl
            · have hb2 : (s.stage == 2) = false := by rw [hstage_eq 2 (by decide), decide_eq_false hst2]
              simp only [hb2, Bool.false_eq_true, ite_false, if_neg hst2]
              -- Stage 3: the clause count.
              by_cases hst3 : c.stage = 3
              · have hb3 : (s.stage == 3) = true := by rw [hstage_eq 3 (by decide), decide_eq_true hst3]
                simp only [hb3, ite_true, if_pos hst3]
                have hvalid3 : (state'.getD 4 0 != 0 && (state'.getD 4 0 == 1 || state'.getD 3 0 == 0) &&
                    decide (state'.getD 3 0 ≤ 256)) =
                    (decide (t.sign ≠ 0) && decide ((t.sign = 1 ∨ t.magnitude = 0) ∧ t.magnitude ≤ 256)) := by
                  rw [hsign0, hsign1, hmag0, hle256]
                  simp only [Bool.decide_and, Bool.decide_or, Bool.and_assoc]
                rw [hvalid3]
                refine ⟨{ s with
                    scan := state'
                    valid := decide (t.sign ≠ 0) && decide ((t.sign = 1 ∨ t.magnitude = 0) ∧ t.magnitude ≤ 256)
                    stage := 4
                    expected := state'.getD 3 0
                    first := false
                    comment := s.comment
                    done := false }, rfl, ?_, ?_⟩
                · unfold CnfRel
                  refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, rfl, rfl, hvars, hmag, hcl, hlit, hpend,
                    rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hlimit, ?_, hpoolpre, hclpre, hns⟩
                  · intro hv' _
                    exact (of_decide_eq_true ((Bool.and_eq_true _ _).mp hv').2).2
                · rfl
              · have hb3 : (s.stage == 3) = false := by rw [hstage_eq 3 (by decide), decide_eq_false hst3]
                simp only [hb3, Bool.false_eq_true, ite_false, if_neg hst3]
                have hst5 : (s.stage == 5) = decide (c.stage = 5) := hstage_eq 5 (by decide)
                have hclex : decide (s.clauses < s.expected) = decide (c.clauses < c.expected) := by
                  rw [decide_lt_toNat, hcl, hexp]
                -- A zero closes a clause; anything else is a literal.
                by_cases hm : t.magnitude = 0
                · have hbm : (state'.getD 3 0 == 0) = true := by rw [hmag0, decide_eq_true hm]
                  simp only [hbm, ite_true, if_pos hm, hsign0, hst5, hclex]
                  by_cases hcond : (decide (t.sign ≠ 0) && decide (c.stage = 5) && decide (c.clauses < c.expected)) = true
                  · simp only [hcond, ite_true]
                    have hparts := (Bool.and_eq_true _ _).mp hcond
                    have hstage5 : c.stage = 5 := of_decide_eq_true ((Bool.and_eq_true _ _).mp hparts.1).2
                    have hltx : c.clauses < c.expected := of_decide_eq_true hparts.2
                    have hexp256' : c.expected ≤ 256 := hexp256 hvalid (by omega)
                    have hcl256 : s.clauses.toNat < 256 := by omega
                    have hclsucc : (s.clauses + 1).toNat = c.clauses + 1 := by
                      rw [UInt32.toNat_add, hcl, toNat_ofNat32 1 (by decide)]
                      exact Nat.mod_eq_of_lt (by omega)
                    have hsizeval : (s.literals - s.pending).toNat = c.pool.length - c.pending := by
                      rw [toNat_sub_of_le' _ _ (by omega), hlit, hpend]
                    refine ⟨{ s with
                        initial := s.initial.setIfInBounds s.clauses.toNat s.pending
                        sizes := s.sizes.setIfInBounds s.clauses.toNat (s.literals - s.pending)
                        scan := state'
                        valid := true
                        clauses := s.clauses + 1
                        pending := s.literals
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold CnfRel
                      refine ⟨hsz, hnext, hpool5, by rw [size_set]; exact hinit5, by rw [size_set]; exact hsizes5,
                        rfl, hstage, hvars, hexp, hclsucc, hlit, hlit, rfl, by rw [hcomment, hcf],
                        Nat.le_refl _, hpoolle, by simp [hinitlen], by simp [hsizeslen], hexplim,
                        fun _ h => hexp256 hvalid h, hpoolpre, ?_, hns⟩
                      intro i hi
                      have hi' : i < c.clauses + 1 := hi
                      by_cases hic : i < c.clauses
                      · obtain ⟨hi1, hi2⟩ := hclpre i hic
                        rw [getD_set_ne _ _ _ _ (by omega), getD_set_ne _ _ _ _ (by omega),
                          list_getD_append_lt _ _ _ (by omega), list_getD_append_lt _ _ _ (by omega)]
                        exact ⟨hi1, hi2⟩
                      · have hieq : i = c.clauses := by omega
                        subst hieq
                        rw [← hcl, getD_set_self _ _ _ (by rw [hinit5]; exact hcl256),
                          getD_set_self _ _ _ (by rw [hsizes5]; exact hcl256), hcl, ← hinitlen,
                          list_getD_append_self, hinitlen, ← hsizeslen, list_getD_append_self]
                        exact ⟨hpend, hsizeval⟩
                    · rfl
                  · have hcondf := Bool.eq_false_iff.mpr hcond
                    simp only [hcondf, Bool.false_eq_true, ite_false]
                    refine ⟨{ s with
                        scan := state'
                        valid := false
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold CnfRel
                      refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, rfl, hstage, hvars, hexp, hcl, hlit, hpend,
                        rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hexplim, ?_, hpoolpre, hclpre, hns⟩
                      intro h; exact absurd h Bool.false_ne_true
                    · rfl
                · have hbm : (state'.getD 3 0 == 0) = false := by rw [hmag0, decide_eq_false hm]
                  have hlevars : decide (state'.getD 3 0 ≤ s.variables) = decide (t.magnitude ≤ c.variables) := by
                    rw [decide_le_toNat, hmag, hvars]
                  have hlit4096 : decide (s.literals < 4096) = decide (c.pool.length < 4096) := by
                    rw [decide_lt_toNat, hlit, toNat_ofNat32 4096 (by decide)]
                  simp only [hbm, Bool.false_eq_true, ite_false, if_neg hm, hsign0, hst5, hlevars, hlit4096]
                  have hcondE : (decide (t.sign ≠ 0) && decide (c.stage = 5) && decide (t.magnitude ≤ c.variables) &&
                      decide (c.pool.length < 4096)) =
                      (decide (t.sign ≠ 0) && decide (c.stage = 5) && decide (t.magnitude ≤ c.variables ∧ c.pool.length < 4096)) := by
                    simp only [Bool.decide_and, Bool.and_assoc]
                  rw [hcondE]
                  by_cases hcond : (decide (t.sign ≠ 0) && decide (c.stage = 5) &&
                      decide (t.magnitude ≤ c.variables ∧ c.pool.length < 4096)) = true
                  · have hparts := (Bool.and_eq_true _ _).mp hcond
                    have hroom : c.pool.length < 4096 := (of_decide_eq_true hparts.2).2
                    obtain ⟨e, he, heval⟩ := rup_encoded_spec (state'.getD 3 0) (state'.getD 4 0) fuel
                      (by rw [hmag]; omega) (by rw [hmag]; exact hlimit)
                    simp only [hcond, ite_true, he]
                    have hlitsucc : (s.literals + 1).toNat = c.pool.length + 1 := by
                      rw [UInt32.toNat_add, hlit, toNat_ofNat32 1 (by decide)]
                      exact Nat.mod_eq_of_lt (by omega)
                    refine ⟨{ s with
                        pool := s.pool.setIfInBounds s.literals.toNat e
                        scan := state'
                        valid := true
                        literals := s.literals + 1
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold CnfRel
                      refine ⟨hsz, hnext, by rw [size_set]; exact hpool5, hinit5, hsizes5,
                        rfl, hstage, hvars, hexp, hcl, by simp [hlitsucc], hpend, rfl, by rw [hcomment, hcf],
                        by simp; omega, by simp; omega, hinitlen, hsizeslen, hexplim,
                        fun _ h => hexp256 hvalid h, ?_, hclpre, hns⟩
                      intro i hi
                      have hi' : i < (c.pool ++ [OakText.encoded t.magnitude t.sign]).length := hi
                      simp only [List.length_append, List.length_singleton] at hi'
                      by_cases hil : i < c.pool.length
                      · rw [getD_set_ne _ _ _ _ (by omega), list_getD_append_lt _ _ _ hil]
                        exact hpoolpre i hil
                      · have hieq : i = c.pool.length := by omega
                        subst hieq
                        rw [← hlit, getD_set_self _ _ _ (by rw [hpool5]; omega), hlit, list_getD_append_self,
                          heval, hmag, hsign]
                    · rfl
                  · have hcondf := Bool.eq_false_iff.mpr hcond
                    simp only [hcondf, Bool.false_eq_true, ite_false]
                    refine ⟨{ s with
                        scan := state'
                        valid := false
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold CnfRel
                      refine ⟨hsz, hnext, hpool5, hinit5, hsizes5, rfl, hstage, hvars, hexp, hcl, hlit, hpend,
                        rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hexplim, ?_, hpoolpre, hclpre, hns⟩
                      intro h; exact absurd h Bool.false_ne_true
                    · rfl


/-- The model's step stops only at the end of the text. -/
theorem cnfStep_stop (bytes : List Nat) (t : Token) (c : OakText.Cnf)
    (h : (OakText.cnfStep bytes t c).2 = false) : t.kind ≠ 0 := by
  unfold OakText.cnfStep at h
  by_cases hk : t.kind ≠ 2
  · rw [if_pos hk] at h
    simp only at h
    exact of_decide_eq_false h
  · intro h0
    exact hk (by omega)

theorem CnfRel.pos_le {cnf : Array UInt8} {s : CnfExt} {pos : Nat} {c : OakText.Cnf}
    (h : CnfRel cnf s pos c) : pos ≤ cnf.size := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hle⟩ := h
  exact hle

theorem CnfRel.valid_eq {cnf : Array UInt8} {s : CnfExt} {pos : Nat} {c : OakText.Cnf}
    (h : CnfRel cnf s pos c) : s.valid = c.valid := by
  obtain ⟨-, -, -, -, -, hv, -⟩ := h
  exact hv

/-- The final relation: the extracted loop's result represents the model's,
at whatever cursor the loop stopped. -/
def CnfRelEnd (cnf : Array UInt8) (s : CnfExt) (c : OakText.Cnf) : Prop :=
  ∃ pos, CnfRel cnf s pos c

/-- The extracted DIMACS loop runs to the model's `cnfLoop` result: from
related live states, with the model's fuel above the bytes that remain and
the extracted fuel above the model's plus the text, both loops return and
their results are related. -/
theorem cnf_loop (cnf : Array UInt8) (hs : cnf.size ≤ 65536) :
    ∀ (m : Nat) (s : CnfExt) (pos : Nat) (c : OakText.Cnf) (fuel : Nat),
      CnfRel cnf s pos c → s.done = false → cnf.size - pos < m → m + cnf.size < fuel →
      ∃ (s' : CnfExt) (c' : OakText.Cnf), s.run cnf fuel = some s'.tuple ∧
        OakText.cnfLoop (toBytes cnf) pos c m = some c' ∧ CnfRelEnd cnf s' c' := by
  intro m
  induction m with
  | zero => intro s pos c fuel _ _ hm; omega
  | succ m ih =>
    intro s pos c fuel hrel hdone hm hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hsize_f : cnf.size < f := by omega
    by_cases hvalid : c.valid = true
    · obtain ⟨s1, hrun, hrel1, hdone1⟩ := cnf_step cnf hs s pos c f hrel hdone hvalid hsize_f
      have hmodel : OakText.cnfLoop (toBytes cnf) pos c (m + 1) =
          (if (OakText.cnfStep (toBytes cnf) (scan (toBytes cnf) pos) c).2 then
            some (OakText.cnfStep (toBytes cnf) (scan (toBytes cnf) pos) c).1
          else OakText.cnfLoop (toBytes cnf) (scan (toBytes cnf) pos).next
            (OakText.cnfStep (toBytes cnf) (scan (toBytes cnf) pos) c).1 m) := by
        simp only [OakText.cnfLoop, hvalid, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hmodel, hrun]
      by_cases hstop : (OakText.cnfStep (toBytes cnf) (scan (toBytes cnf) pos) c).2 = true
      · -- The end of the text: the extracted loop notices on its next test.
        rw [if_pos hstop]
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        refine ⟨s1, _, ?_, rfl, ⟨_, hrel1⟩⟩
        unfold CnfExt.run
        rw [rup_text_check.loop3]
        have hd : (!s1.done && s1.valid) = false := by rw [hdone1, hstop]; rfl
        rw [if_neg (by rw [hd]; exact Bool.false_ne_true)]
        rfl
      · have hstop' := Bool.eq_false_iff.mpr hstop
        rw [if_neg (by rw [hstop']; exact Bool.false_ne_true)]
        have hkind := cnfStep_stop _ _ _ hstop'
        have hrange := scan_range (toBytes cnf) pos (by rw [toBytes_length]; exact hrel.pos_le)
        rw [toBytes_length] at hrange
        obtain ⟨-, -, hns, -, hadv⟩ := hrange
        have hpos := hadv hkind
        exact ih s1 _ _ f hrel1 (by rw [hdone1, hstop']) (by omega) (by omega)
    · -- An invalid state: both loops return it.
      have hvf : c.valid = false := Bool.eq_false_iff.mpr hvalid
      have hsv : (!s.done && s.valid) = false := by rw [hrel.valid_eq, hvf]; simp
      refine ⟨s, c, ?_, ?_, ⟨pos, hrel⟩⟩
      · unfold CnfExt.run
        rw [rup_text_check.loop3]
        rw [if_neg (by rw [hsv]; exact Bool.false_ne_true)]
        rfl
      · simp only [OakText.cnfLoop, hvf, Bool.not_false, ite_true]


/-! ## The entry guards and the initial state -/

/-- The byte the ASCII guard reads, as the model's list element. -/
theorem guard_byte (text : Array UInt8) (i : Nat) (hi : i < text.size) :
    decide (text.getD i 0 ≤ 127) = decide ((toBytes text)[i]'(by rw [toBytes_length]; exact hi) ≤ 127) := by
  rw [← getD_toBytes_of_lt text i hi, ← getD_toBytes]
  exact decide_eq_decide.mpr UInt8.le_iff_toNat_le

/-- `all` over the bytes from a position, one byte at a time. -/
theorem all_drop_cons (bytes : List Nat) (i : Nat) (hi : i < bytes.length) :
    (bytes.drop i).all (fun x => decide (x ≤ 127)) =
      (decide (bytes[i]'hi ≤ 127) && (bytes.drop (i + 1)).all (fun x => decide (x ≤ 127))) := by
  rw [List.drop_eq_getElem_cons hi, List.all_cons]

/-- The first ASCII guard loop: from any position with fuel above the bytes
that remain, it returns the incoming flag conjoined with the model's `all`
over the rest of the text. -/
theorem guard1_spec (cnf : Array UInt8) (hs : cnf.size ≤ 65536) :
    ∀ (fuel : Nat) (valid : Bool) (b : UInt32), b.toNat ≤ cnf.size → cnf.size - b.toNat < fuel →
      ∃ b' : UInt32, rup_text_check.loop1 cnf valid b fuel =
        some (valid && ((toBytes cnf).drop b.toNat).all (fun x => decide (x ≤ 127)), b') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ fuel ih =>
    intro valid b hb hf
    rw [rup_text_check.loop1]
    by_cases hv : valid = true
    · subst hv
      by_cases hin : b.toNat < cnf.size
      · have hlt : decide (b < cnf.size.toUInt32) = true := (lt_size_iff cnf b hs).mpr hin
        simp only [hlt, Bool.true_and, ite_true]
        have hsucc := toNat_succ b (by omega)
        obtain ⟨b', hb'⟩ := ih (decide (cnf.getD b.toNat 0 ≤ 127)) (b + 1) (by omega) (by omega)
        refine ⟨b', ?_⟩
        simp only [hb', hsucc]
        rw [all_drop_cons (toBytes cnf) b.toNat (by rw [toBytes_length]; exact hin), guard_byte cnf b.toNat hin]
      · have hlt : decide (b < cnf.size.toUInt32) = false := by
          have := lt_size_iff cnf b hs
          exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
        simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
        refine ⟨b, ?_⟩
        have hdrop : (toBytes cnf).drop b.toNat = [] := by
          apply List.drop_eq_nil_of_le
          rw [toBytes_length]; omega
        rw [hdrop]
        rfl
    · have hvf : valid = false := Bool.eq_false_iff.mpr hv
      subst hvf
      simp only [Bool.and_false, Bool.false_eq_true, ite_false, pure]
      exact ⟨b, rfl⟩

/-- The second guard loop is the first over the proof text. -/
theorem guard2_spec (proof : Array UInt8) (hs : proof.size ≤ 65536) :
    ∀ (fuel : Nat) (valid : Bool) (b : UInt32), b.toNat ≤ proof.size → proof.size - b.toNat < fuel →
      ∃ b' : UInt32, rup_text_check.loop2 proof valid b fuel =
        some (valid && ((toBytes proof).drop b.toNat).all (fun x => decide (x ≤ 127)), b') := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ fuel ih =>
    intro valid b hb hf
    rw [rup_text_check.loop2]
    by_cases hv : valid = true
    · subst hv
      by_cases hin : b.toNat < proof.size
      · have hlt : decide (b < proof.size.toUInt32) = true := (lt_size_iff proof b hs).mpr hin
        simp only [hlt, Bool.true_and, ite_true]
        have hsucc := toNat_succ b (by omega)
        obtain ⟨b', hb'⟩ := ih (decide (proof.getD b.toNat 0 ≤ 127)) (b + 1) (by omega) (by omega)
        refine ⟨b', ?_⟩
        simp only [hb', hsucc]
        rw [all_drop_cons (toBytes proof) b.toNat (by rw [toBytes_length]; exact hin), guard_byte proof b.toNat hin]
      · have hlt : decide (b < proof.size.toUInt32) = false := by
          have := lt_size_iff proof b hs
          exact Bool.eq_false_iff.mpr (fun h => hin (this.mp h))
        simp only [hlt, Bool.false_and, Bool.false_eq_true, ite_false, pure]
        refine ⟨b, ?_⟩
        have hdrop : (toBytes proof).drop b.toNat = [] := by
          apply List.drop_eq_nil_of_le
          rw [toBytes_length]; omega
        rw [hdrop]
        rfl
    · have hvf : valid = false := Bool.eq_false_iff.mpr hv
      subst hvf
      simp only [Bool.and_false, Bool.false_eq_true, ite_false, pure]
      exact ⟨b, rfl⟩

/-- The extracted DIMACS loop's starting state, as `rup_text_check` builds it. -/
def cnfStart (valid : Bool) : CnfExt :=
  { pool := Array.replicate 4096 0, initial := Array.replicate 256 0, sizes := Array.replicate 256 0,
    scan := (Array.replicate 5 (0 : UInt32)).setIfInBounds 0 0, valid := valid, stage := 0, variables := 0,
    expected := 0, clauses := 0, literals := 0, pending := 0, first := true, comment := false, done := false }

/-- The starting state represents the model's initial `Cnf` with the same
validity flag, at cursor zero. -/
theorem cnfStart_rel (cnf : Array UInt8) (valid : Bool) :
    CnfRel cnf (cnfStart valid) 0 { OakText.initialCnf with valid := valid } := by
  unfold CnfRel cnfStart OakText.initialCnf
  refine ⟨by simp, by simp, by simp, by simp, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, by simp, rfl, rfl, by simp [Decimal.limit], ?_, ?_, ?_, Nat.zero_le _⟩
  · intro _ h; simp at h
  · intro i hi; simp at hi
  · intro i hi; simp at hi

#print axioms cnf_loop

end OakVerification.Extraction
