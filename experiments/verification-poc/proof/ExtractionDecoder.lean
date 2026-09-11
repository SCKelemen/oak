import OakText
import OakTextRefinement
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
  c.initial.length = c.clauses ∧ c.sizes.length = c.clauses ∧ c.clauses ≤ 256 ∧
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
  obtain ⟨h5, hpos, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hle⟩ := hrel
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
    hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, hexp256, hpoolpre, hclpre, hle⟩ := hrel
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
          rfl, rfl, hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, ?_, hpoolpre, hclpre, hns⟩
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
          rfl, rfl, hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, ?_, hpoolpre, hclpre, hns⟩
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
          rfl, rfl, hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, hexp256, hpoolpre, hclpre, hns⟩
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
            rfl, by rw [hcomment, hcc], hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, hexp256, hpoolpre, hclpre, hns⟩
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
              rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, ?_, hpoolpre, hclpre, hns⟩
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
                rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, ?_, hpoolpre, hclpre, hns⟩
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
                  rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, ?_, hpoolpre, hclpre, hns⟩
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
                    rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hlimit, ?_, hpoolpre, hclpre, hns⟩
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
                        Nat.le_refl _, hpoolle, by simp [hinitlen], by simp [hsizeslen],
                        by show c.clauses + 1 ≤ 256; omega, hexplim,
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
                        rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, ?_, hpoolpre, hclpre, hns⟩
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
                        by simp; omega, by simp; omega, hinitlen, hsizeslen, hcl256, hexplim,
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
                        rfl, by rw [hcomment, hcf], hpendle, hpoolle, hinitlen, hsizeslen, hcl256, hexplim, ?_, hpoolpre, hclpre, hns⟩
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hle⟩ := h
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
    Nat.le_refl _, by simp, rfl, rfl, Nat.zero_le _, by simp [Decimal.limit], ?_, ?_, ?_, Nat.zero_le _⟩
  · intro _ h; simp at h
  · intro i hi; simp at hi
  · intro i hi; simp at hi

#print axioms cnf_loop

/-! ## The LRAT phase -/

/-- The extracted command record represents the model's. -/
def CmdRel (e : RUPCommand) (m : Ranges.Command) : Prop :=
  e.addition = m.addition ∧ e.id_.toNat = m.id ∧ e.start.toNat = m.start ∧ e.count.toNat = m.count ∧
  e.refs_start.toNat = m.refsStart ∧ e.refs_count.toNat = m.refsCount

/-- The extracted LRAT loop's state, bundled. -/
structure ProofExt where
  pool : Array UInt32
  refs : Array UInt32
  commands : Array RUPCommand
  scan : Array UInt32
  valid : Bool
  stage : UInt32
  variables : UInt32
  literals : UInt32
  first : Bool
  comment : Bool
  done : Bool
  count : UInt32
  references : UInt32
  command : RUPCommand

def ProofExt.run (proof : Array UInt8) (s : ProofExt) (fuel : Nat) :=
  rup_text_check.loop4 proof s.pool s.refs s.commands s.scan s.valid s.stage s.variables s.literals
    s.first s.comment s.done s.count s.references s.command fuel

def ProofExt.tuple (s : ProofExt) :=
  (s.pool, s.refs, s.commands, s.scan, s.valid, s.stage, s.literals, s.first, s.comment, s.done,
    s.count, s.references, s.command)

/-- The extracted LRAT state represents the model's `Proof` at cursor `pos`. -/
def ProofRel (proof : Array UInt8) (s : ProofExt) (pos : Nat) (p : OakText.Proof) : Prop :=
  s.scan.size = 5 ∧ (s.scan.getD 0 0).toNat = pos ∧
  s.pool.size = 4096 ∧ s.refs.size = 4096 ∧ s.commands.size = 256 ∧
  s.valid = p.valid ∧ s.stage.toNat = p.stage ∧ s.variables.toNat = p.variables ∧
  s.literals.toNat = p.pool.length ∧ s.references.toNat = p.refs.length ∧
  s.count.toNat = p.commands.length ∧ s.first = p.first ∧ s.comment = p.comment ∧
  CmdRel s.command p.command ∧
  p.pool.length ≤ 4096 ∧ p.refs.length ≤ 4096 ∧ p.commands.length ≤ 256 ∧
  p.command.count ≤ p.pool.length ∧ p.command.refsCount ≤ p.refs.length ∧
  (∀ i, i < p.pool.length → (s.pool.getD i 0).toNat = p.pool.getD i 0) ∧
  (∀ i, i < p.refs.length → (s.refs.getD i 0).toNat = p.refs.getD i 0) ∧
  (∀ i (h : i < p.commands.length), CmdRel (s.commands.getD i default) (p.commands[i]'h)) ∧
  pos ≤ proof.size

theorem ProofRel.pos_le {proof : Array UInt8} {s : ProofExt} {pos : Nat} {p : OakText.Proof}
    (h : ProofRel proof s pos p) : pos ≤ proof.size := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hle⟩ := h
  exact hle

theorem ProofRel.valid_eq {proof : Array UInt8} {s : ProofExt} {pos : Nat} {p : OakText.Proof}
    (h : ProofRel proof s pos p) : s.valid = p.valid := by
  obtain ⟨-, -, -, -, -, hv, -⟩ := h
  exact hv

/-- Writes into the command table, read back. -/
theorem getD_set_cmd_ne (a : Array RUPCommand) (i j : Nat) (v : RUPCommand) (hij : j ≠ i) :
    (a.setIfInBounds i v).getD j default = a.getD j default := by
  simp [Array.getD_eq_getD_getElem?, hij.symm]

theorem getD_set_cmd_self (a : Array RUPCommand) (i : Nat) (v : RUPCommand) (hi : i < a.size) :
    (a.setIfInBounds i v).getD i default = v := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem scan_step' (proof : Array UInt8) (hs : proof.size ≤ 65536) (s : ProofExt) (pos : Nat)
    (p : OakText.Proof) (fuel : Nat) (hrel : ProofRel proof s pos p) (hf : proof.size < fuel) :
    ∃ (kind : UInt32) (state' : Array UInt32), rup_token proof s.scan fuel = some (kind, state') ∧
      state'.size = 5 ∧
      kind.toNat = (scan (toBytes proof) pos).kind ∧
      (state'.getD 0 0).toNat = (scan (toBytes proof) pos).next ∧
      (state'.getD 1 0).toNat = (scan (toBytes proof) pos).start ∧
      (state'.getD 2 0).toNat = (scan (toBytes proof) pos).stop ∧
      (state'.getD 3 0).toNat = (scan (toBytes proof) pos).magnitude ∧
      (state'.getD 4 0).toNat = (scan (toBytes proof) pos).sign := by
  obtain ⟨h5, hpos, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hle⟩ := hrel
  have := rup_token_scan proof s.scan fuel hs h5 (by rw [hpos]; exact hle) hf
  rw [hpos] at this
  exact this

/-- One iteration of the extracted LRAT loop is one `proofStep` of the model. -/
theorem proof_step (proof : Array UInt8) (hs : proof.size ≤ 65536) (s : ProofExt) (pos : Nat)
    (p : OakText.Proof) (fuel : Nat) (hrel : ProofRel proof s pos p) (hdone : s.done = false)
    (hvalid : p.valid = true) (hf : proof.size < fuel) :
    ∃ s' : ProofExt, s.run proof (fuel + 1) = s'.run proof fuel ∧
      ProofRel proof s' (scan (toBytes proof) pos).next
        (OakText.proofStep (toBytes proof) (scan (toBytes proof) pos) p).1 ∧
      s'.done = (OakText.proofStep (toBytes proof) (scan (toBytes proof) pos) p).2 := by
  obtain ⟨kind, state', h1, hsz, hk, hnext, hstart, hstop, hmag, hsign⟩ := scan_step' proof hs s pos p fuel hrel hf
  obtain ⟨h5, hpos, hpool5, hrefs5, hcmds5, hv, hstage, hvars, hlit, hrefs, hcnt, hfirst, hcomment, hcmd,
    hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hle⟩ := hrel
  have hrange := scan_range (toBytes proof) pos (by rw [toBytes_length]; exact hle)
  rw [toBytes_length] at hrange
  obtain ⟨hps, hsn, hns, hstopn, hkind0⟩ := hrange
  have hsvalid : s.valid = true := by rw [hv, hvalid]
  unfold ProofExt.run
  rw [rup_text_check.loop4]
  simp only [hdone, hsvalid, Bool.not_false, Bool.true_and, ite_true, h1, bind, Option.bind]
  generalize ht : scan (toBytes proof) pos = t at hk hnext hstart hstop hmag hsign hps hsn hns hstopn hkind0 ⊢
  have hk2 : (kind != 2) = decide (t.kind ≠ 2) := by
    rw [bne_ofNat32 kind 2 (by decide), hk, beq_nat_decide]
    by_cases h : t.kind = 2 <;> simp [h]
  have hk0 : (kind == 0) = decide (t.kind = 0) := by
    rw [beq_ofNat32 kind 0 (by decide), hk, beq_nat_decide]
  have hstage_eq : ∀ n : Nat, n < UInt32.size → (s.stage == (OfNat.ofNat n : UInt32)) = decide (p.stage = n) := by
    intro n hn
    rw [beq_ofNat32 s.stage n hn, hstage, beq_nat_decide]
  have hsign0 : (state'.getD 4 0 != 0) = decide (t.sign ≠ 0) := bne_zero_decide _ _ hsign
  have hsign1 : (state'.getD 4 0 == 1) = decide (t.sign = 1) := by
    rw [beq_ofNat32 _ 1 (by decide), hsign, beq_nat_decide]
  have hmag0 : (state'.getD 3 0 == 0) = decide (t.magnitude = 0) := by
    rw [beq_ofNat32 _ 0 (by decide), hmag, beq_nat_decide]
  have hlimit : t.magnitude ≤ Decimal.limit := by rw [← ht]; exact scan_magnitude_le _ _
  have hlevars : decide (state'.getD 3 0 ≤ s.variables) = decide (t.magnitude ≤ p.variables) := by
    rw [decide_le_toNat, hmag, hvars]
  have hlit4096 : decide (s.literals < 4096) = decide (p.pool.length < 4096) := by
    rw [decide_lt_toNat, hlit, toNat_ofNat32 4096 (by decide)]
  have hrefs4096 : decide (s.references < 4096) = decide (p.refs.length < 4096) := by
    rw [decide_lt_toNat, hrefs, toNat_ofNat32 4096 (by decide)]
  by_cases hnot2 : t.kind ≠ 2
  · -- A newline or the end of the text: publish a complete command.
    have hb : (kind != 2) = true := by rw [hk2, decide_eq_true hnot2]
    simp only [hb, ite_true]
    have hstep : OakText.proofStep (toBytes proof) t p =
        (if p.stage = 5 then
          if p.commands.length < 256 then
            ({ p with
                valid := true
                commands := p.commands ++ [p.command]
                stage := 0
                first := true
                comment := false }, decide (t.kind = 0))
          else ({ p with valid := false, stage := 0, first := true, comment := false }, decide (t.kind = 0))
        else
          ({ p with valid := decide (p.stage = 0), stage := 0, first := true, comment := false },
            decide (t.kind = 0))) := by
      unfold OakText.proofStep
      rw [if_pos hnot2]
    rw [hstep]
    by_cases hst5 : p.stage = 5
    · have hb5 : (s.stage == 5) = true := by rw [hstage_eq 5 (by decide), decide_eq_true hst5]
      have hb0 : (s.stage == 0) = false := by rw [hstage_eq 0 (by decide), decide_eq_false (by omega)]
      have hcnt256 : decide (s.count < 256) = decide (p.commands.length < 256) := by
        rw [decide_lt_toNat, hcnt, toNat_ofNat32 256 (by decide)]
      simp only [hb5, hb0, ite_true, if_pos hst5, Bool.false_or, Bool.true_and, hcnt256, pure]
      by_cases hroom : p.commands.length < 256
      · have hcntsucc : (s.count + 1).toNat = p.commands.length + 1 := by
          rw [UInt32.toNat_add, hcnt, toNat_ofNat32 1 (by decide)]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [decide_eq_true hroom, ite_true, if_pos hroom]
        refine ⟨{ s with
            commands := s.commands.setIfInBounds s.count.toNat s.command
            scan := state'
            valid := true
            stage := 0
            first := true
            comment := false
            done := (kind == 0)
            count := s.count + 1 }, rfl, ?_, ?_⟩
        · unfold ProofRel
          refine ⟨hsz, hnext, hpool5, hrefs5, by show (s.commands.setIfInBounds _ _).size = 256; rw [Array.size_setIfInBounds]; exact hcmds5,
            rfl, rfl, hvars, hlit, hrefs,
            by simp [hcntsucc], rfl, rfl, hcmd, hpoolle, hrefsle, by simp; omega, hccount, hcrefs,
            hpoolpre, hrefspre, ?_, hns⟩
          intro i hi
          have hi' : i < (p.commands ++ [p.command]).length := hi
          simp only [List.length_append, List.length_singleton] at hi'
          by_cases hil : i < p.commands.length
          · rw [getD_set_cmd_ne _ _ _ _ (by omega), List.getElem_append_left hil]
            exact hcmdpre i hil
          · have hieq : i = p.commands.length := by omega
            subst hieq
            have hwrite : (s.commands.setIfInBounds s.count.toNat s.command).getD p.commands.length default = s.command := by
              rw [← hcnt]
              exact getD_set_cmd_self _ _ _ (by rw [hcmds5]; omega)
            rw [hwrite]
            simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
            exact hcmd
        · exact hk0
      · simp only [decide_eq_false hroom, Bool.false_eq_true, ite_false, if_neg hroom]
        refine ⟨{ s with
            scan := state'
            valid := false
            stage := 0
            first := true
            comment := false
            done := (kind == 0) }, rfl, ?_, ?_⟩
        · unfold ProofRel
          refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, rfl, hvars, hlit, hrefs, hcnt, rfl, rfl, hcmd,
            hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
        · exact hk0
    · have hb5 : (s.stage == 5) = false := by rw [hstage_eq 5 (by decide), decide_eq_false hst5]
      simp only [hb5, Bool.false_eq_true, ite_false, if_neg hst5, Bool.or_false, pure]
      refine ⟨{ s with
          scan := state'
          valid := (s.stage == 0)
          stage := 0
          first := true
          comment := false
          done := (kind == 0) }, rfl, ?_, ?_⟩
      · unfold ProofRel
        refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, hstage_eq 0 (by decide), rfl, hvars, hlit, hrefs, hcnt, rfl, rfl, hcmd,
          hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
      · exact hk0
  · -- A word.
    have hb : (kind != 2) = false := by rw [hk2, decide_eq_false hnot2]
    simp only [hb, Bool.false_eq_true, ite_false]
    have hw99 := rup_word_spec proof state' 99 fuel t hstart hstop ⟨by omega, by omega⟩
    rw [hw99]
    simp only []
    have hcom : (s.first && decide (Word (toBytes proof) t (99 : UInt8).toNat)) =
        (p.first && decide (Word (toBytes proof) t 99)) := by rw [hfirst]; rfl
    have hmodel : OakText.proofStep (toBytes proof) t p =
        (let comment := p.comment || (p.first && decide (Word (toBytes proof) t 99))
        if comment then ({ p with first := false, comment := comment }, false)
        else if p.stage = 0 then
          ({ p with
              valid := decide (t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0))
              stage := 1
              command := ⟨true, t.magnitude, p.pool.length, 0, p.refs.length, 0⟩
              first := false
              comment := comment }, false)
        else if p.stage = 1 ∧ Word (toBytes proof) t 100 then
          ({ p with
              command := { p.command with addition := false }
              stage := 4
              first := false
              comment := comment }, false)
        else
          let stage := if p.stage = 1 then 2 else p.stage
          if stage = 2 then
            if t.magnitude = 0 then
              ({ p with valid := decide (t.sign ≠ 0), stage := 3, first := false, comment := comment }, false)
            else if decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables ∧ p.pool.length < 4096) then
              ({ p with
                  valid := true
                  stage := stage
                  pool := p.pool ++ [OakText.encoded t.magnitude t.sign]
                  command := { p.command with count := p.command.count + 1 }
                  first := false
                  comment := comment }, false)
            else ({ p with valid := false, stage := stage, first := false, comment := comment }, false)
          else if t.magnitude = 0 then
            ({ p with
                valid := decide (t.sign ≠ 0 ∧ stage ≠ 5) && (if stage = 4 then decide (Word (toBytes proof) t 48) else true)
                stage := 5
                first := false
                comment := comment }, false)
          else if decide (t.sign ≠ 0 ∧ stage ≠ 5) && decide (t.sign = 1 ∧ p.refs.length < 4096) then
            ({ p with
                valid := true
                stage := stage
                refs := p.refs ++ [t.magnitude]
                command := { p.command with refsCount := p.command.refsCount + 1 }
                first := false
                comment := comment }, false)
          else ({ p with valid := false, stage := stage, first := false, comment := comment }, false)) := by
      unfold OakText.proofStep
      rw [if_neg hnot2]
    rw [hmodel]
    by_cases hfw : (p.first && decide (Word (toBytes proof) t 99)) = true
    · have hfw' : (s.first && decide (Word (toBytes proof) t (99 : UInt8).toNat)) = true := by rw [hcom, hfw]
      have hcm : (p.comment || (p.first && decide (Word (toBytes proof) t 99))) = true := by rw [hfw, Bool.or_true]
      simp only [hfw', ite_true, hcm, Bool.not_true, Bool.false_eq_true, ite_false, pure]
      refine ⟨{ s with
          scan := state'
          valid := true
          first := false
          comment := true
          done := false }, rfl, ?_, ?_⟩
      · unfold ProofRel
        refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, hvalid.symm, hstage, hvars, hlit, hrefs, hcnt, rfl, rfl, hcmd,
          hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
      · rfl
    · have hfw' : (s.first && decide (Word (toBytes proof) t (99 : UInt8).toNat)) = false := by
        rw [hcom]; exact Bool.eq_false_iff.mpr hfw
      have hcm : (p.comment || (p.first && decide (Word (toBytes proof) t 99))) = p.comment := by
        rw [Bool.eq_false_iff.mpr hfw, Bool.or_false]
      simp only [hfw', Bool.false_eq_true, ite_false, hcm, pure]
      by_cases hcc : p.comment = true
      · have hsc : (!s.comment) = false := by rw [hcomment, hcc]; rfl
        simp only [hcc, ite_true, hsc, Bool.false_eq_true, ite_false]
        refine ⟨{ s with
            scan := state'
            valid := true
            first := false
            done := false }, rfl, ?_, ?_⟩
        · unfold ProofRel
          refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, hvalid.symm, hstage, hvars, hlit, hrefs, hcnt, rfl,
            by rw [hcomment, hcc], hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
        · rfl
      · have hcf : p.comment = false := Bool.eq_false_iff.mpr hcc
        have hsc : (!s.comment) = true := by rw [hcomment, hcf]; rfl
        simp only [hcf, Bool.false_eq_true, ite_false, hsc, ite_true]
        -- Stage 0: the command head.
        by_cases hst0 : p.stage = 0
        · have hb0 : (s.stage == 0) = true := by rw [hstage_eq 0 (by decide), decide_eq_true hst0]
          simp only [hb0, ite_true, if_pos hst0, hsign0, hsign1, hmag0]
          have hvalid0 : (decide (t.sign ≠ 0) && (decide (t.sign = 1) || decide (t.magnitude = 0))) =
              decide (t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0)) := by
            simp only [Bool.decide_and, Bool.decide_or]
          rw [hvalid0]
          refine ⟨{ s with
              scan := state'
              valid := decide (t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0))
              stage := 1
              first := false
              comment := s.comment
              done := false
              command := {
                addition := true
                id_ := state'.getD 3 0
                start := s.literals
                count := 0
                refs_start := s.references
                refs_count := 0 } }, rfl, ?_, ?_⟩
          · unfold ProofRel
            refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, rfl, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
              ⟨rfl, hmag, hlit, rfl, hrefs, rfl⟩, hpoolle, hrefsle, hcmdsle, Nat.zero_le _, Nat.zero_le _,
              hpoolpre, hrefspre, hcmdpre, hns⟩
          · rfl
        · have hb0 : (s.stage == 0) = false := by rw [hstage_eq 0 (by decide), decide_eq_false hst0]
          simp only [hb0, Bool.false_eq_true, ite_false, if_neg hst0]
          have hw100 := rup_word_spec proof state' 100 fuel t hstart hstop ⟨by omega, by omega⟩
          rw [hw100]
          simp only []
          have hdel : (s.stage == 1 && decide (Word (toBytes proof) t (100 : UInt8).toNat)) =
              decide (p.stage = 1 ∧ Word (toBytes proof) t 100) := by
            rw [hstage_eq 1 (by decide), Bool.decide_and]; rfl
          rw [hdel]
          by_cases hdw : p.stage = 1 ∧ Word (toBytes proof) t 100
          · -- The deletion keyword.
            simp only [decide_eq_true hdw, ite_true, if_pos hdw]
            refine ⟨{ s with
                scan := state'
                valid := true
                stage := 4
                first := false
                comment := s.comment
                done := false
                command := { s.command with addition := false } }, rfl, ?_, ?_⟩
            · unfold ProofRel
              refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, hvalid.symm, rfl, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                ⟨rfl, hcmd.2.1, hcmd.2.2.1, hcmd.2.2.2.1, hcmd.2.2.2.2.1, hcmd.2.2.2.2.2⟩,
                hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
            · rfl
          · simp only [decide_eq_false hdw, Bool.false_eq_true, ite_false, if_neg hdw]
            -- The stage promotion: a second word after the head is a literal.
            by_cases hst1 : p.stage = 1
            · have hb1 : (s.stage == 1) = true := by rw [hstage_eq 1 (by decide), decide_eq_true hst1]
              simp only [hb1, ite_true, if_pos hst1]

              -- The literal stage: a zero ends the clause, a literal joins the pool.
              have hne5 : ((2 : UInt32) != 5) = true := by decide
              have heq2 : ((2 : UInt32) == 2) = true := by decide
              simp only [hne5, Bool.and_true, heq2, ite_true]
              by_cases hm : t.magnitude = 0
              · have hbm : (state'.getD 3 0 == 0) = true := by rw [hmag0, decide_eq_true hm]
                simp only [hbm, ite_true, if_pos hm, hsign0]
                refine ⟨{ s with
                    scan := state'
                    valid := decide (t.sign ≠ 0)
                    stage := 3
                    first := false
                    comment := s.comment
                    done := false }, rfl, ?_, ?_⟩
                · unfold ProofRel
                  refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, rfl, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                    hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
                · rfl
              · have hbm : (state'.getD 3 0 == 0) = false := by rw [hmag0, decide_eq_false hm]
                simp only [hbm, Bool.false_eq_true, ite_false, if_neg hm, hsign0, hlevars, hlit4096]
                have hcondE : (decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables) && decide (p.pool.length < 4096)) =
                    (decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables ∧ p.pool.length < 4096)) := by
                  simp only [Bool.decide_and, Bool.and_assoc]
                rw [hcondE]
                by_cases hcond : (decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables ∧ p.pool.length < 4096)) = true
                · have hparts := (Bool.and_eq_true _ _).mp hcond
                  have hroom : p.pool.length < 4096 := (of_decide_eq_true hparts.2).2
                  obtain ⟨e, he, heval⟩ := rup_encoded_spec (state'.getD 3 0) (state'.getD 4 0) fuel
                    (by rw [hmag]; omega) (by rw [hmag]; exact hlimit)
                  simp only [hcond, ite_true, he]
                  have hlitsucc : (s.literals + 1).toNat = p.pool.length + 1 := by
                    rw [UInt32.toNat_add, hlit, toNat_ofNat32 1 (by decide)]
                    exact Nat.mod_eq_of_lt (by omega)
                  have hcntsucc : (s.command.count + 1).toNat = p.command.count + 1 := by
                    rw [UInt32.toNat_add, hcmd.2.2.2.1, toNat_ofNat32 1 (by decide)]
                    exact Nat.mod_eq_of_lt (by omega)
                  refine ⟨{ s with
                      pool := s.pool.setIfInBounds s.literals.toNat e
                      scan := state'
                      valid := true
                      stage := (2 : UInt32)
                      literals := s.literals + 1
                      first := false
                      comment := s.comment
                      done := false
                      command := { s.command with count := s.command.count + 1 } }, rfl, ?_, ?_⟩
                  · unfold ProofRel
                    refine ⟨hsz, hnext, by rw [size_set]; exact hpool5, hrefs5, hcmds5, rfl, rfl, hvars,
                      by simp [hlitsucc], hrefs, hcnt, rfl, by rw [hcomment, hcf],
                      ⟨hcmd.1, hcmd.2.1, hcmd.2.2.1, hcntsucc, hcmd.2.2.2.2.1, hcmd.2.2.2.2.2⟩,
                      by simp; omega, hrefsle, hcmdsle, by simp; omega, hcrefs, ?_, hrefspre, hcmdpre, hns⟩
                    intro i hi
                    have hi' : i < (p.pool ++ [OakText.encoded t.magnitude t.sign]).length := hi
                    simp only [List.length_append, List.length_singleton] at hi'
                    by_cases hil : i < p.pool.length
                    · rw [getD_set_ne _ _ _ _ (by omega), list_getD_append_lt _ _ _ hil]
                      exact hpoolpre i hil
                    · have hieq : i = p.pool.length := by omega
                      subst hieq
                      rw [← hlit, getD_set_self _ _ _ (by rw [hpool5]; omega), hlit, list_getD_append_self, heval, hmag, hsign]
                  · rfl
                · have hcondf := Bool.eq_false_iff.mpr hcond
                  simp only [hcondf, Bool.false_eq_true, ite_false]
                  refine ⟨{ s with
                      scan := state'
                      valid := false
                      stage := (2 : UInt32)
                      first := false
                      comment := s.comment
                      done := false }, rfl, ?_, ?_⟩
                  · unfold ProofRel
                    refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, rfl, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                      hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
                  · rfl

            · have hb1 : (s.stage == 1) = false := by rw [hstage_eq 1 (by decide), decide_eq_false hst1]
              simp only [hb1, Bool.false_eq_true, ite_false, if_neg hst1]
              by_cases hst2 : p.stage = 2
              · have hne5' : (s.stage != 5) = true := by
                  rw [bne_ofNat32 s.stage 5 (by decide), hstage, hst2]; rfl
                have heq2' : (s.stage == 2) = true := by rw [hstage_eq 2 (by decide), decide_eq_true hst2]
                have hst2e : s.stage = 2 := by
                  apply UInt32.toNat_inj.mp; rw [hstage, hst2]; rfl
                rw [if_pos hst2]

                -- The literal stage: a zero ends the clause, a literal joins the pool.
                have hne5 : (s.stage != 5) = true := hne5'
                have heq2 : (s.stage == 2) = true := heq2'
                simp only [hne5, Bool.and_true, heq2, ite_true]
                by_cases hm : t.magnitude = 0
                · have hbm : (state'.getD 3 0 == 0) = true := by rw [hmag0, decide_eq_true hm]
                  simp only [hbm, ite_true, if_pos hm, hsign0]
                  refine ⟨{ s with
                      scan := state'
                      valid := decide (t.sign ≠ 0)
                      stage := 3
                      first := false
                      comment := s.comment
                      done := false }, rfl, ?_, ?_⟩
                  · unfold ProofRel
                    refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, rfl, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                      hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
                  · rfl
                · have hbm : (state'.getD 3 0 == 0) = false := by rw [hmag0, decide_eq_false hm]
                  simp only [hbm, Bool.false_eq_true, ite_false, if_neg hm, hsign0, hlevars, hlit4096]
                  have hcondE : (decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables) && decide (p.pool.length < 4096)) =
                      (decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables ∧ p.pool.length < 4096)) := by
                    simp only [Bool.decide_and, Bool.and_assoc]
                  rw [hcondE]
                  by_cases hcond : (decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables ∧ p.pool.length < 4096)) = true
                  · have hparts := (Bool.and_eq_true _ _).mp hcond
                    have hroom : p.pool.length < 4096 := (of_decide_eq_true hparts.2).2
                    obtain ⟨e, he, heval⟩ := rup_encoded_spec (state'.getD 3 0) (state'.getD 4 0) fuel
                      (by rw [hmag]; omega) (by rw [hmag]; exact hlimit)
                    simp only [hcond, ite_true, he]
                    have hlitsucc : (s.literals + 1).toNat = p.pool.length + 1 := by
                      rw [UInt32.toNat_add, hlit, toNat_ofNat32 1 (by decide)]
                      exact Nat.mod_eq_of_lt (by omega)
                    have hcntsucc : (s.command.count + 1).toNat = p.command.count + 1 := by
                      rw [UInt32.toNat_add, hcmd.2.2.2.1, toNat_ofNat32 1 (by decide)]
                      exact Nat.mod_eq_of_lt (by omega)
                    refine ⟨{ s with
                        pool := s.pool.setIfInBounds s.literals.toNat e
                        scan := state'
                        valid := true
                        stage := s.stage
                        literals := s.literals + 1
                        first := false
                        comment := s.comment
                        done := false
                        command := { s.command with count := s.command.count + 1 } }, rfl, ?_, ?_⟩
                    · unfold ProofRel
                      refine ⟨hsz, hnext, by rw [size_set]; exact hpool5, hrefs5, hcmds5, rfl, hstage, hvars,
                        by simp [hlitsucc], hrefs, hcnt, rfl, by rw [hcomment, hcf],
                        ⟨hcmd.1, hcmd.2.1, hcmd.2.2.1, hcntsucc, hcmd.2.2.2.2.1, hcmd.2.2.2.2.2⟩,
                        by simp; omega, hrefsle, hcmdsle, by simp; omega, hcrefs, ?_, hrefspre, hcmdpre, hns⟩
                      intro i hi
                      have hi' : i < (p.pool ++ [OakText.encoded t.magnitude t.sign]).length := hi
                      simp only [List.length_append, List.length_singleton] at hi'
                      by_cases hil : i < p.pool.length
                      · rw [getD_set_ne _ _ _ _ (by omega), list_getD_append_lt _ _ _ hil]
                        exact hpoolpre i hil
                      · have hieq : i = p.pool.length := by omega
                        subst hieq
                        rw [← hlit, getD_set_self _ _ _ (by rw [hpool5]; omega), hlit, list_getD_append_self, heval, hmag, hsign]
                    · rfl
                  · have hcondf := Bool.eq_false_iff.mpr hcond
                    simp only [hcondf, Bool.false_eq_true, ite_false]
                    refine ⟨{ s with
                        scan := state'
                        valid := false
                        stage := s.stage
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold ProofRel
                      refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, hstage, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                        hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
                    · rfl

              · have heq2' : (s.stage == 2) = false := by rw [hstage_eq 2 (by decide), decide_eq_false hst2]
                have hne5s : (s.stage != 5) = decide (p.stage ≠ 5) := by
                  rw [bne_ofNat32 s.stage 5 (by decide), hstage, beq_nat_decide, decide_not]
                simp only [heq2', Bool.false_eq_true, ite_false, if_neg hst2, hsign0, hne5s]
                have hvalid5 : (decide (t.sign ≠ 0) && decide (p.stage ≠ 5)) = decide (t.sign ≠ 0 ∧ p.stage ≠ 5) := by
                  rw [Bool.decide_and]
                rw [hvalid5]
                by_cases hm : t.magnitude = 0
                · have hbm : (state'.getD 3 0 == 0) = true := by rw [hmag0, decide_eq_true hm]
                  simp only [hbm, ite_true, if_pos hm]
                  by_cases hst4 : p.stage = 4
                  · have hb4 : (s.stage == 4) = true := by rw [hstage_eq 4 (by decide), decide_eq_true hst4]
                    have hw48 := rup_word_spec proof state' 48 fuel t hstart hstop ⟨by omega, by omega⟩
                    simp only [hb4, ite_true, if_pos hst4, hw48]
                    refine ⟨{ s with
                        scan := state'
                        valid := decide (t.sign ≠ 0 ∧ p.stage ≠ 5) && decide (Word (toBytes proof) t (48 : UInt8).toNat)
                        stage := 5
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold ProofRel
                      refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, rfl, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                        hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
                    · rfl
                  · have hb4 : (s.stage == 4) = false := by rw [hstage_eq 4 (by decide), decide_eq_false hst4]
                    simp only [hb4, Bool.false_eq_true, ite_false, if_neg hst4, Bool.and_true]
                    refine ⟨{ s with
                        scan := state'
                        valid := decide (t.sign ≠ 0 ∧ p.stage ≠ 5)
                        stage := 5
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold ProofRel
                      refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, rfl, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                        hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
                    · rfl
                · have hbm : (state'.getD 3 0 == 0) = false := by rw [hmag0, decide_eq_false hm]
                  simp only [hbm, Bool.false_eq_true, ite_false, if_neg hm, hsign1, hrefs4096]
                  have hcondE : (decide (t.sign ≠ 0 ∧ p.stage ≠ 5) && decide (t.sign = 1) && decide (p.refs.length < 4096)) =
                      (decide (t.sign ≠ 0 ∧ p.stage ≠ 5) && decide (t.sign = 1 ∧ p.refs.length < 4096)) := by
                    simp only [Bool.decide_and, Bool.and_assoc]
                  rw [hcondE]
                  by_cases hcond : (decide (t.sign ≠ 0 ∧ p.stage ≠ 5) && decide (t.sign = 1 ∧ p.refs.length < 4096)) = true
                  · have hparts := (Bool.and_eq_true _ _).mp hcond
                    have hroom : p.refs.length < 4096 := (of_decide_eq_true hparts.2).2
                    simp only [hcond, ite_true]
                    have hrefsucc : (s.references + 1).toNat = p.refs.length + 1 := by
                      rw [UInt32.toNat_add, hrefs, toNat_ofNat32 1 (by decide)]
                      exact Nat.mod_eq_of_lt (by omega)
                    have hrcsucc : (s.command.refs_count + 1).toNat = p.command.refsCount + 1 := by
                      rw [UInt32.toNat_add, hcmd.2.2.2.2.2, toNat_ofNat32 1 (by decide)]
                      exact Nat.mod_eq_of_lt (by omega)
                    refine ⟨{ s with
                        refs := s.refs.setIfInBounds s.references.toNat (state'.getD 3 0)
                        scan := state'
                        valid := true
                        first := false
                        comment := s.comment
                        done := false
                        references := s.references + 1
                        command := { s.command with refs_count := s.command.refs_count + 1 } }, rfl, ?_, ?_⟩
                    · unfold ProofRel
                      refine ⟨hsz, hnext, hpool5, by rw [size_set]; exact hrefs5, hcmds5, rfl, hstage, hvars, hlit,
                        by simp [hrefsucc], hcnt, rfl, by rw [hcomment, hcf],
                        ⟨hcmd.1, hcmd.2.1, hcmd.2.2.1, hcmd.2.2.2.1, hcmd.2.2.2.2.1, hrcsucc⟩,
                        hpoolle, by simp; omega, hcmdsle, hccount, by simp; omega, hpoolpre, ?_, hcmdpre, hns⟩
                      intro i hi
                      have hi' : i < (p.refs ++ [t.magnitude]).length := hi
                      simp only [List.length_append, List.length_singleton] at hi'
                      by_cases hil : i < p.refs.length
                      · rw [getD_set_ne _ _ _ _ (by omega), list_getD_append_lt _ _ _ hil]
                        exact hrefspre i hil
                      · have hieq : i = p.refs.length := by omega
                        subst hieq
                        rw [← hrefs, getD_set_self _ _ _ (by rw [hrefs5]; omega), hrefs, list_getD_append_self, hmag]
                    · rfl
                  · have hcondf := Bool.eq_false_iff.mpr hcond
                    simp only [hcondf, Bool.false_eq_true, ite_false]
                    refine ⟨{ s with
                        scan := state'
                        valid := false
                        first := false
                        comment := s.comment
                        done := false }, rfl, ?_, ?_⟩
                    · unfold ProofRel
                      refine ⟨hsz, hnext, hpool5, hrefs5, hcmds5, rfl, hstage, hvars, hlit, hrefs, hcnt, rfl, by rw [hcomment, hcf],
                        hcmd, hpoolle, hrefsle, hcmdsle, hccount, hcrefs, hpoolpre, hrefspre, hcmdpre, hns⟩
                    · rfl

/-- The model's LRAT step stops only at the end of the text. -/
theorem proofStep_stop (bytes : List Nat) (t : Token) (p : OakText.Proof)
    (h : (OakText.proofStep bytes t p).2 = false) : t.kind ≠ 0 := by
  unfold OakText.proofStep at h
  by_cases hk : t.kind ≠ 2
  · rw [if_pos hk] at h
    by_cases h5 : p.stage = 5
    · rw [if_pos h5] at h
      by_cases hroom : p.commands.length < 256
      · rw [if_pos hroom] at h; exact of_decide_eq_false h
      · rw [if_neg hroom] at h; exact of_decide_eq_false h
    · rw [if_neg h5] at h; exact of_decide_eq_false h
  · intro h0
    exact hk (by omega)

def ProofRelEnd (proof : Array UInt8) (s : ProofExt) (p : OakText.Proof) : Prop :=
  ∃ pos, ProofRel proof s pos p

/-- The extracted LRAT loop runs to the model's `proofLoop` result. -/
theorem proof_loop (proof : Array UInt8) (hs : proof.size ≤ 65536) :
    ∀ (m : Nat) (s : ProofExt) (pos : Nat) (p : OakText.Proof) (fuel : Nat),
      ProofRel proof s pos p → s.done = false → proof.size - pos < m → m + proof.size < fuel →
      ∃ (s' : ProofExt) (p' : OakText.Proof), s.run proof fuel = some s'.tuple ∧
        OakText.proofLoop (toBytes proof) pos p m = some p' ∧ ProofRelEnd proof s' p' := by
  intro m
  induction m with
  | zero => intro s pos p fuel _ _ hm; omega
  | succ m ih =>
    intro s pos p fuel hrel hdone hm hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hsize_f : proof.size < f := by omega
    by_cases hvalid : p.valid = true
    · obtain ⟨s1, hrun, hrel1, hdone1⟩ := proof_step proof hs s pos p f hrel hdone hvalid hsize_f
      have hmodel : OakText.proofLoop (toBytes proof) pos p (m + 1) =
          (if (OakText.proofStep (toBytes proof) (scan (toBytes proof) pos) p).2 then
            some (OakText.proofStep (toBytes proof) (scan (toBytes proof) pos) p).1
          else OakText.proofLoop (toBytes proof) (scan (toBytes proof) pos).next
            (OakText.proofStep (toBytes proof) (scan (toBytes proof) pos) p).1 m) := by
        simp only [OakText.proofLoop, hvalid, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hmodel, hrun]
      by_cases hstop : (OakText.proofStep (toBytes proof) (scan (toBytes proof) pos) p).2 = true
      · rw [if_pos hstop]
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        refine ⟨s1, _, ?_, rfl, ⟨_, hrel1⟩⟩
        unfold ProofExt.run
        rw [rup_text_check.loop4]
        have hd : (!s1.done && s1.valid) = false := by rw [hdone1, hstop]; rfl
        rw [if_neg (by rw [hd]; exact Bool.false_ne_true)]
        rfl
      · have hstop' := Bool.eq_false_iff.mpr hstop
        rw [if_neg (by rw [hstop']; exact Bool.false_ne_true)]
        have hkind := proofStep_stop _ _ _ hstop'
        have hrange := scan_range (toBytes proof) pos (by rw [toBytes_length]; exact hrel.pos_le)
        rw [toBytes_length] at hrange
        obtain ⟨-, -, hns, -, hadv⟩ := hrange
        have hpos := hadv hkind
        exact ih s1 _ _ f hrel1 (by rw [hdone1, hstop']) (by omega) (by omega)
    · have hvf : p.valid = false := Bool.eq_false_iff.mpr hvalid
      have hsv : (!s.done && s.valid) = false := by rw [hrel.valid_eq, hvf]; simp
      refine ⟨s, p, ?_, ?_, ⟨pos, hrel⟩⟩
      · unfold ProofExt.run
        rw [rup_text_check.loop4]
        rw [if_neg (by rw [hsv]; exact Bool.false_ne_true)]
        rfl
      · simp only [OakText.proofLoop, hvf, Bool.not_false, ite_true]

/-- The LRAT loop's starting state, as `rup_text_check` builds it from the
DIMACS loop's result: the closing check, the scanner reset, fresh tables. -/
def proofStart (s : CnfExt) : ProofExt :=
  { pool := s.pool, refs := Array.replicate 4096 0, commands := Array.replicate 256 default,
    scan := s.scan.setIfInBounds 0 0,
    valid := (((s.valid && (s.stage == 5)) && (s.clauses == s.expected)) && (s.pending == s.literals)),
    stage := 0, variables := s.variables, literals := s.literals, first := true, comment := false,
    done := false, count := 0, references := 0,
    command := { addition := true, id_ := 0, start := 0, count := 0, refs_start := 0, refs_count := 0 } }

/-- The LRAT start represents the model's `proofStart` of the DIMACS result. -/
theorem proofStart_rel (cnf proof : Array UInt8) (s : CnfExt) (pos : Nat) (c : OakText.Cnf)
    (hrel : CnfRel cnf s pos c) : ProofRel proof (proofStart s) 0 (OakText.proofStart c) := by
  obtain ⟨h5, hpos, hpool5, hinit5, hsizes5, hv, hstage, hvars, hexp, hcl, hlit, hpend, hfirst, hcomment,
    hpendle, hpoolle, hinitlen, hsizeslen, -, hexplim, hexp256, hpoolpre, hclpre, hle⟩ := hrel
  have hclosing : (((s.valid && (s.stage == 5)) && (s.clauses == s.expected)) && (s.pending == s.literals)) =
      OakText.closingCheck c := by
    unfold OakText.closingCheck
    rw [hv, beq_ofNat32 s.stage 5 (by decide), hstage, beq_nat_decide, beq_toNat32 s.clauses s.expected, hcl, hexp,
      beq_toNat32 s.pending s.literals, hpend, hlit]
    simp only [Bool.decide_and, Bool.and_assoc]
  unfold ProofRel proofStart OakText.proofStart
  refine ⟨by rw [size_set]; exact h5, by rw [getD_set_self _ _ _ (by rw [h5]; decide)]; rfl,
    hpool5, by simp, by simp, hclosing, rfl, hvars, hlit, rfl, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hpoolle, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    hpoolpre, ?_, ?_, Nat.zero_le _⟩
  · intro i hi; simp at hi
  · intro i hi; simp at hi

#print axioms proof_loop

/-! ## The whole decoder -/

/-- The entry guards on an invalid flag return at once, whatever the text. -/
theorem guard1_false (cnf : Array UInt8) (b : UInt32) (fuel : Nat) :
    rup_text_check.loop1 cnf false b (fuel + 1) = some (false, b) := by
  rw [rup_text_check.loop1]; simp

theorem guard2_false (proof : Array UInt8) (b : UInt32) (fuel : Nat) :
    rup_text_check.loop2 proof false b (fuel + 1) = some (false, b) := by
  rw [rup_text_check.loop2]; simp

/-- Both loops return an invalid state at once. -/
theorem cnf_run_invalid (cnf : Array UInt8) (s : CnfExt) (fuel : Nat) (h : s.valid = false) :
    s.run cnf (fuel + 1) = some s.tuple := by
  unfold CnfExt.run
  rw [rup_text_check.loop3]
  rw [if_neg (by rw [h]; simp)]
  rfl

theorem proof_run_invalid (proof : Array UInt8) (s : ProofExt) (fuel : Nat) (h : s.valid = false) :
    s.run proof (fuel + 1) = some s.tuple := by
  unfold ProofExt.run
  rw [rup_text_check.loop4]
  rw [if_neg (by rw [h]; simp)]
  rfl

/-- The model's loops return an invalid state at once as well. -/
theorem cnfLoop_invalid (bytes : List Nat) (pos : Nat) (c : OakText.Cnf) (m : Nat) (h : c.valid = false) :
    OakText.cnfLoop bytes pos c (m + 1) = some c := by
  simp [OakText.cnfLoop, h]

theorem proofLoop_invalid (bytes : List Nat) (pos : Nat) (p : OakText.Proof) (m : Nat) (h : p.valid = false) :
    OakText.proofLoop bytes pos p (m + 1) = some p := by
  simp [OakText.proofLoop, h]

/-- A prefix of a bounded array, as the view the decoder hands on. -/
theorem extract_size {α : Type} (a : Array α) (n : Nat) (hn : n ≤ a.size) : (a.extract 0 n).size = n := by
  rw [Array.size_extract]; omega

theorem extract_getD (a : Array UInt32) (n i : Nat) (hi : i < n) (hn : n ≤ a.size) :
    (a.extract 0 n).getD i 0 = a.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  simp only [Nat.sub_zero, Nat.zero_add]
  rw [if_pos (Nat.lt_min.mpr ⟨hi, by omega⟩)]

theorem extract_getD_cmd (a : Array RUPCommand) (n i : Nat) (hi : i < n) (hn : n ≤ a.size) :
    (a.extract 0 n).getD i default = a.getD i default := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  simp only [Nat.sub_zero, Nat.zero_add]
  rw [if_pos (Nat.lt_min.mpr ⟨hi, by omega⟩)]

/-- `OakText.layout` over byte lists: the model's two phases and the closing
test, as the transliteration spells them over strings. -/
def layoutBytes (cnfBytes proofBytes : List Nat) : Option Ranges.Layout :=
  match OakText.cnfPhase cnfBytes proofBytes with
  | none => none
  | some c =>
    match OakText.proofLoop proofBytes 0 (OakText.proofStart c) (proofBytes.length + 1) with
    | none => none
    | some p => if p.valid then some ⟨p.variables, p.pool, c.initial, c.sizes, p.refs, p.commands⟩ else none

theorem layout_eq (cnf proof : String) : OakText.layout cnf proof = layoutBytes (bytesOf cnf) (bytesOf proof) := rfl

/-- The arrays the extracted decoder hands to the stream checker represent a
model layout: the same variable count, and the same elements at every index
of the same length. -/
def LayoutRel (raw : Ranges.Layout) (variables : UInt32) (pool initial sizes refs : Array UInt32)
    (commands : Array RUPCommand) : Prop :=
  variables.toNat = raw.variables ∧
  pool.size = raw.pool.length ∧ (∀ i, i < raw.pool.length → (pool.getD i 0).toNat = raw.pool.getD i 0) ∧
  initial.size = raw.starts.length ∧ (∀ i, i < raw.starts.length → (initial.getD i 0).toNat = raw.starts.getD i 0) ∧
  sizes.size = raw.sizes.length ∧ (∀ i, i < raw.sizes.length → (sizes.getD i 0).toNat = raw.sizes.getD i 0) ∧
  refs.size = raw.refs.length ∧ (∀ i, i < raw.refs.length → (refs.getD i 0).toNat = raw.refs.getD i 0) ∧
  commands.size = raw.commands.length ∧
  (∀ i (h : i < raw.commands.length), CmdRel (commands.getD i default) (raw.commands[i]'h))

theorem toUInt32_le_65536 (n : Nat) (hn : n < UInt32.size) :
    decide (n.toUInt32 ≤ 65536) = decide (n ≤ 65536) := by
  rw [decide_le_toNat]
  show decide ((UInt32.ofNat n).toNat ≤ (65536 : UInt32).toNat) = _
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
  rfl

/-- The decoder theorem: the extracted `rup_text_check` computes the model's
layout. On every pair of texts below the `UInt32` range, with fuel above
both texts twice over, the extraction either rejects where the model's
`layout` is `none`, or hands the stream checker arrays that represent the
model's `Layout`, so the acceptance of the extracted program is the
acceptance of the extracted stream checker on the model's layout. -/
theorem rup_text_check_spec (cnf proof : Array UInt8) (hc : cnf.size < UInt32.size)
    (hp : proof.size < UInt32.size) (fuel : Nat) (hf : 2 * cnf.size + 2 * proof.size + 3 < fuel) :
    ∃ (valid : Bool) (variables : UInt32) (pool initial sizes refs : Array UInt32) (commands : Array RUPCommand),
      rup_text_check cnf proof fuel =
        (if valid then rup_stream_check pool initial sizes refs commands variables fuel else some false) ∧
      (valid = false → layoutBytes (toBytes cnf) (toBytes proof) = none) ∧
      (valid = true → ∃ raw, layoutBytes (toBytes cnf) (toBytes proof) = some raw ∧
        LayoutRel raw variables pool initial sizes refs commands) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hsz1 := toUInt32_le_65536 cnf.size hc
  have hsz2 := toUInt32_le_65536 proof.size hp
  have hlen1 : (toBytes cnf).length = cnf.size := toBytes_length cnf
  have hlen2 : (toBytes proof).length = proof.size := toBytes_length proof
  unfold rup_text_check
  simp only [hsz1, hsz2]
  by_cases hsmall : cnf.size ≤ 65536 ∧ proof.size ≤ 65536
  · obtain ⟨hcs, hps⟩ := hsmall
    simp only [decide_eq_true hcs, decide_eq_true hps, Bool.true_and]
    obtain ⟨b1, hg1⟩ := guard1_spec cnf hcs (f + 1) true 0 (by simp) (by simp; omega)
    simp only [hg1, bind, Option.bind, Bool.true_and, UInt32.toNat_zero, List.drop_zero]
    obtain ⟨b2, hg2⟩ := guard2_spec proof hps (f + 1) ((toBytes cnf).all fun x => decide (x ≤ 127)) 0
      (by simp) (by simp; omega)
    simp only [hg2, UInt32.toNat_zero, List.drop_zero]
    -- The DIMACS phase.
    have hv : (((toBytes cnf).all fun x => decide (x ≤ 127)) && ((toBytes proof).all fun x => decide (x ≤ 127))) =
        (OakText.guard (toBytes cnf) && OakText.guard (toBytes proof)) := by
      unfold OakText.guard
      rw [hlen1, hlen2, decide_eq_true hcs, decide_eq_true hps, Bool.true_and, Bool.true_and]
    obtain ⟨s3, c3, hrun3, hmodel3, ⟨pos3, hrel3⟩⟩ := cnf_loop cnf hcs (cnf.size + 1)
      (cnfStart (OakText.guard (toBytes cnf) && OakText.guard (toBytes proof))) 0
      { OakText.initialCnf with valid := (OakText.guard (toBytes cnf) && OakText.guard (toBytes proof)) } (f + 1)
      (cnfStart_rel cnf _) rfl (by omega) (by omega)
    have hrun3' : rup_text_check.loop3 cnf (Array.replicate 4096 0) (Array.replicate 256 0) (Array.replicate 256 0)
        ((Array.replicate 5 (0 : UInt32)).setIfInBounds 0 (0 : UInt32))
        (OakText.guard (toBytes cnf) && OakText.guard (toBytes proof)) 0 0 0 0 0 0 true false false (f + 1) =
        some s3.tuple := hrun3
    rw [hv, hrun3']
    simp only [CnfExt.tuple]
    -- The LRAT phase.
    obtain ⟨s4, p4, hrun4, hmodel4, ⟨pos4, hrel4⟩⟩ := proof_loop proof hps (proof.size + 1) (proofStart s3) 0
      (OakText.proofStart c3) (f + 1) (proofStart_rel cnf proof s3 pos3 c3 hrel3) rfl (by omega) (by omega)
    have hrun4' : rup_text_check.loop4 proof s3.pool (Array.replicate 4096 0) (Array.replicate 256 default)
        (s3.scan.setIfInBounds 0 0)
        (((s3.valid && (s3.stage == 5)) && (s3.clauses == s3.expected)) && (s3.pending == s3.literals))
        0 s3.variables s3.literals true false false 0 0
        { addition := true, id_ := 0, start := 0, count := 0, refs_start := 0, refs_count := 0 } (f + 1) =
        some s4.tuple := hrun4
    rw [hrun4']
    simp only [ProofExt.tuple]
    -- The model's layout.
    have hphase : OakText.cnfPhase (toBytes cnf) (toBytes proof) = some c3 := by
      unfold OakText.cnfPhase
      rw [hlen1]
      exact hmodel3
    have hlayout : layoutBytes (toBytes cnf) (toBytes proof) =
        (if p4.valid then some ⟨p4.variables, p4.pool, c3.initial, c3.sizes, p4.refs, p4.commands⟩ else none) := by
      unfold layoutBytes
      rw [hphase]
      simp only [hlen2, hmodel4]
    obtain ⟨-, -, hpool5, hinit5, hsizes5, -, -, hvars3, -, hcl3, -, -, -, -, -, -, hinitlen, hsizeslen, hcl256, -, -,
      -, hclpre, -⟩ := hrel3
    obtain ⟨-, -, hpool4, hrefs4, hcmds4, hv4, -, -, hlit4, hrefs4', hcnt4, -, -, -, hpoolle4, hrefsle4, hcmdsle4,
      -, -, hpoolpre4, hrefspre4, hcmdpre4, -⟩ := hrel4
    have hvars4 : p4.variables = (OakText.proofStart c3).variables :=
      OakText.proofLoop_variables (toBytes proof) _ _ _ _ hmodel4
    refine ⟨s4.valid, s3.variables, s4.pool.extract 0 s4.literals.toNat, s3.initial.extract 0 s3.clauses.toNat,
      s3.sizes.extract 0 s3.clauses.toNat, s4.refs.extract 0 s4.references.toNat,
      s4.commands.extract 0 s4.count.toNat, ?_, ?_, ?_⟩
    · by_cases hval : s4.valid = true
      · simp only [hval, ite_true]
        cases rup_stream_check (s4.pool.extract 0 s4.literals.toNat) (s3.initial.extract 0 s3.clauses.toNat)
          (s3.sizes.extract 0 s3.clauses.toNat) (s4.refs.extract 0 s4.references.toNat)
          (s4.commands.extract 0 s4.count.toNat) s3.variables (f + 1) <;> rfl
      · have hvf := Bool.eq_false_iff.mpr hval
        simp only [hvf, Bool.false_eq_true, ite_false]
        rfl
    · intro hval
      rw [hlayout, ← hv4, hval]
      rfl
    · intro hval
      rw [hlayout, ← hv4, hval, if_pos rfl]
      refine ⟨_, rfl, ?_⟩
      unfold LayoutRel
      refine ⟨by rw [hvars3, hvars4]; rfl,
        by rw [extract_size _ _ (by omega), hlit4],
        fun i hi => by
          have hi' : i < p4.pool.length := hi
          rw [extract_getD _ _ _ (by omega) (by omega)]; exact hpoolpre4 i hi',
        by rw [extract_size _ _ (by omega), hcl3, hinitlen],
        fun i hi => by
          have hi' : i < c3.initial.length := hi
          rw [extract_getD _ _ _ (by omega) (by omega)]; exact (hclpre i (by omega)).1,
        by rw [extract_size _ _ (by omega), hcl3, hsizeslen],
        fun i hi => by
          have hi' : i < c3.sizes.length := hi
          rw [extract_getD _ _ _ (by omega) (by omega)]; exact (hclpre i (by omega)).2,
        by rw [extract_size _ _ (by omega), hrefs4'],
        fun i hi => by
          have hi' : i < p4.refs.length := hi
          rw [extract_getD _ _ _ (by omega) (by omega)]; exact hrefspre4 i hi',
        by rw [extract_size _ _ (by omega), hcnt4],
        fun i hi => by
          have hi' : i < p4.commands.length := hi
          rw [extract_getD_cmd _ _ _ (by omega) (by omega)]; exact hcmdpre4 i hi'⟩
  · -- A text over the size limit: rejected before anything is scanned.
    have hguard : (decide (cnf.size ≤ 65536) && decide (proof.size ≤ 65536)) = false := by
      rcases Decidable.not_and_iff_or_not.mp hsmall with h | h
      · rw [decide_eq_false h]; rfl
      · rw [decide_eq_false h]; simp
    simp only [hguard, guard1_false, bind, Option.bind, guard2_false]
    have hrun3 := cnf_run_invalid cnf (cnfStart false) f rfl
    have hrun3' : rup_text_check.loop3 cnf (Array.replicate 4096 0) (Array.replicate 256 0) (Array.replicate 256 0)
        ((Array.replicate 5 (0 : UInt32)).setIfInBounds 0 (0 : UInt32))
        false 0 0 0 0 0 0 true false false (f + 1) = some (cnfStart false).tuple := hrun3
    rw [hrun3']
    simp only [CnfExt.tuple, cnfStart, Bool.false_and]
    have hrun4 := proof_run_invalid proof (proofStart (cnfStart false)) f (by simp [proofStart, cnfStart])
    have hrun4' : rup_text_check.loop4 proof (Array.replicate 4096 0) (Array.replicate 4096 0)
        (Array.replicate 256 default) (((Array.replicate 5 (0 : UInt32)).setIfInBounds 0 (0 : UInt32)).setIfInBounds 0 0)
        false 0 0 0 true false false 0 0
        { addition := true, id_ := 0, start := 0, count := 0, refs_start := 0, refs_count := 0 } (f + 1) =
        some (proofStart (cnfStart false)).tuple := by
      have := hrun4
      unfold ProofExt.run proofStart cnfStart at this
      simp only [Bool.false_and] at this
      exact this
    rw [hrun4']
    simp only [ProofExt.tuple, proofStart, cnfStart, Bool.false_and]
    refine ⟨false, 0, Array.empty, Array.empty, Array.empty, Array.empty, Array.empty, rfl, fun _ => ?_,
      fun h => absurd h Bool.false_ne_true⟩
    -- The model rejects too: the guard fails, both loops return invalid states.
    have hmg : (OakText.guard (toBytes cnf) && OakText.guard (toBytes proof)) = false := by
      unfold OakText.guard
      rw [hlen1, hlen2]
      rcases Decidable.not_and_iff_or_not.mp hsmall with h | h
      · rw [decide_eq_false h]; rfl
      · rw [decide_eq_false h]; simp
    unfold layoutBytes OakText.cnfPhase
    rw [hlen1, hmg, cnfLoop_invalid _ _ _ _ rfl]
    simp only []
    rw [hlen2, proofLoop_invalid _ _ _ _ (by simp [OakText.proofStart, OakText.closingCheck])]
    simp [OakText.proofStart, OakText.closingCheck]

#print axioms rup_text_check_spec

end OakVerification.Extraction
