import OakTextExtracted
import ScannerState

set_option autoImplicit false
namespace OakVerification.Extraction
open Scanner Extracted

/-! The extracted scanner refines the proved scanner (docs/spec/95-extraction.md,
roadmap step 3's second increment). `Extracted.rup_token` is the compiler's
translation of `rup_token` in `self_hosted_rup.oak`; `Scanner.scan` is the
byte-list model whose agreement with compiled Oak the scanner gate compares
token by token. `rup_token_scan` below turns that gate into a theorem: on any
text of at most 65536 bytes, from any cursor inside it, with fuel above the
text length, the extracted scanner returns exactly the token the model
returns — kind, next cursor, start, stop, magnitude, and sign. -/

/-- The byte list the models read is the extracted array's elements. -/
def toBytes (text : Array UInt8) : List Nat := text.toList.map UInt8.toNat

theorem toBytes_length (text : Array UInt8) : (toBytes text).length = text.size := by
  simp [toBytes]

theorem getD_toBytes (text : Array UInt8) (i : Nat) :
    (text.getD i 0).toNat = (toBytes text).getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [toBytes, List.getElem?_map, Array.getElem?_toList]
  cases text[i]? <;> simp

theorem getD_toBytes_of_lt (text : Array UInt8) (i : Nat) (h : i < text.size) :
    (toBytes text).getD i 0 = (toBytes text)[i]'(by rw [toBytes_length]; exact h) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
  rfl

/-- Sizes below 2^32 survive the round trip through `UInt32`. -/
theorem toNat_size (text : Array UInt8) (h : text.size ≤ 65536) :
    text.size.toUInt32.toNat = text.size := by
  show (UInt32.ofNat text.size).toNat = text.size
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem toNat_succ (a : UInt32) (h : a.toNat < 65536) : (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add, UInt32.toNat_one]
  exact Nat.mod_eq_of_lt (by omega)

theorem lt_size_iff (text : Array UInt8) (pos : UInt32) (h : text.size ≤ 65536) :
    (decide (pos < text.size.toUInt32) = true) ↔ pos.toNat < text.size := by
  rw [decide_eq_true_iff, UInt32.lt_iff_toNat_lt, toNat_size text h]

/-- Byte equality against a small literal is equality of the byte's value. -/
theorem beq_ofNat (b : UInt8) (n : Nat) (hn : n < 256) :
    (b == (OfNat.ofNat n : UInt8)) = (b.toNat == n) := by
  rcases Bool.eq_false_or_eq_true (b == (OfNat.ofNat n : UInt8)) with heq | heq
  · rw [heq]
    have : b = OfNat.ofNat n := by simpa using heq
    subst this
    simp [UInt8.toNat_ofNat_of_lt (by simpa [UInt8.size] using hn)]
  · rw [heq]
    have hne : b ≠ OfNat.ofNat n := by simpa using heq
    symm
    apply beq_eq_false_iff_ne.mpr
    intro hb
    apply hne
    apply UInt8.toNat_inj.mp
    rw [hb, UInt8.toNat_ofNat_of_lt (by simpa [UInt8.size] using hn)]

/-- `rup_space` is the model's `space` on the byte's value. -/
theorem rup_space_eq (b : UInt8) (fuel : Nat) : rup_space b fuel = some (space b.toNat) := by
  simp only [rup_space, space, pure, Option.some.injEq]
  rw [beq_ofNat b 32 (by decide), beq_ofNat b 9 (by decide), beq_ofNat b 13 (by decide),
    beq_ofNat b 11 (by decide), beq_ofNat b 12 (by decide)]

/-- One step of `countWhile` over a suffix of the byte list. -/
theorem countWhile_drop (p : Nat → Bool) (l : List Nat) (i : Nat) :
    countWhile p (l.drop i) =
      if h : i < l.length then (if p (l[i]'h) then 1 + countWhile p (l.drop (i + 1)) else 0) else 0 := by
  split
  · rename_i h
    rw [List.drop_eq_getElem_cons h]
    simp [countWhile]
  · rename_i h
    rw [List.drop_of_length_le (by omega)]
    simp [countWhile]

/-- The whitespace loop advances the cursor by the model's space count. -/
theorem loop1_spec (text : Array UInt8) (hs : text.size ≤ 65536) :
    ∀ (fuel : Nat) (pos : UInt32), pos.toNat ≤ text.size → text.size - pos.toNat < fuel →
      ∃ pos' : UInt32, rup_token.loop1 text pos fuel = some pos' ∧
        pos'.toNat = pos.toNat + countWhile space ((toBytes text).drop pos.toNat) := by
  intro fuel
  induction fuel with
  | zero => intro pos _ hf; omega
  | succ fuel ih =>
    intro pos hp hf
    simp only [rup_token.loop1, rup_space_eq, bind, Option.bind]
    rw [countWhile_drop]
    by_cases hin : pos.toNat < text.size
    · have hl : pos.toNat < (toBytes text).length := by rw [toBytes_length]; exact hin
      simp only [hl, dite_true]
      have hb : (text.getD pos.toNat 0).toNat = (toBytes text)[pos.toNat]'hl := by
        rw [getD_toBytes, getD_toBytes_of_lt text pos.toNat hin]
      rw [hb]
      have hdec : decide (pos < text.size.toUInt32) = true := (lt_size_iff text pos hs).mpr hin
      rw [hdec]
      by_cases hsp : space ((toBytes text)[pos.toNat]'hl) = true
      · simp only [hsp, Bool.true_and, if_true]
        have hnext : (pos + 1).toNat = pos.toNat + 1 := toNat_succ pos (by omega)
        obtain ⟨pos', hrun, hval⟩ := ih (pos + 1) (by omega) (by omega)
        refine ⟨pos', hrun, ?_⟩
        rw [hval, hnext]
        omega
      · have hsp' : space ((toBytes text)[pos.toNat]'hl) = false := by simpa using hsp
        simp [hsp']
    · have hl : ¬ pos.toNat < (toBytes text).length := by rw [toBytes_length]; exact hin
      have hdec : decide (pos < text.size.toUInt32) = false := by
        have := (lt_size_iff text pos hs)
        simpa using fun h => hin (this.mp h)
      simp [hl, hdec]

/-- The word loop advances the cursor by the model's word-byte count. -/
theorem loop2_spec (text : Array UInt8) (hs : text.size ≤ 65536) :
    ∀ (fuel : Nat) (pos : UInt32), pos.toNat ≤ text.size → text.size - pos.toNat < fuel →
      ∃ pos' : UInt32, rup_token.loop2 text pos fuel = some pos' ∧
        pos'.toNat = pos.toNat + countWhile wordByte ((toBytes text).drop pos.toNat) := by
  intro fuel
  induction fuel with
  | zero => intro pos _ hf; omega
  | succ fuel ih =>
    intro pos hp hf
    simp only [rup_token.loop2, rup_space_eq, bind, Option.bind]
    rw [countWhile_drop]
    by_cases hin : pos.toNat < text.size
    · have hl : pos.toNat < (toBytes text).length := by rw [toBytes_length]; exact hin
      simp only [hl, dite_true]
      have hb : (text.getD pos.toNat 0).toNat = (toBytes text)[pos.toNat]'hl := by
        rw [getD_toBytes, getD_toBytes_of_lt text pos.toNat hin]
      have hne : ((text.getD pos.toNat 0) != (10 : UInt8)) = (((toBytes text)[pos.toNat]'hl) != 10) := by
        simp only [bne, beq_ofNat (text.getD pos.toNat 0) 10 (by decide), hb]
      rw [hb, hne]
      have hdec : decide (pos < text.size.toUInt32) = true := (lt_size_iff text pos hs).mpr hin
      rw [hdec]
      by_cases hw : wordByte ((toBytes text)[pos.toNat]'hl) = true
      · have hw' := hw
        simp only [wordByte, Bool.and_eq_true, Bool.not_eq_true'] at hw'
        obtain ⟨hten, hspace⟩ := hw'
        simp only [hten, hspace, hw, Bool.true_and, if_true]
        have hnext : (pos + 1).toNat = pos.toNat + 1 := toNat_succ pos (by omega)
        obtain ⟨pos', hrun, hval⟩ := ih (pos + 1) (by omega) (by omega)
        refine ⟨pos', hrun, ?_⟩
        rw [hval, hnext]
        omega
      · by_cases h10 : (toBytes text)[pos.toNat]'hl = 10
        · simp [h10, wordByte, space]
        · have hsp : space ((toBytes text)[pos.toNat]'hl) = true := by
            apply Decidable.byContradiction
            intro hns
            have hsf : space ((toBytes text)[pos.toNat]'hl) = false := by simpa using hns
            exact hw (by simp [wordByte, h10, hsf])
          simp [hsp, wordByte]
    · have hl : ¬ pos.toNat < (toBytes text).length := by rw [toBytes_length]; exact hin
      have hdec : decide (pos < text.size.toUInt32) = false := by
        have := (lt_size_iff text pos hs)
        simpa using fun h => hin (this.mp h)
      simp [hl, hdec]

/-- UInt32 equality against a literal is equality of the value. -/
theorem beq_ofNat32 (a : UInt32) (n : Nat) (hn : n < UInt32.size) :
    (a == (OfNat.ofNat n : UInt32)) = (a.toNat == n) := by
  rcases Bool.eq_false_or_eq_true (a == (OfNat.ofNat n : UInt32)) with heq | heq
  · rw [heq]
    have : a = OfNat.ofNat n := by simpa using heq
    subst this
    simp [UInt32.toNat_ofNat_of_lt hn]
  · rw [heq]
    have hne : a ≠ OfNat.ofNat n := by simpa using heq
    symm
    apply beq_eq_false_iff_ne.mpr
    intro ha
    apply hne
    apply UInt32.toNat_inj.mp
    rw [ha, UInt32.toNat_ofNat_of_lt hn]

theorem toNat_ofNat32 (n : Nat) (hn : n < UInt32.size) : (OfNat.ofNat n : UInt32).toNat = n :=
  UInt32.toNat_ofNat_of_lt hn

theorem toNat_ofNat8 (n : Nat) (hn : n < UInt8.size) : (OfNat.ofNat n : UInt8).toNat = n :=
  UInt8.toNat_ofNat_of_lt hn

/-- The slice of the word the digit loop walks: one byte, then the rest. -/
theorem slice_cons (l : List Nat) (i j : Nat) (hi : i < l.length) (hij : i < j) :
    (l.drop i).take (j - i) = (l[i]'hi) :: (l.drop (i + 1)).take (j - (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  obtain ⟨k, hk⟩ : ∃ k, j - i = k + 1 := ⟨j - i - 1, by omega⟩
  rw [hk, List.take_succ_cons]
  congr 2
  omega

/-- The digit loop walks the model's digit walk over the word's remaining
bytes: the magnitude agrees and the sign survives exactly when the walk is
valid; a zero sign on entry leaves everything untouched. -/
theorem loop3_spec (text : Array UInt8) (hs : text.size ≤ 65536) (pos : UInt32)
    (hpos : pos.toNat ≤ text.size) :
    ∀ (fuel : Nat) (digit magnitude sign : UInt32), digit.toNat ≤ pos.toNat →
      magnitude.toNat ≤ Decimal.limit → pos.toNat - digit.toNat < fuel →
      ∃ m s d : UInt32, rup_token.loop3 text pos magnitude sign digit fuel = some (m, s, d) ∧
        (sign = 0 → m = magnitude ∧ s = 0) ∧
        (sign ≠ 0 →
          m.toNat = (walk magnitude.toNat (((toBytes text).drop digit.toNat).take (pos.toNat - digit.toNat))).magnitude ∧
          s = (if (walk magnitude.toNat (((toBytes text).drop digit.toNat).take (pos.toNat - digit.toNat))).valid then sign else 0)) := by
  intro fuel
  induction fuel with
  | zero => intro digit magnitude sign _ _ hf; omega
  | succ fuel ih =>
    intro digit magnitude sign hdp hmag hf
    by_cases hsign : sign = 0
    · subst hsign
      refine ⟨magnitude, 0, digit, ?_, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
      simp [rup_token.loop3]
    · have hsne : (sign != (0 : UInt32)) = true := by simpa using hsign
      by_cases hlt : digit.toNat < pos.toNat
      · have hdec : decide (digit < pos) = true := by
          rw [decide_eq_true_iff, UInt32.lt_iff_toNat_lt]; exact hlt
        have hl : digit.toNat < (toBytes text).length := by rw [toBytes_length]; omega
        have hb : (text.getD digit.toNat 0).toNat = (toBytes text)[digit.toNat]'hl := by
          rw [getD_toBytes, getD_toBytes_of_lt text digit.toNat (by omega)]
        have hslice := slice_cons (toBytes text) digit.toNat pos.toNat hl hlt
        have hnext : (digit + 1).toNat = digit.toNat + 1 := toNat_succ digit (by omega)
        obtain ⟨b, hbdef⟩ : ∃ b : Nat, (toBytes text)[digit.toNat]'hl = b := ⟨_, rfl⟩
        rw [hbdef] at hb hslice
        -- The model's step on this byte.
        have hwalk : walk magnitude.toNat (((toBytes text).drop digit.toNat).take (pos.toNat - digit.toNat)) =
            match advance magnitude.toNat b with
            | none => ⟨1, magnitude.toNat, false⟩
            | some next =>
              let r := walk next (((toBytes text).drop (digit.toNat + 1)).take (pos.toNat - (digit.toNat + 1)))
              ⟨1 + r.used, r.magnitude, r.valid⟩ := by
          rw [hslice]; rfl
        simp only [rup_token.loop3, hdec, hsne, Bool.true_and, if_true, bind, Option.bind]
        by_cases hdig : 48 ≤ b ∧ b ≤ 57
        · -- A digit: the threshold guard decides.
          have hlt48 : decide ((text.getD digit.toNat 0) < (48 : UInt8)) = false := by
            simp only [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, toNat_ofNat8 48 (by decide), hb]; omega
          have hgt57 : decide ((text.getD digit.toNat 0) > (57 : UInt8)) = false := by
            simp only [decide_eq_false_iff_not, gt_iff_lt, UInt8.lt_iff_toNat_lt, toNat_ofNat8 57 (by decide), hb]; omega
          have hvalue : ((text.getD digit.toNat 0).toUInt32 - (48 : UInt32)).toNat = b - 48 := by
            rw [UInt32.toNat_sub, UInt8.toNat_toUInt32, toNat_ofNat32 48 (by decide), hb]
            have hb256 : b < 256 := by
              rw [← hb]; exact UInt8.toNat_lt_size _
            rw [show 2 ^ 32 - 48 + b = (b - 48) + 2 ^ 32 by omega, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          have hadv : advance magnitude.toNat b = Decimal.step magnitude.toNat (b - 48) := by
            simp [advance, Decimal.decodeDigit, hdig]
          simp only [hlt48, hgt57, Bool.or_self]
          by_cases hguard : magnitude.toNat > 214748364 ∨ (magnitude.toNat = 214748364 ∧ b - 48 > 7)
          · have hg : (decide (magnitude > (214748364 : UInt32)) ||
                ((magnitude == (214748364 : UInt32)) && decide (((text.getD digit.toNat 0).toUInt32 - (48 : UInt32)) > (7 : UInt32)))) = true := by
              simp only [Bool.or_eq_true, decide_eq_true_iff, Bool.and_eq_true, gt_iff_lt,
                UInt32.lt_iff_toNat_lt, toNat_ofNat32 214748364 (by decide), toNat_ofNat32 7 (by decide),
                beq_ofNat32 magnitude 214748364 (by decide), beq_iff_eq, hvalue]
              omega
            have hstep : Decimal.step magnitude.toNat (b - 48) = none := by
              simp only [Decimal.step]
              have hd : b - 48 < 10 := by omega
              simp only [hd, if_true]
              have : (magnitude.toNat > 214748364 || decide (magnitude.toNat = 214748364 ∧ b - 48 > 7)) = true := by
                simpa [decide_eq_true_iff] using hguard
              simp
              omega
            simp only [hg, if_true]
            obtain ⟨m, s, d, hrun, hzero, _⟩ := ih (digit + 1) magnitude 0 (by omega) hmag (by omega)
            refine ⟨m, s, d, hrun, fun h => absurd h hsign, fun _ => ?_⟩
            obtain ⟨hm, hs0⟩ := hzero rfl
            rw [hwalk, hadv, hstep]
            simp [hm, hs0]
          · have hg : (decide (magnitude > (214748364 : UInt32)) ||
                ((magnitude == (214748364 : UInt32)) && decide (((text.getD digit.toNat 0).toUInt32 - (48 : UInt32)) > (7 : UInt32)))) = false := by
              simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff, gt_iff_lt,
                UInt32.lt_iff_toNat_lt, toNat_ofNat32 214748364 (by decide), toNat_ofNat32 7 (by decide),
                beq_ofNat32 magnitude 214748364 (by decide), beq_eq_false_iff_ne, hvalue]
              omega
            have hstep : Decimal.step magnitude.toNat (b - 48) = some (magnitude.toNat * 10 + (b - 48)) := by
              simp only [Decimal.step]
              have hd : b - 48 < 10 := by omega
              have : (magnitude.toNat > 214748364 || decide (magnitude.toNat = 214748364 ∧ b - 48 > 7)) = false := by
                simpa [decide_eq_false_iff_not] using hguard
              simp [hd]
              omega
            have hprod : (magnitude * (10 : UInt32) + ((text.getD digit.toNat 0).toUInt32 - (48 : UInt32))).toNat = magnitude.toNat * 10 + (b - 48) := by
              rw [UInt32.toNat_add, UInt32.toNat_mul, toNat_ofNat32 10 (by decide), hvalue]
              have hsmall : magnitude.toNat * 10 + (b - 48) < 2 ^ 32 := by
                unfold Decimal.limit at hmag; omega
              rw [Nat.mod_eq_of_lt (show magnitude.toNat * 10 < 2 ^ 32 by unfold Decimal.limit at hmag; omega),
                Nat.mod_eq_of_lt hsmall]
            have hbound : (magnitude * (10 : UInt32) + ((text.getD digit.toNat 0).toUInt32 - (48 : UInt32))).toNat ≤ Decimal.limit := by
              rw [hprod]; unfold Decimal.limit at *; omega
            simp only [hg]
            obtain ⟨m, s, d, hrun, _, hpos'⟩ := ih (digit + 1) (magnitude * 10 + ((text.getD digit.toNat 0).toUInt32 - 48)) sign (by omega) hbound (by omega)
            refine ⟨m, s, d, hrun, fun h => absurd h hsign, fun _ => ?_⟩
            obtain ⟨hm, hs'⟩ := hpos' hsign
            rw [hwalk, hadv, hstep]
            simp only [hnext] at hm hs'
            rw [hprod] at hm hs'
            exact ⟨hm, hs'⟩
        · -- Not a digit: the sign dies, the magnitude stays.
          have hbad : (decide ((text.getD digit.toNat 0) < (48 : UInt8)) || decide ((text.getD digit.toNat 0) > (57 : UInt8))) = true := by
            simp only [Bool.or_eq_true, decide_eq_true_iff, gt_iff_lt, UInt8.lt_iff_toNat_lt,
              toNat_ofNat8 48 (by decide), toNat_ofNat8 57 (by decide), hb]
            omega
          have hadv : advance magnitude.toNat b = none := by
            simp [advance, Decimal.decodeDigit, hdig]
          simp only [hbad, if_true]
          obtain ⟨m, s, d, hrun, hzero, _⟩ := ih (digit + 1) magnitude 0 (by omega) hmag (by omega)
          refine ⟨m, s, d, hrun, fun h => absurd h hsign, fun _ => ?_⟩
          obtain ⟨hm, hs0⟩ := hzero rfl
          rw [hwalk, hadv]
          simp [hm, hs0]
      · -- At the word's end: nothing left to walk.
        have heq : digit.toNat = pos.toNat := by omega
        have hdec : decide (digit < pos) = false := by
          simp only [decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt]; omega
        refine ⟨magnitude, sign, digit, ?_, fun h => absurd h hsign, fun _ => ?_⟩
        · simp [rup_token.loop3, hdec]
        · rw [heq, Nat.sub_self, List.take_zero]
          simp [walk]

theorem getD_of_lt (l : List Nat) (i : Nat) (h : i < l.length) : l.getD i 0 = l[i]'h := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
  rfl

/-- Where `countWhile` stops inside the list, the predicate fails. -/
theorem countWhile_stop (p : Nat → Bool) (l : List Nat) :
    ∀ (k i : Nat), countWhile p (l.drop i) = k → i + k < l.length → p (l.getD (i + k) 0) = false := by
  intro k
  induction k with
  | zero =>
    intro i hc h
    rw [countWhile_drop] at hc
    simp only [Nat.add_zero] at h ⊢
    simp only [h, dite_true] at hc
    rw [getD_of_lt l i h]
    split at hc
    · omega
    · rename_i hnp
      simpa using hnp
  | succ k ih =>
    intro i hc h
    rw [countWhile_drop] at hc
    have hi : i < l.length := by omega
    simp only [hi, dite_true] at hc
    split at hc
    · have := ih (i + 1) (by omega) (by omega)
      rw [show i + (k + 1) = i + 1 + k by omega]
      exact this
    · omega

/-- Reading the scanner state back after its five stores. -/
theorem state_reads (state : Array UInt32) (hstate : state.size = 5) (a b c d e : UInt32) :
    (((((state.setIfInBounds 0 a).setIfInBounds 1 b).setIfInBounds 2 c).setIfInBounds 3 d).setIfInBounds 4 e).size = 5 ∧
    (((((state.setIfInBounds 0 a).setIfInBounds 1 b).setIfInBounds 2 c).setIfInBounds 3 d).setIfInBounds 4 e).getD 0 0 = a ∧
    (((((state.setIfInBounds 0 a).setIfInBounds 1 b).setIfInBounds 2 c).setIfInBounds 3 d).setIfInBounds 4 e).getD 1 0 = b ∧
    (((((state.setIfInBounds 0 a).setIfInBounds 1 b).setIfInBounds 2 c).setIfInBounds 3 d).setIfInBounds 4 e).getD 2 0 = c ∧
    (((((state.setIfInBounds 0 a).setIfInBounds 1 b).setIfInBounds 2 c).setIfInBounds 3 d).setIfInBounds 4 e).getD 3 0 = d ∧
    (((((state.setIfInBounds 0 a).setIfInBounds 1 b).setIfInBounds 2 c).setIfInBounds 3 d).setIfInBounds 4 e).getD 4 0 = e := by
  simp [Array.getD_eq_getD_getElem?, Array.size_setIfInBounds, hstate]

theorem beq_nat_decide (a n : Nat) : (a == n) = decide (a = n) := by
  by_cases h : a = n <;> simp [h]

theorem beq_toNat32 (a b : UInt32) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [beq_eq_false_iff_ne.mpr hab, decide_eq_false (fun h => hab (UInt32.toNat_inj.mp h))]

theorem numeric_plus (rest : List Nat) :
    numeric (43 :: rest) =
      (if rest.isEmpty then (0, 0) else ((walk 0 rest).magnitude, if (walk 0 rest).valid then 1 else 0)) := rfl

theorem numeric_minus (rest : List Nat) :
    numeric (45 :: rest) =
      (if rest.isEmpty then (0, 0) else ((walk 0 rest).magnitude, if (walk 0 rest).valid then 2 else 0)) := rfl

theorem numeric_other (b : Nat) (rest : List Nat) (h43 : b ≠ 43) (h45 : b ≠ 45) :
    numeric (b :: rest) = ((walk 0 (b :: rest)).magnitude, if (walk 0 (b :: rest)).valid then 1 else 0) := by
  unfold numeric
  split
  rename_i heq
  split at heq
  · simp_all
  · simp_all
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨htag, hds⟩ := heq
    subst htag
    subst hds
    simp

/-- The scanner gate as a theorem: the extracted `rup_token` returns the
proved scanner's token — kind, cursor, range, magnitude, sign — on every
bounded text from every cursor inside it. -/
theorem rup_token_scan (text : Array UInt8) (state : Array UInt32) (fuel : Nat)
    (hs : text.size ≤ 65536) (hstate : state.size = 5)
    (hpos : (state.getD 0 0).toNat ≤ text.size) (hf : text.size < fuel) :
    ∃ (kind : UInt32) (state' : Array UInt32), rup_token text state fuel = some (kind, state') ∧
      state'.size = 5 ∧
      kind.toNat = (scan (toBytes text) (state.getD 0 0).toNat).kind ∧
      (state'.getD 0 0).toNat = (scan (toBytes text) (state.getD 0 0).toNat).next ∧
      (state'.getD 1 0).toNat = (scan (toBytes text) (state.getD 0 0).toNat).start ∧
      (state'.getD 2 0).toNat = (scan (toBytes text) (state.getD 0 0).toNat).stop ∧
      (state'.getD 3 0).toNat = (scan (toBytes text) (state.getD 0 0).toNat).magnitude ∧
      (state'.getD 4 0).toNat = (scan (toBytes text) (state.getD 0 0).toNat).sign := by
  -- The whitespace loop lands on the token start.
  obtain ⟨pos1, h1, hv1⟩ := loop1_spec text hs fuel (state.getD 0 0) hpos (by omega)
  have hlen : ((toBytes text).drop (state.getD 0 0).toNat).length = text.size - (state.getD 0 0).toNat := by
    rw [List.length_drop, toBytes_length]
  have hc1 := countWhile_bounds space ((toBytes text).drop (state.getD 0 0).toNat)
  have hpos1 : pos1.toNat ≤ text.size := by omega
  have hscan : scan (toBytes text) (state.getD 0 0).toNat = tokenAt pos1.toNat ((toBytes text).drop pos1.toNat) := by
    unfold scan scanTail
    rw [List.drop_drop, ← hv1]
  rw [hscan]
  simp only [rup_token, h1, bind, Option.bind]
  by_cases hin : pos1.toNat < text.size
  · have hl : pos1.toNat < (toBytes text).length := by rw [toBytes_length]; exact hin
    have hdec : decide (pos1 < text.size.toUInt32) = true := (lt_size_iff text pos1 hs).mpr hin
    have hb : (text.getD pos1.toNat 0).toNat = (toBytes text)[pos1.toNat]'hl := by
      rw [getD_toBytes, getD_toBytes_of_lt text pos1.toNat hin]
    have hdrop : (toBytes text).drop pos1.toNat = ((toBytes text)[pos1.toNat]'hl) :: (toBytes text).drop (pos1.toNat + 1) :=
      List.drop_eq_getElem_cons hl
    rw [hdrop]
    obtain ⟨b, hbdef⟩ : ∃ b : Nat, (toBytes text)[pos1.toNat]'hl = b := ⟨_, rfl⟩
    rw [hbdef] at hb
    rw [hbdef]
    simp only [hdec, if_true]
    by_cases h10 : b = 10
    · -- A newline token.
      have hbeq : ((text.getD pos1.toNat 0) == (10 : UInt8)) = true := by
        rw [beq_ofNat _ 10 (by decide), hb, h10]; simp
      simp only [hbeq, if_true, pure]
      have hnext : (pos1 + 1).toNat = pos1.toNat + 1 := toNat_succ pos1 (by omega)
      obtain ⟨hsz, r0, r1, r2, r3, r4⟩ := state_reads state hstate (pos1 + 1) pos1 (pos1 + 1) 0 1
      refine ⟨1, _, rfl, hsz, ?_⟩
      rw [r0, r1, r2, r3, r4]
      simp [tokenAt, h10, hnext, toNat_ofNat32 1 (by decide)]
    · -- A word token.
      have hbeq : ((text.getD pos1.toNat 0) == (10 : UInt8)) = false := by
        rw [beq_ofNat _ 10 (by decide), hb]; simpa using h10
      simp only [hbeq]
      -- The word loop lands on the word end.
      have hspace : space b = false := by
        have := countWhile_stop space (toBytes text) (countWhile space ((toBytes text).drop (state.getD 0 0).toNat))
          (state.getD 0 0).toNat rfl (by rw [toBytes_length]; omega)
        rw [← hv1, getD_of_lt _ _ hl, hbdef] at this
        exact this
      have hword : wordByte b = true := by simp [wordByte, h10, hspace]
      obtain ⟨pos2, h2, hv2⟩ := loop2_spec text hs fuel pos1 hpos1 (by omega)
      have hcount : countWhile wordByte ((toBytes text).drop pos1.toNat) =
          1 + countWhile wordByte ((toBytes text).drop (pos1.toNat + 1)) := by
        rw [countWhile_drop]; simp [hl, hbdef, hword]
      have hcb := countWhile_bounds wordByte ((toBytes text).drop (pos1.toNat + 1))
      have hlen2 : ((toBytes text).drop (pos1.toNat + 1)).length = text.size - (pos1.toNat + 1) := by
        rw [List.length_drop, toBytes_length]
      have hpos2 : pos2.toNat ≤ text.size := by omega
      have hpos12 : pos1.toNat < pos2.toNat := by omega
      simp only [h2]
      -- The token the model produces.
      have hsize : 1 + countWhile wordByte ((toBytes text).drop (pos1.toNat + 1)) = pos2.toNat - pos1.toNat := by omega
      have htake : (b :: (toBytes text).drop (pos1.toNat + 1)).take (1 + countWhile wordByte ((toBytes text).drop (pos1.toNat + 1))) =
          b :: ((toBytes text).drop (pos1.toNat + 1)).take (countWhile wordByte ((toBytes text).drop (pos1.toNat + 1))) := by
        rw [Nat.add_comm, List.take_succ_cons]
      have hrest : ((toBytes text).drop (pos1.toNat + 1)).take (countWhile wordByte ((toBytes text).drop (pos1.toNat + 1))) =
          ((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1)) := by
        congr 1; omega
      have hwhole : ((toBytes text).drop pos1.toNat).take (pos2.toNat - pos1.toNat) =
          b :: ((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1)) := by
        rw [hdrop, hbdef]
        obtain ⟨k, hk⟩ : ∃ k, pos2.toNat - pos1.toNat = k + 1 := ⟨pos2.toNat - pos1.toNat - 1, by omega⟩
        rw [hk, List.take_succ_cons]
        congr 2; omega
      have hnext1 : (pos1 + 1).toNat = pos1.toNat + 1 := toNat_succ pos1 (by omega)
      -- Whether the word is a bare sign.
      have hwordEmpty : (((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1))).isEmpty =
          decide (pos2.toNat = pos1.toNat + 1) := by
        by_cases he : pos2.toNat = pos1.toNat + 1
        · simp [he]
        · have hne : ¬ ((((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1))).isEmpty = true) := by
            rw [List.isEmpty_iff_length_eq_zero, List.length_take, hlen2]; omega
          rw [decide_eq_false he]
          exact Bool.eq_false_iff.mpr hne
      -- Result assembly, one case per leading byte.
      simp only [tokenAt, h10, if_false, htake, hrest, Bool.false_eq_true]
      have hbeq43 : ((text.getD pos1.toNat 0) == (43 : UInt8)) = decide (b = 43) := by
        rw [beq_ofNat _ 43 (by decide), hb, beq_nat_decide]
      have hbeq45 : ((text.getD pos1.toNat 0) == (45 : UInt8)) = decide (b = 45) := by
        rw [beq_ofNat _ 45 (by decide), hb, beq_nat_decide]
      have hbare : ((pos1 + 1) == pos2) = decide (pos1.toNat + 1 = pos2.toNat) := by
        rw [beq_toNat32, hnext1]
      have hnotbare : (pos1 == pos2) = false := by
        rw [beq_toNat32, decide_eq_false (by omega)]
      have hsign2 : (2 : UInt32) ≠ 0 := by decide
      have hsign1 : (1 : UInt32) ≠ 0 := by decide
      -- The digit loop's slice for a signed word.
      have hslice1 : ((toBytes text).drop (pos1 + 1).toNat).take (pos2.toNat - (pos1 + 1).toNat) =
          ((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1)) := by
        rw [hnext1]
      by_cases h43 : b = 43
      · subst h43
        rw [numeric_plus]
        have hT : decide True = true := by decide
        have hF : decide (43 = 45) = false := by decide
        simp only [hbeq43, hbeq45, hT, hF, Bool.true_or, hbare, hwordEmpty, pure, if_true, if_false,
          Bool.false_eq_true]
        by_cases hbe : pos1.toNat + 1 = pos2.toNat
        · have hbe' : pos2.toNat = pos1.toNat + 1 := hbe.symm
          simp only [decide_eq_true hbe, decide_eq_true hbe', if_true]
          obtain ⟨m, s', d, hrun, hzero, _⟩ := loop3_spec text hs pos2 hpos2 fuel (pos1 + 1) 0 0 (by omega) (by simp [Decimal.limit]) (by omega)
          obtain ⟨hm, hs0⟩ := hzero rfl
          rw [hrun]
          simp only [hm, hs0]
          obtain ⟨hsz, r0, r1, r2, r3, r4⟩ := state_reads state hstate pos2 pos1 pos2 0 0
          refine ⟨2, _, rfl, hsz, ?_⟩
          rw [r0, r1, r2, r3, r4]
          simp [toNat_ofNat32 2 (by decide)]
          omega
        · have hbe' : ¬ pos2.toNat = pos1.toNat + 1 := fun h => hbe h.symm
          simp only [decide_eq_false hbe, decide_eq_false hbe', if_false, Bool.false_eq_true]
          obtain ⟨m, s', d, hrun, _, hval⟩ := loop3_spec text hs pos2 hpos2 fuel (pos1 + 1) 0 1 (by omega) (by simp [Decimal.limit]) (by omega)
          obtain ⟨hm, hs'⟩ := hval hsign1
          rw [hslice1] at hm hs'
          rw [hrun]
          obtain ⟨hsz, r0, r1, r2, r3, r4⟩ := state_reads state hstate pos2 pos1 pos2 m s'
          refine ⟨2, _, rfl, hsz, ?_⟩
          rw [r0, r1, r2, r3, r4]
          refine ⟨toNat_ofNat32 2 (by decide), by omega, rfl, by omega, ?_, ?_⟩
          · rw [UInt32.toNat_zero] at hm; simpa using hm
          · rw [hs']
            by_cases hv : (walk 0 (((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1)))).valid = true
            · simp [hv, toNat_ofNat32 1 (by decide)]
            · simp [hv]
      · by_cases h45 : b = 45
        · subst h45
          rw [numeric_minus]
          have hT : decide True = true := by decide
          have hF : decide (45 = 43) = false := by decide
          have hE : decide (45 = 45) = true := by decide
          simp only [hbeq43, hbeq45, hT, hF, Bool.false_or, hbare, hwordEmpty, pure, if_true]
          by_cases hbe : pos1.toNat + 1 = pos2.toNat
          · have hbe' : pos2.toNat = pos1.toNat + 1 := hbe.symm
            simp only [decide_eq_true hbe, decide_eq_true hbe', if_true]
            obtain ⟨m, s', d, hrun, hzero, _⟩ := loop3_spec text hs pos2 hpos2 fuel (pos1 + 1) 0 0 (by omega) (by simp [Decimal.limit]) (by omega)
            obtain ⟨hm, hs0⟩ := hzero rfl
            rw [hrun]
            simp only [hm, hs0]
            obtain ⟨hsz, r0, r1, r2, r3, r4⟩ := state_reads state hstate pos2 pos1 pos2 0 0
            refine ⟨2, _, rfl, hsz, ?_⟩
            rw [r0, r1, r2, r3, r4]
            simp [toNat_ofNat32 2 (by decide)]
            omega
          · have hbe' : ¬ pos2.toNat = pos1.toNat + 1 := fun h => hbe h.symm
            simp only [decide_eq_false hbe, decide_eq_false hbe', if_false, Bool.false_eq_true]
            obtain ⟨m, s', d, hrun, _, hval⟩ := loop3_spec text hs pos2 hpos2 fuel (pos1 + 1) 0 2 (by omega) (by simp [Decimal.limit]) (by omega)
            obtain ⟨hm, hs'⟩ := hval hsign2
            rw [hslice1] at hm hs'
            rw [hrun]
            obtain ⟨hsz, r0, r1, r2, r3, r4⟩ := state_reads state hstate pos2 pos1 pos2 m s'
            refine ⟨2, _, rfl, hsz, ?_⟩
            rw [r0, r1, r2, r3, r4]
            refine ⟨toNat_ofNat32 2 (by decide), by omega, rfl, by omega, ?_, ?_⟩
            · rw [UInt32.toNat_zero] at hm; simpa using hm
            · rw [hs']
              by_cases hv : (walk 0 (((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1)))).valid = true
              · simp [hv, toNat_ofNat32 2 (by decide)]
              · simp [hv]
        · rw [numeric_other b _ h43 h45]
          have hd1 : (decide (b = 43) || decide (b = 45)) = false := by
            rw [decide_eq_false h43, decide_eq_false h45]; rfl
          simp only [hbeq43, hbeq45, hd1, hnotbare, pure, if_false, Bool.false_eq_true]
          obtain ⟨m, s', d, hrun, _, hval⟩ := loop3_spec text hs pos2 hpos2 fuel pos1 0 1 (by omega) (by simp [Decimal.limit]) (by omega)
          obtain ⟨hm, hs'⟩ := hval hsign1
          rw [hwhole] at hm hs'
          rw [hrun]
          obtain ⟨hsz, r0, r1, r2, r3, r4⟩ := state_reads state hstate pos2 pos1 pos2 m s'
          refine ⟨2, _, rfl, hsz, ?_⟩
          rw [r0, r1, r2, r3, r4]
          refine ⟨toNat_ofNat32 2 (by decide), by omega, rfl, by omega, ?_, ?_⟩
          · rw [UInt32.toNat_zero] at hm; simpa using hm
          · rw [hs']
            by_cases hv : (walk 0 (b :: ((toBytes text).drop (pos1.toNat + 1)).take (pos2.toNat - (pos1.toNat + 1)))).valid = true
            · simp [hv, toNat_ofNat32 1 (by decide)]
            · simp [hv]
  · -- End of input.
    have hdec : decide (pos1 < text.size.toUInt32) = false := by
      have := lt_size_iff text pos1 hs
      simpa using fun h => hin (this.mp h)
    have hnil : (toBytes text).drop pos1.toNat = [] := List.drop_of_length_le (by rw [toBytes_length]; omega)
    rw [hnil]
    simp only [hdec, pure]
    obtain ⟨hsz, r0, r1, r2, r3, r4⟩ := state_reads state hstate pos1 pos1 pos1 0 1
    refine ⟨0, _, rfl, hsz, ?_⟩
    rw [r0, r1, r2, r3, r4]
    simp [tokenAt, toNat_ofNat32 1 (by decide)]

#print axioms loop1_spec
#print axioms loop2_spec
#print axioms loop3_spec
#print axioms rup_token_scan

end OakVerification.Extraction
