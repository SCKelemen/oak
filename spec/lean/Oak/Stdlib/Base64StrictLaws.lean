import Std.Tactic.BVDecide
import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.EncodingLaws
import Oak.Stdlib.Base64Laws

/-!
# Oak.Stdlib.Base64StrictLaws — base64 strictness on the extracted `encoding` package

`base64_decode` accepts a text iff it is an encoding: `base64_decode_strict`
builds the witness — the bytes the decoder wrote are a source whose
encoding (padded iff the text carries padding) is the text, in the sense
of `Encoded` from `Base64Laws`; `base64_decode_encoded` there gives the
converse; `base64_decode_ok_iff` states the equivalence.

The rejection half follows the decoder on arbitrary input: the padding
strip counts trailing `=` (at most two), the validation scan's accumulated
`or` carries bit 6 once any byte outside the alphabet is seen (its table
value is exactly 64), the length check refuses a body of one symbol past a
group, and the canonical check reads the last symbol's unused bits. What
survives is exactly what the encoder writes: the decoded bytes reassemble
into the decoder's words, whose six-bit fields are the symbol values, and
the symbol table inverts the value table on the alphabet.
-/

namespace Oak.Stdlib.Encoding

set_option maxRecDepth 65536

/-! ## Tables -/

theorem b64_values_shape_std : ∀ b : Fin 256,
    (BASE64_STD_VALUES.getD b.val 0).toNat < 64 ∨ (BASE64_STD_VALUES.getD b.val 0).toNat = 64 := by decide +kernel
theorem b64_values_shape_url : ∀ b : Fin 256,
    (BASE64_URL_VALUES.getD b.val 0).toNat < 64 ∨ (BASE64_URL_VALUES.getD b.val 0).toNat = 64 := by decide +kernel
theorem b64_symbol_value_std : ∀ b : Fin 256, (BASE64_STD_VALUES.getD b.val 0).toNat < 64 →
    BASE64_STD_SYMBOLS.getD (BASE64_STD_VALUES.getD b.val 0).toNat 0 = b.val.toUInt8 := by decide +kernel
theorem b64_symbol_value_url : ∀ b : Fin 256, (BASE64_URL_VALUES.getD b.val 0).toNat < 64 →
    BASE64_URL_SYMBOLS.getD (BASE64_URL_VALUES.getD b.val 0).toNat 0 = b.val.toUInt8 := by decide +kernel

/-- A byte's value is a symbol value or exactly 64 (pad or foreign byte). -/
theorem symValue_shape (url : Bool) (b : UInt8) : (symValue url b).toNat < 64 ∨ (symValue url b).toNat = 64 := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  cases url
  · have := b64_values_shape_std ⟨b.toNat, hb⟩
    simpa [symValue, b64values, UInt8.toNat_toUInt32] using this
  · have := b64_values_shape_url ⟨b.toNat, hb⟩
    simpa [symValue, b64values, UInt8.toNat_toUInt32] using this

/-- The symbol table inverts the value table on the alphabet. -/
theorem symbol_symValue (url : Bool) (b : UInt8) (h : (symValue url b).toNat < 64) :
    (b64symbols url).getD (symValue url b).toNat 0 = b := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  cases url
  · have := b64_symbol_value_std ⟨b.toNat, hb⟩
    simp only [symValue, b64values, Bool.false_eq_true, ↓reduceIte, UInt8.toNat_toUInt32] at h ⊢
    unfold b64symbols; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [this h]; exact toUInt8_toNat b
  · have := b64_symbol_value_url ⟨b.toNat, hb⟩
    simp only [symValue, b64values, ↓reduceIte, UInt8.toNat_toUInt32] at h ⊢
    unfold b64symbols; simp only [↓reduceIte]
    rw [this h]; exact toUInt8_toNat b

theorem base64_value_eq (b : UInt8) (url : Bool) (fuel : Nat) : base64_value b url fuel = some (symValue url b) := by
  unfold base64_value symValue b64values; cases url <;> rfl

theorem toUInt32_succ' (t : Nat) (h : t + 1 < 2 ^ 32) : t.toUInt32 + 1 = (t + 1).toUInt32 := by
  apply UInt32.toNat.inj
  rw [uadd _ 1 1 (by decide) (by rw [toUInt32_toNat_of_lt _ (by omega)]; exact h), toUInt32_toNat_of_lt _ (by omega),
    toUInt32_toNat_of_lt _ h]

/-! ## The padding strip on any text -/

/-- The last `p` bytes are `=`. -/
def TrailingPads (src : Array UInt8) (p : Nat) : Prop := p ≤ src.size ∧ ∀ j, j < p → src.getD (src.size - 1 - j) 0 = 61

theorem unpad_loop_gen (src : Array UInt8) (hsize : src.size < 2 ^ 32) (fuel : Nat) :
    ∀ p : Nat, p ≤ 2 → TrailingPads src p → 2 - p < fuel →
      ∃ pads : Nat, base64_unpadded_length.loop1 src p.toUInt32 fuel = some pads.toUInt32 ∧ pads ≤ 2 ∧ TrailingPads src pads := by
  have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ hsize
  induction fuel with
  | zero => intro p _ _ hf; omega
  | succ fuel ih =>
    intro p hp htp hf
    have hp32 : (p.toUInt32).toNat = p := toUInt32_toNat_of_lt _ (by omega)
    have hidx : p < src.size → ((src.size.toUInt32 - 1) - p.toUInt32).toNat = src.size - 1 - p := by
      intro h1
      rw [UInt32.toNat_sub_of_le, UInt32.toNat_sub_of_le, hsz, hp32, show (1 : UInt32).toNat = 1 by decide]
      · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; omega
      · rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, hsz, hp32, show (1 : UInt32).toNat = 1 by decide]
        · omega
        · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; omega
    unfold base64_unpadded_length.loop1
    by_cases hc : p < src.size ∧ p < 2 ∧ src.getD (src.size - 1 - p) 0 = 61
    · have hc1 : decide (p.toUInt32 < src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz, hp32]; exact hc.1
      have hc2 : decide (p.toUInt32 < (2 : UInt32)) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hp32, show (2 : UInt32).toNat = 2 by decide]; exact hc.2.1
      have hc3 : (src.getD ((src.size.toUInt32 - 1) - p.toUInt32).toNat 0 == 61) = true := by
        rw [beq_iff_eq, hidx hc.1]; exact hc.2.2
      simp only [hc1, hc2, hc3, Bool.and_self, ↓reduceIte]
      rw [toUInt32_succ' p (by omega)]
      apply ih (p + 1) (by omega) ?_ (by omega)
      refine ⟨by omega, ?_⟩
      intro j hj
      by_cases hjp : j = p
      · subst hjp; exact hc.2.2
      · exact htp.2 j (by omega)
    · have hstop : ((decide (p.toUInt32 < src.size.toUInt32) && decide (p.toUInt32 < (2 : UInt32))) &&
          (src.getD ((src.size.toUInt32 - 1) - p.toUInt32).toNat 0 == 61)) = false := by
        by_cases h1 : p < src.size
        · by_cases h2 : p < 2
          · have h3 : src.getD (src.size - 1 - p) 0 ≠ 61 := fun h => hc ⟨h1, h2, h⟩
            have : (src.getD ((src.size.toUInt32 - 1) - p.toUInt32).toNat 0 == 61) = false := by
              rw [beq_eq_false_iff_ne, hidx h1]; exact h3
            exact Bool.and_eq_false_iff.mpr (Or.inr this)
          · have : decide (p.toUInt32 < (2 : UInt32)) = false := by
              apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hp32, show (2 : UInt32).toNat = 2 by decide]; exact h2
            exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inr this)))
        · have : decide (p.toUInt32 < src.size.toUInt32) = false := by
            apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz, hp32]; exact h1
          exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inl this)))
      rw [if_neg (by simpa using hstop)]
      exact ⟨p, rfl, hp, htp⟩

/-- The padding strip on any text: `InvalidPadding`, or a body whose padding is consistent. -/
theorem unpadded_length_gen (src : Array UInt8) (hsize : src.size < 2 ^ 32) (fuel : Nat) (hf : 2 < fuel) :
    (base64_unpadded_length src fuel = some (.Err .InvalidPadding)) ∨
    ∃ pads : Nat, pads ≤ 2 ∧ TrailingPads src pads ∧ (pads = 0 ∨ (src.size % 4 = 0 ∧ 2 ≤ (src.size - pads) % 4)) ∧
      base64_unpadded_length src fuel = some (.Ok (src.size - pads).toUInt32) := by
  have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ hsize
  obtain ⟨pads, hloop, hp2, htp⟩ :=
    unpad_loop_gen src hsize fuel 0 (by omega) ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ (by omega)
  have hp32 : (pads.toUInt32).toNat = pads := toUInt32_toNat_of_lt _ (by omega)
  have hbody : (src.size.toUInt32 - pads.toUInt32).toNat = src.size - pads := by
    rw [UInt32.toNat_sub_of_le, hsz, hp32]; rw [UInt32.le_iff_toNat_le, hsz, hp32]; exact htp.1
  have hbody' : src.size.toUInt32 - pads.toUInt32 = (src.size - pads).toUInt32 :=
    UInt32.toNat.inj (by rw [hbody, toUInt32_toNat_of_lt _ (by omega)])
  have hrest : ((src.size - pads).toUInt32 % 4).toNat = (src.size - pads) % 4 := by
    rw [UInt32.toNat_mod, toUInt32_toNat_of_lt _ (by omega), show (4 : UInt32).toNat = 4 by decide]
  have hmod4 : (src.size.toUInt32 % 4).toNat = src.size % 4 := by
    rw [UInt32.toNat_mod, hsz, show (4 : UInt32).toNat = 4 by decide]
  have hloop0 : base64_unpadded_length.loop1 src 0 fuel = some pads.toUInt32 := hloop
  unfold base64_unpadded_length
  simp only [Option.pure_def, Option.bind_eq_bind, hloop0, Option.bind_some]
  rw [hbody']
  by_cases hbad : pads = 0 ∨ (src.size % 4 = 0 ∧ 2 ≤ (src.size - pads) % 4)
  · right
    refine ⟨pads, hp2, htp, hbad, ?_⟩
    rcases hbad with h0 | ⟨h4, hr⟩
    · have hp : decide (pads.toUInt32 > (0 : UInt32)) = false := by
        apply decide_eq_false; rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hp32, h0]; simp
      simp only [hp, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · have h1 : (src.size.toUInt32 % 4 != 0) = false := by
        rw [bne_eq_false_iff_eq]; apply UInt32.toNat.inj; rw [hmod4, h4]; rfl
      have h2 : ((src.size - pads).toUInt32 % 4 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
      have h3 : ((src.size - pads).toUInt32 % 4 == 1) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
      simp only [h1, h2, h3, Bool.or_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · left
    have hpos : 0 < pads := by omega
    have hp : decide (pads.toUInt32 > (0 : UInt32)) = true := by
      apply decide_eq_true; rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hp32]; exact hpos
    simp only [hp, Bool.true_and]
    by_cases h4 : src.size % 4 = 0
    · have hr : ¬ 2 ≤ (src.size - pads) % 4 := fun h => hbad (Or.inr ⟨h4, h⟩)
      rcases (show (src.size - pads) % 4 = 0 ∨ (src.size - pads) % 4 = 1 by omega) with h | h
      · have hb : ((src.size - pads).toUInt32 % 4 == 0) = true := by
          rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h]; rfl
        simp only [hb, Bool.or_true, Bool.true_or, ↓reduceIte]
      · have hb : ((src.size - pads).toUInt32 % 4 == 1) = true := by
          rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h]; rfl
        simp only [hb, Bool.or_true, ↓reduceIte]
    · have hb : (src.size.toUInt32 % 4 != 0) = true := by
        rw [bne_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hmod4] at h'; simp at h'; exact h4 h'
      simp only [hb, Bool.true_or, ↓reduceIte]

/-! ## The validation scan on any text -/

/-- Bit 6 of the scan accumulator: set once a byte outside the alphabet has been seen. -/
def Bit6 (acc : UInt32) : Prop := acc.toNat.testBit 6 = true

theorem bit6_or_left {a : UInt32} (b : UInt32) (h : Bit6 a) : Bit6 (a ||| b) := by
  unfold Bit6 at h ⊢
  rw [UInt32.toNat_or, Nat.testBit_or, h]; rfl

theorem bit6_or_right (a : UInt32) {b : UInt32} (h : Bit6 b) : Bit6 (a ||| b) := by
  unfold Bit6 at h ⊢
  rw [UInt32.toNat_or, Nat.testBit_or, h]; simp

theorem bit6_of_64 {v : UInt32} (h : v.toNat = 64) : Bit6 v := by
  unfold Bit6; rw [h]; decide

theorem not_lt_of_bit6 {acc : UInt32} (h : Bit6 acc) : ¬ (acc.toNat < 64) := by
  intro hlt
  have := Nat.testBit_lt_two_pow (x := acc.toNat) (i := 6) hlt
  rw [h] at this
  cases this

theorem b64_scan_loop1_bit (src : Array UInt8) (url : Bool) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32) (fuel : Nat) :
    ∀ (acc i acc' i' : UInt32), i.toNat ≤ body.toNat →
      base64_scan.loop1 src body (b64values url) acc i fuel = some (acc', i') →
      (Bit6 acc → Bit6 acc') ∧ i.toNat ≤ i'.toNat ∧ i'.toNat ≤ body.toNat ∧
      (∀ k, i.toNat ≤ k → k < i'.toNat → (symValue url (src.getD k 0)).toNat = 64 → Bit6 acc') := by
  induction fuel with
  | zero => intro acc i acc' i' _ h; cases h
  | succ fuel ih =>
    intro acc i acc' i' hi h
    unfold base64_scan.loop1 at h
    have hi4 : (i + 4).toNat = i.toNat + 4 := uadd i 4 4 (by decide) (by omega)
    by_cases hle : i.toNat + 4 ≤ body.toNat
    · have hc : decide (i + 4 ≤ body) = true := by
        apply decide_eq_true; rw [UInt32.le_iff_toNat_le, hi4]; exact hle
      simp only [hc, ↓reduceIte] at h
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
      have hi3 : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
      obtain ⟨hb, hle', hbound, hk⟩ := ih _ (i + 4) acc' i' (by rw [hi4]; exact hle) h
      refine ⟨fun h0 => hb (bit6_or_left _ (bit6_or_left _ (bit6_or_left _ (bit6_or_left _ h0)))), by omega, hbound, ?_⟩
      intro k hk0 hk1 hv
      by_cases hk4 : i.toNat + 4 ≤ k
      · exact hk k (by omega) hk1 hv
      · apply hb
        rcases (show k = i.toNat ∨ k = (i + 1).toNat ∨ k = (i + 2).toNat ∨ k = (i + 3).toNat by
            rw [hi1, hi2, hi3]; omega) with rfl | rfl | rfl | rfl
        · exact bit6_or_left _ (bit6_or_left _ (bit6_or_left _ (bit6_or_right _ (bit6_of_64 hv))))
        · exact bit6_or_left _ (bit6_or_left _ (bit6_or_right _ (bit6_of_64 hv)))
        · exact bit6_or_left _ (bit6_or_right _ (bit6_of_64 hv))
        · exact bit6_or_right _ (bit6_of_64 hv)
    · have hc : decide (i + 4 ≤ body) = false := by
        apply decide_eq_false; rw [UInt32.le_iff_toNat_le, hi4]; exact hle
      simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨id, Nat.le_refl _, hi, fun k h1 h2 _ => absurd h2 (Nat.not_lt.mpr h1)⟩

theorem b64_scan_loop2_bit (src : Array UInt8) (url : Bool) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32) (fuel : Nat) :
    ∀ (acc i acc' i' : UInt32), i.toNat ≤ body.toNat →
      base64_scan.loop2 src body (b64values url) acc i fuel = some (acc', i') →
      (Bit6 acc → Bit6 acc') ∧ body.toNat ≤ i'.toNat ∧
      (∀ k, i.toNat ≤ k → k < body.toNat → (symValue url (src.getD k 0)).toNat = 64 → Bit6 acc') := by
  induction fuel with
  | zero => intro acc i acc' i' _ h; cases h
  | succ fuel ih =>
    intro acc i acc' i' hi h
    unfold base64_scan.loop2 at h
    by_cases hlt : i.toNat < body.toNat
    · have hc : decide (i < body) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, ↓reduceIte] at h
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      obtain ⟨hb, hbound, hk⟩ := ih _ (i + 1) acc' i' (by rw [hi1]; omega) h
      refine ⟨fun h0 => hb (bit6_or_left _ h0), hbound, ?_⟩
      intro k hk0 hk1 hv
      by_cases hki : k = i.toNat
      · subst hki
        exact hb (bit6_or_right _ (bit6_of_64 hv))
      · exact hk k (by rw [hi1]; omega) hk1 hv
    · have hc : decide (i < body) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨id, by omega, fun k h1 h2 _ => absurd h2 (by omega)⟩

/-- A scan that sees a byte outside the alphabet reports it in bit 6. -/
theorem b64_scan_bit (src : Array UInt8) (url : Bool) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32) (fuel : Nat) (acc : UInt32)
    (h : base64_scan src body url fuel = some acc) (k : Nat) (hk : k < body.toNat)
    (hv : (symValue url (src.getD k 0)).toNat = 64) : Bit6 acc := by
  unfold base64_scan at h
  have hvalues : (if url then BASE64_URL_VALUES else BASE64_STD_VALUES) = b64values url := rfl
  rw [hvalues] at h
  simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, bind, Prod.exists] at h
  obtain ⟨a1, i1, h1, a2, i2, h2, rfl⟩ := h
  obtain ⟨hb1, -, hbound1, hk1⟩ := b64_scan_loop1_bit src url body hsize fuel 0 0 a1 i1 (by simp) h1
  obtain ⟨hb2, -, hk2⟩ := b64_scan_loop2_bit src url body hsize fuel a1 i1 a2 i2 hbound1 h2
  by_cases hki : k < i1.toNat
  · exact hb2 (hk1 k (by simp) hki hv)
  · exact hk2 k (by omega) hk hv

theorem b64_scan_loop1_some (src : Array UInt8) (values : Array UInt8) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32) (fuel : Nat) :
    ∀ (acc i : UInt32), i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      ∃ acc' i', base64_scan.loop1 src body values acc i fuel = some (acc', i') ∧ i'.toNat ≤ body.toNat := by
  induction fuel with
  | zero => intro acc i _ hf; omega
  | succ fuel ih =>
    intro acc i hi hf
    unfold base64_scan.loop1
    have hi4 : (i + 4).toNat = i.toNat + 4 := uadd i 4 4 (by decide) (by omega)
    by_cases hle : i.toNat + 4 ≤ body.toNat
    · have hc : decide (i + 4 ≤ body) = true := by
        apply decide_eq_true; rw [UInt32.le_iff_toNat_le, hi4]; exact hle
      simp only [hc, ↓reduceIte]
      exact ih _ (i + 4) (by rw [hi4]; exact hle) (by omega)
    · have hc : decide (i + 4 ≤ body) = false := by
        apply decide_eq_false; rw [UInt32.le_iff_toNat_le, hi4]; exact hle
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨acc, i, rfl, hi⟩

theorem b64_scan_loop2_some (src : Array UInt8) (values : Array UInt8) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32) (fuel : Nat) :
    ∀ (acc i : UInt32), i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      ∃ acc' i', base64_scan.loop2 src body values acc i fuel = some (acc', i') := by
  induction fuel with
  | zero => intro acc i _ hf; omega
  | succ fuel ih =>
    intro acc i hi hf
    unfold base64_scan.loop2
    by_cases hlt : i.toNat < body.toNat
    · have hc : decide (i < body) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, ↓reduceIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      exact ih _ (i + 1) (by rw [hi1]; omega) (by omega)
    · have hc : decide (i < body) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨acc, i, rfl⟩

theorem b64_scan_some (src : Array UInt8) (url : Bool) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32) (fuel : Nat)
    (hf : body.toNat < fuel) : ∃ acc, base64_scan src body url fuel = some acc := by
  obtain ⟨a1, i1, h1, hi1⟩ := b64_scan_loop1_some src (b64values url) body hsize fuel 0 0 (by simp) (by simp; omega)
  obtain ⟨a2, i2, h2⟩ := b64_scan_loop2_some src (b64values url) body hsize fuel a1 i1 hi1 (by omega)
  refine ⟨a2, ?_⟩
  unfold base64_scan
  have hvalues : (if url then BASE64_URL_VALUES else BASE64_STD_VALUES) = b64values url := rfl
  rw [hvalues]
  simp [h1, h2]

/-- A scan below 64 means every symbol of the body is in the alphabet. -/
theorem all_symbols_of_scan (src : Array UInt8) (url : Bool) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32) (fuel : Nat)
    (acc : UInt32) (h : base64_scan src body url fuel = some acc) (hacc : acc.toNat < 64) :
    AllSymbols src (b64values url) body.toNat := by
  intro k hk
  rcases symValue_shape url (src.getD k 0) with hlt | heq
  · exact hlt
  · exact absurd hacc (not_lt_of_bit6 (b64_scan_bit src url body hsize fuel acc h k hk heq))

/-- The misplaced-pad classifier terminates on any text with enough fuel. -/
theorem classify_loop_some (src : Array UInt8) (body : UInt32) (hsize : body.toNat < 2 ^ 32) (fuel : Nat) :
    ∀ (m : Bool) (i : UInt32), body.toNat - i.toNat < fuel → i.toNat ≤ body.toNat →
      ∃ r, base64_classify.loop1 src body m i fuel = some r := by
  induction fuel with
  | zero => intro m i hf _; omega
  | succ fuel ih =>
    intro m i hf hi
    unfold base64_classify.loop1
    by_cases hc : (decide (i < body) && !m) = true
    · rw [if_pos hc]
      have hlt : i.toNat < body.toNat := by
        rw [Bool.and_eq_true] at hc
        exact UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc.1)
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      exact ih _ (i + 1) (by omega) (by omega)
    · rw [if_neg hc]
      exact ⟨_, rfl⟩

theorem classify_some (src : Array UInt8) (body : UInt32) (hsize : body.toNat < 2 ^ 32) (fuel : Nat) (hf : body.toNat < fuel) :
    ∃ r, base64_classify src body fuel = some r := by
  obtain ⟨⟨m, i⟩, h⟩ := classify_loop_some src body hsize fuel false 0 (by simp; omega) (by simp)
  refine ⟨if m then .InvalidPadding else if (body % 4 == 1) then .InvalidLength else .InvalidCharacter, ?_⟩
  unfold base64_classify
  simp [h]

/-! ## The decoded size on any text -/

theorem decoded_size_of_err (src : Array UInt8) (url : Bool) (fuel : Nat)
    (h : base64_unpadded_length src fuel = some (.Err .InvalidPadding)) :
    base64_decoded_size src url fuel = some (.Err .InvalidPadding) := by
  unfold base64_decoded_size; rw [h]; rfl

/-- The byte count the decoder reports for a body of `body` symbols. -/
def decSize (body : Nat) : Nat := body / 4 * 3 + (if body % 4 = 0 then 0 else body % 4 - 1)

theorem decSize_le (body : Nat) : decSize body ≤ body := by unfold decSize; split <;> omega

/-- `base64_decoded_size` on any text: an error, or the facts that make the body an encoding. -/
theorem decoded_size_gen (src : Array UInt8) (url : Bool) (fuel : Nat) (hsize : src.size + 4 < 2 ^ 32) (hf : src.size + 4 < fuel) :
    (∃ reason, base64_decoded_size src url fuel = some (.Err reason)) ∨
    ∃ pads : Nat, pads ≤ 2 ∧ TrailingPads src pads ∧ (pads = 0 ∨ (src.size % 4 = 0 ∧ 2 ≤ (src.size - pads) % 4)) ∧
      (src.size - pads) % 4 ≠ 1 ∧ AllSymbols src (b64values url) (src.size - pads) ∧
      ((src.size - pads) % 4 = 2 → (symValue url (src.getD (src.size - pads - 1) 0) &&& 15) = 0) ∧
      ((src.size - pads) % 4 = 3 → (symValue url (src.getD (src.size - pads - 1) 0) &&& 3) = 0) ∧
      base64_decoded_size src url fuel = some (.Ok (decSize (src.size - pads)).toUInt32) := by
  rcases unpadded_length_gen src (by omega) fuel (by omega) with herr | ⟨pads, hp2, htp, hbad, hlen⟩
  · left; exact ⟨_, decoded_size_of_err src url fuel herr⟩
  obtain ⟨body, hbody⟩ : ∃ body, body = src.size - pads := ⟨_, rfl⟩
  rw [← hbody] at hlen hbad
  have hb32 : (body.toUInt32).toNat = body := toUInt32_toNat_of_lt _ (by omega)
  have hrest : (body.toUInt32 % 4).toNat = body % 4 := by
    rw [UInt32.toNat_mod, hb32, show (4 : UInt32).toNat = 4 by decide]
  have hdiv : (body.toUInt32 / 4).toNat = body / 4 := by
    rw [UInt32.toNat_div, hb32, show (4 : UInt32).toNat = 4 by decide]
  obtain ⟨acc, hscan⟩ := b64_scan_some src url body.toUInt32 (by omega) fuel (by omega)
  unfold base64_decoded_size
  rw [hlen]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hscan]
  by_cases hacc : acc.toNat < 64
  · have hge : decide (acc ≥ (64 : UInt32)) = false := by
      apply decide_eq_false; intro h; have := UInt32.le_iff_toNat_le.mp h
      rw [show (64 : UInt32).toNat = 64 by decide] at this; omega
    simp only [hge, Bool.false_eq_true, ↓reduceIte]
    have hall : AllSymbols src (b64values url) body := by
      have := all_symbols_of_scan src url body.toUInt32 (by omega) fuel acc hscan hacc; rwa [hb32] at this
    by_cases h1 : body % 4 = 1
    · left
      have hb : (body.toUInt32 % 4 == 1) = true := by rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h1]; rfl
      simp only [hb, ↓reduceIte]
      exact ⟨_, rfl⟩
    have hb1 : (body.toUInt32 % 4 == 1) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; exact h1 h'
    simp only [hb1, Bool.false_eq_true, ↓reduceIte, base64_value_eq]
    by_cases h0 : body = 0
    · have hb : (body.toUInt32 == 0) = true := by rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hb32, h0]; rfl
      have hr0 : (body.toUInt32 % 4 == 0) = true := by rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h0]; rfl
      simp only [hb, hr0, ↓reduceIte, Bool.true_or, Option.bind_some]
      right
      refine ⟨pads, hp2, htp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hbody]
      · exact hbad
      · exact h1
      · exact hall
      · exact fun h => absurd h (by omega)
      · exact fun h => absurd h (by omega)
      · rw [h0]; rfl
    have hb0 : (body.toUInt32 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hb32] at h'; simp at h'; exact h0 h'
    have hidx : (body.toUInt32 - 1).toNat = body - 1 := by
      rw [UInt32.toNat_sub_of_le, hb32, show (1 : UInt32).toNat = 1 by decide]
      rw [UInt32.le_iff_toNat_le, hb32, show (1 : UInt32).toNat = 1 by decide]; omega
    simp only [hb0, Bool.false_eq_true, ↓reduceIte, Option.bind_some, hidx]
    split
    · rename_i hcan
      right
      refine ⟨pads, hp2, htp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hbody]
      · exact hbad
      · exact h1
      · exact hall
      · intro h2
        have hr0 : (body.toUInt32 % 4 == 0) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
        have hr2 : (body.toUInt32 % 4 == 2) = true := by rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h2]; rfl
        have hr3 : (body.toUInt32 % 4 == 3) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
        rw [hr0, hr2, hr3] at hcan
        simpa using hcan
      · intro h3
        have hr0 : (body.toUInt32 % 4 == 0) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
        have hr2 : (body.toUInt32 % 4 == 2) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
        have hr3 : (body.toUInt32 % 4 == 3) = true := by rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h3]; rfl
        rw [hr0, hr2, hr3] at hcan
        simpa using hcan
      · -- the reported size
        congr 3
        apply UInt32.toNat.inj
        rw [toUInt32_toNat_of_lt _ (by have := decSize_le body; omega)]
        unfold decSize
        have hmul : (body.toUInt32 / 4 * 3).toNat = body / 4 * 3 := by
          rw [UInt32.toNat_mul, hdiv, show (3 : UInt32).toNat = 3 by decide, Nat.mod_eq_of_lt (by omega)]
        by_cases hr0 : body % 4 = 0
        · have hb : (body.toUInt32 % 4 == 0) = true := by rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, hr0]; rfl
          rw [if_pos hb, if_pos hr0, UInt32.toNat_add, hmul, show (0 : UInt32).toNat = 0 by decide, Nat.mod_eq_of_lt (by omega)]
        · have hb : (body.toUInt32 % 4 == 0) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; exact hr0 h'
          have hsub : (body.toUInt32 % 4 - 1).toNat = body % 4 - 1 := by
            rw [UInt32.toNat_sub_of_le, hrest, show (1 : UInt32).toNat = 1 by decide]
            rw [UInt32.le_iff_toNat_le, hrest, show (1 : UInt32).toNat = 1 by decide]; omega
          rw [if_neg (by simpa using hb), if_neg hr0, UInt32.toNat_add, hmul, hsub, Nat.mod_eq_of_lt (by omega)]
    · left; exact ⟨_, rfl⟩
  · have hge : decide (acc ≥ (64 : UInt32)) = true := by
      apply decide_eq_true; rw [ge_iff_le, UInt32.le_iff_toNat_le, show (64 : UInt32).toNat = 64 by decide]; omega
    simp only [hge, ↓reduceIte]
    obtain ⟨r, hr⟩ := classify_some src body.toUInt32 (by omega) fuel (by omega)
    rw [hr]
    left; exact ⟨r, rfl⟩

/-! ## The decoder on an accepted text -/

/-- The word the tail reads from two symbols, and from three. -/
def tail2Word (src : Array UInt8) (url : Bool) (g : Nat) : UInt32 :=
  (symValue url (src.getD (4 * g) 0) <<< 18) ||| (symValue url (src.getD (4 * g + 1) 0) <<< 12)
def tail3Word (src : Array UInt8) (url : Bool) (g : Nat) : UInt32 :=
  tail2Word src url g ||| (symValue url (src.getD (4 * g + 2) 0) <<< 6)

theorem decode_of_err (src dst : Array UInt8) (url : Bool) (fuel : Nat) (reason : EncodingError)
    (h : base64_decoded_size src url fuel = some (.Err reason)) :
    base64_decode dst src url fuel = some (.Err reason, dst) := by
  unfold base64_decode; rw [h]; rfl

theorem decode_too_small (src dst : Array UInt8) (url : Bool) (fuel : Nat) (needed : UInt32)
    (h : base64_decoded_size src url fuel = some (.Ok needed)) (hbig : dst.size < needed.toNat) (hdst_small : dst.size < 2 ^ 32) :
    base64_decode dst src url fuel = some (.Err .DestinationTooSmall, dst) := by
  have hfits : decide (needed > dst.size.toUInt32) = true := by
    apply decide_eq_true; rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, toUInt32_toNat_of_lt _ hdst_small]; exact hbig
  unfold base64_decode; rw [h]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hfits, ↓reduceIte]

/-- The decoder on a text the size pass accepted: the group loop's bytes, then the tail's. -/
theorem b64_decode_of_size (src dst : Array UInt8) (url : Bool) (fuel : Nat) (body : Nat) (hb4 : body + 4 < 2 ^ 32)
    (hb1 : body % 4 ≠ 1) (hsz : base64_decoded_size src url fuel = some (.Ok (decSize body).toUInt32))
    (hdst : decSize body ≤ dst.size) (hdst_small : dst.size < 2 ^ 32) (hf : body < fuel) :
    ∃ dst', base64_decode dst src url fuel = some (.Ok (decSize body).toUInt32, dst') ∧ dst'.size = dst.size ∧
      (∀ k, k < 3 * (body / 4) → dst'.getD k 0 = decByte3 src (b64values url) k) ∧
      (body % 4 = 2 → dst'.getD (3 * (body / 4)) 0 = (tail2Word src url (body / 4) >>> 16).toUInt8) ∧
      (body % 4 = 3 → dst'.getD (3 * (body / 4)) 0 = (tail3Word src url (body / 4) >>> 16).toUInt8 ∧
        dst'.getD (3 * (body / 4) + 1) 0 = (tail3Word src url (body / 4) >>> 8).toUInt8) := by
  have hn_le := decSize_le body
  have hn0 : body % 4 = 0 → decSize body = 3 * (body / 4) := by intro h; unfold decSize; rw [if_pos h]; omega
  have hn2 : body % 4 = 2 → decSize body = 3 * (body / 4) + 1 := by intro h; unfold decSize; rw [if_neg (by omega), h]; omega
  have hn3 : body % 4 = 3 → decSize body = 3 * (body / 4) + 2 := by intro h; unfold decSize; rw [if_neg (by omega), h]; omega
  have hn3g : 3 * (body / 4) ≤ decSize body := by unfold decSize; omega
  have hn32 : ((decSize body).toUInt32).toNat = decSize body := toUInt32_toNat_of_lt _ (by omega)
  have hfits : decide ((decSize body).toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false; intro h; have := UInt32.lt_iff_toNat_lt.mp h
    rw [hn32, toUInt32_toNat_of_lt _ hdst_small] at this; omega
  have hb32 : (body.toUInt32).toNat = body := toUInt32_toNat_of_lt _ (by omega)
  -- the body the decoder recomputes from the size
  have hbody : ((decSize body).toUInt32 / 3 * 4 +
      (if ((decSize body).toUInt32 % 3 == 0) then (0 : UInt32) else (decSize body).toUInt32 % 3 + 1)) = body.toUInt32 := by
    apply UInt32.toNat.inj
    have hdiv : ((decSize body).toUInt32 / 3).toNat = body / 4 := by
      rw [UInt32.toNat_div, hn32, show (3 : UInt32).toNat = 3 by decide]; unfold decSize; split <;> omega
    have hmod : ((decSize body).toUInt32 % 3).toNat = (if body % 4 = 0 then 0 else body % 4 - 1) := by
      rw [UInt32.toNat_mod, hn32, show (3 : UInt32).toNat = 3 by decide]; unfold decSize; split <;> omega
    rw [hb32]
    by_cases h0 : body % 4 = 0
    · have hb : ((decSize body).toUInt32 % 3 == 0) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hmod, if_pos h0]; rfl
      rw [if_pos hb, UInt32.toNat_add, UInt32.toNat_mul, hdiv, show (4 : UInt32).toNat = 4 by decide,
        show (0 : UInt32).toNat = 0 by decide, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have hb : ((decSize body).toUInt32 % 3 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hmod, if_neg h0] at h'; simp at h'; omega
      rw [if_neg (by simpa using hb), UInt32.toNat_add, UInt32.toNat_mul, hdiv, show (4 : UInt32).toNat = 4 by decide,
        UInt32.toNat_add, hmod, if_neg h0, show (1 : UInt32).toNat = 1 by decide, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  have hvalues : (if url then BASE64_URL_VALUES else BASE64_STD_VALUES) = b64values url := rfl
  obtain ⟨dst1, i1, out1, hloop, hsize1, hi1, hout1, hget1⟩ :=
    b64_decode_loop src (b64values url) (body / 4) body.toUInt32 (by rw [hb32]) (by rw [hb32]; omega) fuel dst 0 0
      (by omega) hdst_small (by simp) (by simp) (by simp) (by simp; omega)
  unfold base64_decode
  rw [hsz]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hfits, Bool.false_eq_true, ↓reduceIte, hvalues, hbody, hloop]
  have hrest : (body.toUInt32 - i1).toNat = body % 4 := by
    rw [UInt32.toNat_sub_of_le, hb32, hi1]
    · omega
    · rw [UInt32.le_iff_toNat_le, hb32, hi1]; omega
  have hi1p : (i1 + 1).toNat = 4 * (body / 4) + 1 := by rw [uadd i1 1 1 (by decide) (by omega), hi1]
  have hi1q : (i1 + 2).toNat = 4 * (body / 4) + 2 := by rw [uadd i1 2 2 (by decide) (by omega), hi1]
  have ho1 : (out1 + 1).toNat = 3 * (body / 4) + 1 := by rw [uadd out1 1 1 (by decide) (by omega), hout1]
  have hw3 : ((((b64values url).getD ((src.getD i1.toNat 0).toUInt32).toNat 0).toUInt32 <<< (18 : UInt32)) |||
      (((b64values url).getD ((src.getD (i1 + 1).toNat 0).toUInt32).toNat 0).toUInt32 <<< (12 : UInt32))) |||
      (((b64values url).getD ((src.getD (i1 + 2).toNat 0).toUInt32).toNat 0).toUInt32 <<< (6 : UInt32)) =
      tail3Word src url (body / 4) := by
    unfold tail3Word tail2Word; rw [hi1, hi1p, hi1q]; rfl
  have hw2 : (((b64values url).getD ((src.getD i1.toNat 0).toUInt32).toNat 0).toUInt32 <<< (18 : UInt32)) |||
      (((b64values url).getD ((src.getD (i1 + 1).toNat 0).toUInt32).toNat 0).toUInt32 <<< (12 : UInt32)) =
      tail2Word src url (body / 4) := by
    unfold tail2Word; rw [hi1, hi1p]; rfl
  rw [hw3, hw2]
  rcases (show body % 4 = 0 ∨ body % 4 = 2 ∨ body % 4 = 3 by omega) with h0 | h2 | h3
  · have hne2 : (body.toUInt32 - i1 == 2) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest, h0] at h'; simp at h'
    have hne3 : (body.toUInt32 - i1 == 3) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest, h0] at h'; simp at h'
    simp only [hne2, hne3, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
    refine ⟨dst1, rfl, hsize1, ?_, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    intro k hk; rw [hget1 k, if_pos ⟨by simp, hk⟩]
  · have heq2 : (body.toUInt32 - i1 == 2) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h2]; rfl
    have hne3 : (body.toUInt32 - i1 == 3) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest, h2] at h'; simp at h'
    simp only [heq2, hne3, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
    have hn' := hn2 h2
    refine ⟨_, rfl, by rw [Array.size_setIfInBounds, hsize1], ?_, fun _ => ?_, fun h => absurd h (by omega)⟩
    · intro k hk
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hout1, if_neg (by omega), ← Array.getD_eq_getD_getElem?,
        hget1 k, if_pos ⟨by simp, hk⟩]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hout1, if_pos rfl, if_pos (by rw [hsize1]; omega),
        Option.getD_some]
  · have hne2 : (body.toUInt32 - i1 == 2) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest, h3] at h'; simp at h'
    have heq3 : (body.toUInt32 - i1 == 3) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h3]; rfl
    simp only [hne2, heq3, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
    have hn' := hn3 h3
    refine ⟨_, rfl, by rw [Array.size_setIfInBounds, Array.size_setIfInBounds, hsize1], ?_, fun h => absurd h (by omega), fun _ => ⟨?_, ?_⟩⟩
    · intro k hk
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds, ho1, hout1,
        if_neg (by omega), if_neg (by omega), ← Array.getD_eq_getD_getElem?, hget1 k, if_pos ⟨by simp, hk⟩]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds, ho1, hout1,
        if_neg (by omega), if_pos rfl, if_pos (by rw [hsize1]; omega), Option.getD_some]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, ho1, if_pos rfl,
        if_pos (by rw [Array.size_setIfInBounds, hsize1]; omega), Option.getD_some]

/-! ## The witness: the decoded bytes encode to the text -/

theorem extract_getD (a : Array UInt8) (n k : Nat) (hn : n ≤ a.size) :
    (a.extract 0 n).getD k 0 = if k < n then a.getD k 0 else 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  simp only [Nat.zero_add, Nat.sub_zero, Nat.min_eq_left hn]
  by_cases hk : k < n
  · rw [if_pos hk, if_pos hk, Array.getD_eq_getD_getElem?]
  · rw [if_neg hk, if_neg hk]; rfl

theorem sixbit_of_word (v0 v1 v2 v3 : UInt32) (h0 : v0 < 64) (h1 : v1 < 64) (h2 : v2 < 64) (h3 : v3 < 64) :
    let w : UInt32 := (((v0 <<< 18) ||| (v1 <<< 12)) ||| (v2 <<< 6)) ||| v3
    let w' : UInt32 := (((w >>> 16).toUInt8.toUInt32 <<< 16) ||| ((w >>> 8).toUInt8.toUInt32 <<< 8)) ||| w.toUInt8.toUInt32
    w' >>> 18 = v0 ∧ (w' >>> 12) &&& 63 = v1 ∧ (w' >>> 6) &&& 63 = v2 ∧ w' &&& 63 = v3 := by
  intro w w'; refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem sixbit_of_tail2 (v0 v1 : UInt32) (h0 : v0 < 64) (h1 : v1 < 64) (hc : v1 &&& 15 = 0) :
    let w : UInt32 := (v0 <<< 18) ||| (v1 <<< 12)
    let w' : UInt32 := (((w >>> 16).toUInt8.toUInt32 <<< 16) ||| ((0 : UInt8).toUInt32 <<< 8)) ||| (0 : UInt8).toUInt32
    w' >>> 18 = v0 ∧ (w' >>> 12) &&& 63 = v1 := by
  intro w w'; refine ⟨?_, ?_⟩ <;> bv_decide

theorem sixbit_of_tail3 (v0 v1 v2 : UInt32) (h0 : v0 < 64) (h1 : v1 < 64) (h2 : v2 < 64) (hc : v2 &&& 3 = 0) :
    let w : UInt32 := ((v0 <<< 18) ||| (v1 <<< 12)) ||| (v2 <<< 6)
    let w' : UInt32 := (((w >>> 16).toUInt8.toUInt32 <<< 16) ||| ((w >>> 8).toUInt8.toUInt32 <<< 8)) ||| (0 : UInt8).toUInt32
    w' >>> 18 = v0 ∧ (w' >>> 12) &&& 63 = v1 ∧ (w' >>> 6) &&& 63 = v2 := by
  intro w w'; refine ⟨?_, ?_, ?_⟩ <;> bv_decide

theorem symValue_lt64 (url : Bool) (b : UInt8) (h : (symValue url b).toNat < 64) : symValue url b < (64 : UInt32) := by
  rw [UInt32.lt_iff_toNat_lt]; simpa using h

/-- The decoder's word of group `j`, spelled with `symValue`. -/
theorem decWord_eq (src : Array UInt8) (url : Bool) (j : Nat) :
    decWord src (b64values url) j = (((symValue url (src.getD (4 * j) 0) <<< 18) ||| (symValue url (src.getD (4 * j + 1) 0) <<< 12)) |||
      (symValue url (src.getD (4 * j + 2) 0) <<< 6)) ||| symValue url (src.getD (4 * j + 3) 0) := rfl

/-- A symbol of a full group reads back from the decoded bytes. -/
theorem sym_full_group (src dst' : Array UInt8) (url : Bool) (body : Nat) (hall : AllSymbols src (b64values url) body)
    (n : Nat) (hn : n ≤ dst'.size) (h3n : 3 * (body / 4) ≤ n)
    (hfull : ∀ k, k < 3 * (body / 4) → dst'.getD k 0 = decByte3 src (b64values url) k)
    (k : Nat) (hk : k < 4 * (body / 4)) :
    src.getD k 0 = encSym (dst'.extract 0 n) (b64symbols url) k := by
  obtain ⟨j, hj⟩ : ∃ j, j = k / 4 := ⟨_, rfl⟩
  have hjg : j < body / 4 := by omega
  have hb0 : (dst'.extract 0 n).getD (3 * j) 0 = decByte3 src (b64values url) (3 * j) := by
    rw [extract_getD _ _ _ hn, if_pos (by omega), hfull _ (by omega)]
  have hb1 : (dst'.extract 0 n).getD (3 * j + 1) 0 = decByte3 src (b64values url) (3 * j + 1) := by
    rw [extract_getD _ _ _ hn, if_pos (by omega), hfull _ (by omega)]
  have hb2 : (dst'.extract 0 n).getD (3 * j + 2) 0 = decByte3 src (b64values url) (3 * j + 2) := by
    rw [extract_getD _ _ _ hn, if_pos (by omega), hfull _ (by omega)]
  have hv : ∀ t, t < 4 → (symValue url (src.getD (4 * j + t) 0)).toNat < 64 := fun t ht => hall _ (by omega)
  have hw := sixbit_of_word _ _ _ _ (symValue_lt64 _ _ (hv 0 (by omega))) (symValue_lt64 _ _ (hv 1 (by omega)))
    (symValue_lt64 _ _ (hv 2 (by omega))) (symValue_lt64 _ _ (hv 3 (by omega)))
  simp only [Nat.add_zero] at hw
  rw [← decWord_eq] at hw
  have hword : encWord (dst'.extract 0 n) j =
      (((decWord src (b64values url) j >>> 16).toUInt8.toUInt32 <<< 16) |||
        ((decWord src (b64values url) j >>> 8).toUInt8.toUInt32 <<< 8)) ||| (decWord src (b64values url) j).toUInt8.toUInt32 := by
    unfold encWord
    rw [hb0, hb1, hb2]
    unfold decByte3
    rw [show 3 * j % 3 = 0 by omega, show 3 * j / 3 = j by omega, show (3 * j + 1) % 3 = 1 by omega,
      show (3 * j + 1) / 3 = j by omega, show (3 * j + 2) % 3 = 2 by omega, show (3 * j + 2) / 3 = j by omega]
    simp only [↓reduceIte, Nat.succ_ne_zero, Nat.reduceEqDiff]
  unfold encSym
  rw [← hj, hword]
  obtain ⟨t, ht⟩ : ∃ t, t = k % 4 := ⟨_, rfl⟩
  have hkt : k = 4 * j + t := by omega
  rw [← ht, hkt]
  have hsym : ∀ t', t' < 4 → (b64symbols url).getD (symValue url (src.getD (4 * j + t') 0)).toNat 0 = src.getD (4 * j + t') 0 :=
    fun t' ht' => symbol_symValue url _ (hv t' ht')
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with h | h | h | h <;> subst h
  · unfold sixbit; simp only [↓reduceIte]; rw [hw.1, Nat.add_zero]; exact (hsym 0 (by omega)).symm
  · unfold sixbit; simp only [Nat.one_ne_zero, ↓reduceIte]; rw [hw.2.1]; exact (hsym 1 (by omega)).symm
  · unfold sixbit; simp only [Nat.succ_ne_zero, Nat.reduceEqDiff, ↓reduceIte]; rw [hw.2.2.1]; exact (hsym 2 (by omega)).symm
  · unfold sixbit; simp only [Nat.succ_ne_zero, Nat.reduceEqDiff, ↓reduceIte]; rw [hw.2.2.2]; exact (hsym 3 (by omega)).symm

/-- The decoded bytes are a source whose encoding is the text. -/
theorem encoded_of_decoded (src dst' : Array UInt8) (url : Bool) (pads : Nat) (hp2 : pads ≤ 2) (htp : TrailingPads src pads)
    (hbad : pads = 0 ∨ (src.size % 4 = 0 ∧ 2 ≤ (src.size - pads) % 4)) (hb1 : (src.size - pads) % 4 ≠ 1)
    (hall : AllSymbols src (b64values url) (src.size - pads))
    (hc2 : (src.size - pads) % 4 = 2 → (symValue url (src.getD (src.size - pads - 1) 0) &&& 15) = 0)
    (hc3 : (src.size - pads) % 4 = 3 → (symValue url (src.getD (src.size - pads - 1) 0) &&& 3) = 0)
    (hn : decSize (src.size - pads) ≤ dst'.size)
    (hfull : ∀ k, k < 3 * ((src.size - pads) / 4) → dst'.getD k 0 = decByte3 src (b64values url) k)
    (ht2 : (src.size - pads) % 4 = 2 →
      dst'.getD (3 * ((src.size - pads) / 4)) 0 = (tail2Word src url ((src.size - pads) / 4) >>> 16).toUInt8)
    (ht3 : (src.size - pads) % 4 = 3 →
      dst'.getD (3 * ((src.size - pads) / 4)) 0 = (tail3Word src url ((src.size - pads) / 4) >>> 16).toUInt8 ∧
      dst'.getD (3 * ((src.size - pads) / 4) + 1) 0 = (tail3Word src url ((src.size - pads) / 4) >>> 8).toUInt8) :
    ∃ pad, Encoded (dst'.extract 0 (decSize (src.size - pads))) src url pad := by
  obtain ⟨body, hbody⟩ : ∃ body, body = src.size - pads := ⟨_, rfl⟩
  rw [← hbody] at hbad hb1 hall hc2 hc3 hn hfull ht2 ht3 ⊢
  have hpb : body ≤ src.size := by omega
  obtain ⟨n, hn_def⟩ : ∃ n, n = decSize body := ⟨_, rfl⟩
  rw [← hn_def] at hn ⊢
  have hn0 : body % 4 = 0 → n = 3 * (body / 4) := by intro h; rw [hn_def]; unfold decSize; rw [if_pos h]; omega
  have hn2 : body % 4 = 2 → n = 3 * (body / 4) + 1 := by intro h; rw [hn_def]; unfold decSize; rw [if_neg (by omega), h]; omega
  have hn3 : body % 4 = 3 → n = 3 * (body / 4) + 2 := by intro h; rw [hn_def]; unfold decSize; rw [if_neg (by omega), h]; omega
  have hn3g : 3 * (body / 4) ≤ n := by rw [hn_def]; unfold decSize; omega
  have hsize_ex : (dst'.extract 0 n).size = n := by rw [Array.size_extract]; omega
  -- the symbol count and the encoded size of the decoded bytes
  have hcount : symCount n = body := by
    rw [symCount_eq]
    rcases (show body % 4 = 0 ∨ body % 4 = 2 ∨ body % 4 = 3 by omega) with h | h | h
    · rw [hn0 h]; rw [if_pos (by omega)]; omega
    · rw [hn2 h]; rw [if_neg (by omega)]; omega
    · rw [hn3 h]; rw [if_neg (by omega)]; omega
  have hsyms : ∀ k, k < body → src.getD k 0 = encSym (dst'.extract 0 n) (b64symbols url) k := by
    intro k hk
    by_cases hkg : k < 4 * (body / 4)
    · exact sym_full_group src dst' url body hall n hn hn3g hfull k hkg
    · -- the tail group
      obtain ⟨g, hg⟩ : ∃ g, g = body / 4 := ⟨_, rfl⟩
      rw [← hg] at hkg hfull ht2 ht3 hn0 hn2 hn3 hn3g
      have hsym : ∀ t', 4 * g + t' < body →
          (b64symbols url).getD (symValue url (src.getD (4 * g + t') 0)).toNat 0 = src.getD (4 * g + t') 0 :=
        fun t' ht' => symbol_symValue url _ (hall _ ht')
      have hv : ∀ t', 4 * g + t' < body → symValue url (src.getD (4 * g + t') 0) < (64 : UInt32) :=
        fun t' ht' => symValue_lt64 _ _ (hall _ ht')
      unfold encSym
      rw [show k / 4 = g by omega]
      rcases (show body % 4 = 2 ∨ body % 4 = 3 by omega) with h2 | h3
      · have hnv := hn2 h2
        have hw := sixbit_of_tail2 _ _ (hv 0 (by omega)) (hv 1 (by omega)) (by rw [show 4 * g + 1 = body - 1 by omega]; exact hc2 h2)
        simp only [Nat.add_zero] at hw
        have hword : encWord (dst'.extract 0 n) g =
            (((tail2Word src url g >>> 16).toUInt8.toUInt32 <<< 16) ||| ((0 : UInt8).toUInt32 <<< 8)) ||| (0 : UInt8).toUInt32 := by
          unfold encWord
          rw [extract_getD _ _ _ hn, extract_getD _ _ _ hn, extract_getD _ _ _ hn, if_pos (by omega), if_neg (by omega),
            if_neg (by omega), ht2 h2]
        rw [hword]
        rcases (show k % 4 = 0 ∨ k % 4 = 1 by omega) with h | h
        · rw [h]; unfold sixbit; simp only [↓reduceIte]
          have := hw.1; unfold tail2Word; rw [this, show k = 4 * g by omega]; exact (hsym 0 (by omega)).symm
        · rw [h]; unfold sixbit; simp only [Nat.one_ne_zero, ↓reduceIte]
          have := hw.2; unfold tail2Word; rw [this, show k = 4 * g + 1 by omega]; exact (hsym 1 (by omega)).symm
      · have hnv := hn3 h3
        have hw := sixbit_of_tail3 _ _ _ (hv 0 (by omega)) (hv 1 (by omega)) (hv 2 (by omega))
          (by rw [show 4 * g + 2 = body - 1 by omega]; exact hc3 h3)
        simp only [Nat.add_zero] at hw
        have hword : encWord (dst'.extract 0 n) g =
            (((tail3Word src url g >>> 16).toUInt8.toUInt32 <<< 16) ||| ((tail3Word src url g >>> 8).toUInt8.toUInt32 <<< 8)) |||
              (0 : UInt8).toUInt32 := by
          unfold encWord
          rw [extract_getD _ _ _ hn, extract_getD _ _ _ hn, extract_getD _ _ _ hn, if_pos (by omega), if_pos (by omega),
            if_neg (by omega), (ht3 h3).1, (ht3 h3).2]
        rw [hword]
        rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 by omega) with h | h | h
        · rw [h]; unfold sixbit; simp only [↓reduceIte]
          have := hw.1; unfold tail3Word tail2Word; rw [this, show k = 4 * g by omega]; exact (hsym 0 (by omega)).symm
        · rw [h]; unfold sixbit; simp only [Nat.one_ne_zero, ↓reduceIte]
          have := hw.2.1; unfold tail3Word tail2Word; rw [this, show k = 4 * g + 1 by omega]
          exact (hsym 1 (by omega)).symm
        · rw [h]; unfold sixbit; simp only [Nat.succ_ne_zero, Nat.reduceEqDiff, ↓reduceIte]
          have := hw.2.2; unfold tail3Word tail2Word; rw [this, show k = 4 * g + 2 by omega]
          exact (hsym 2 (by omega)).symm
  by_cases hp0 : pads = 0
  · -- no padding: the text is the symbols
    have hsz : src.size = body := by omega
    refine ⟨false, ?_, ?_, ?_⟩
    · rw [hsize_ex, hsz]; unfold encSize
      rcases (show body % 4 = 0 ∨ body % 4 = 2 ∨ body % 4 = 3 by omega) with h | h | h
      · rw [hn0 h, if_pos (by omega)]; omega
      · rw [hn2 h, if_neg (by omega), if_neg Bool.false_ne_true]; omega
      · rw [hn3 h, if_neg (by omega), if_neg Bool.false_ne_true]; omega
    · intro k hk; rw [hsize_ex, hcount] at hk; exact hsyms k hk
    · intro k hk1 hk2
      rw [hsize_ex, hcount] at hk1
      rw [hsize_ex] at hk2
      exfalso
      unfold encSize at hk2
      rcases (show body % 4 = 0 ∨ body % 4 = 2 ∨ body % 4 = 3 by omega) with h | h | h
      · rw [hn0 h, if_pos (by omega)] at hk2; omega
      · rw [hn2 h, if_neg (by omega), if_neg Bool.false_ne_true] at hk2; omega
      · rw [hn3 h, if_neg (by omega), if_neg Bool.false_ne_true] at hk2; omega
  · -- padding: the text is a multiple of four ending in `pads` pads
    have hp4 : src.size % 4 = 0 ∧ 2 ≤ body % 4 := by rcases hbad with h | h; exact absurd h hp0; exact h
    have hsz : src.size = 4 * (body / 4) + 4 := by omega
    refine ⟨true, ?_, ?_, ?_⟩
    · rw [hsize_ex, hsz]; unfold encSize
      rcases (show body % 4 = 2 ∨ body % 4 = 3 by omega) with h | h
      · rw [hn2 h, if_neg (by omega), if_pos rfl]; omega
      · rw [hn3 h, if_neg (by omega), if_pos rfl]; omega
    · intro k hk; rw [hsize_ex, hcount] at hk; exact hsyms k hk
    · intro k hk1 hk2
      rw [hsize_ex, hcount] at hk1
      have hk' : k < src.size := by
        rw [hsize_ex] at hk2; unfold encSize at hk2
        rcases (show body % 4 = 2 ∨ body % 4 = 3 by omega) with h | h
        · rw [hn2 h, if_neg (by omega), if_pos rfl] at hk2; omega
        · rw [hn3 h, if_neg (by omega), if_pos rfl] at hk2; omega
      have := htp.2 (src.size - 1 - k) (by omega)
      rw [show src.size - 1 - (src.size - 1 - k) = k by omega] at this
      exact this

/-! ## Strictness -/

/-- What `base64_decode` accepts is an encoding: the bytes it wrote (the first
`n` of the destination) are a source whose encoding — padded iff the text
carries padding — is the text. -/
theorem base64_decode_strict (src dst : Array UInt8) (url : Bool) (fuel : Nat) (n : UInt32) (dst' : Array UInt8)
    (hsize : src.size + 4 < 2 ^ 32) (hdst_small : dst.size < 2 ^ 32) (hf : src.size + 4 < fuel)
    (h : base64_decode dst src url fuel = some (.Ok n, dst')) :
    n.toNat ≤ dst.size ∧ dst'.size = dst.size ∧ ∃ pad, Encoded (dst'.extract 0 n.toNat) src url pad := by
  rcases decoded_size_gen src url fuel hsize hf with ⟨reason, herr⟩ | ⟨pads, hp2, htp, hbad, hb1, hall, hc2, hc3, hok⟩
  · rw [decode_of_err src dst url fuel reason herr] at h; simp at h
  · have hn32 : ((decSize (src.size - pads)).toUInt32).toNat = decSize (src.size - pads) :=
      toUInt32_toNat_of_lt _ (by have := decSize_le (src.size - pads); omega)
    by_cases hfit : decSize (src.size - pads) ≤ dst.size
    · obtain ⟨dst'', hdec, hsize', hfull, ht2, ht3⟩ :=
        b64_decode_of_size src dst url fuel (src.size - pads) (by omega) hb1 hok hfit hdst_small (by omega)
      rw [hdec] at h
      simp only [Option.some.injEq, Prod.mk.injEq, Result_u32_EncodingError.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hn32]
      exact ⟨hfit, hsize', encoded_of_decoded src dst'' url pads hp2 htp hbad hb1 hall hc2 hc3 (by rw [hsize']; exact hfit) hfull ht2 ht3⟩
    · rw [decode_too_small src dst url fuel _ hok (by rw [hn32]; omega) hdst_small] at h; simp at h

/-- Strictness: `base64_decode` succeeds iff the text is an encoding (of a
source the destination holds), for a text of fewer than `2^31 - 8` bytes and
enough fuel. -/
theorem base64_decode_ok_iff (src dst : Array UInt8) (url : Bool) (fuel : Nat)
    (hsize : src.size + 8 < 2 ^ 31) (hdst_small : dst.size < 2 ^ 32) (hf : 2 * src.size + 16 < fuel) :
    (∃ n dst', base64_decode dst src url fuel = some (.Ok n, dst')) ↔ ∃ b pad, Encoded b src url pad ∧ b.size ≤ dst.size := by
  constructor
  · intro ⟨n, dst', h⟩
    obtain ⟨hn, hsize', pad, he⟩ := base64_decode_strict src dst url fuel n dst' (by omega) hdst_small (by omega) h
    refine ⟨_, pad, he, ?_⟩
    rw [Array.size_extract]; omega
  · intro ⟨b, pad, he, hb⟩
    have hbsize : b.size ≤ src.size := by
      have := he.size; unfold encSize at this; split at this <;> (try split at this) <;> omega
    obtain ⟨dst', h, -, -⟩ := base64_decode_encoded b src dst url pad fuel he (by omega) hb hdst_small (by omega)
    exact ⟨_, dst', h⟩

end Oak.Stdlib.Encoding
