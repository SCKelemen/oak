import Std.Tactic.BVDecide
import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.EncodingLaws
import Oak.Stdlib.Base64Laws
import Oak.Stdlib.Base64StrictLaws
import Oak.Stdlib.Base32Laws

/-!
# Oak.Stdlib.Base32StrictLaws — base32 strictness on the extracted `encoding` package

`base32_decode` accepts a text iff it is an encoding: `base32_decode_strict`
builds the witness — the bytes the decoder wrote are a source whose
encoding (padded iff the text carries padding) is the text, in the sense
of `Encoded32` from `Base32Laws`; `base32_decode_encoded` there gives the
converse; `base32_decode_ok_iff` states the equivalence.

The rejection half follows the decoder on arbitrary input: the padding
strip counts trailing `=` (at most six), the misplaced-pad scan refuses a
`=` inside the body, the validity scan stops at the first byte outside the
alphabet (its table value is 32), the length check refuses bodies of one,
three, or six symbols past a group, and the canonical check reads the last
symbol's unused bits. What survives is exactly what the encoder writes: the
decoded bytes reassemble into the decoder's 40-bit words, whose five-bit
fields are the symbol values, and the symbol table inverts the value table
on the alphabet.
-/

namespace Oak.Stdlib.Encoding

set_option maxRecDepth 65536

/-! ## Tables -/

/-- ASCII upper case, as the decoder folds letters: the alphabets accept `a`–`z` for `A`–`Z`. -/
def upper32 (c : UInt8) : UInt8 := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

theorem b32_symbol_value_std : ∀ b : Fin 256, (BASE32_STD_VALUES.getD b.val 0).toNat < 32 →
    BASE32_STD_SYMBOLS.getD (BASE32_STD_VALUES.getD b.val 0).toNat 0 = upper32 b.val.toUInt8 := by decide +kernel
theorem b32_symbol_value_hex : ∀ b : Fin 256, (BASE32_HEX_VALUES.getD b.val 0).toNat < 32 →
    BASE32_HEX_SYMBOLS.getD (BASE32_HEX_VALUES.getD b.val 0).toNat 0 = upper32 b.val.toUInt8 := by decide +kernel
theorem b32_value_upper_std : ∀ b : Fin 256,
    BASE32_STD_VALUES.getD (upper32 b.val.toUInt8).toNat 0 = BASE32_STD_VALUES.getD b.val 0 := by decide +kernel
theorem b32_value_upper_hex : ∀ b : Fin 256,
    BASE32_HEX_VALUES.getD (upper32 b.val.toUInt8).toNat 0 = BASE32_HEX_VALUES.getD b.val 0 := by decide +kernel

/-- The value of a byte, spelled through the tables. -/
theorem val32_eq (hex : Bool) (b : UInt8) : val32 hex b = ((b32values hex).getD (b.toUInt32).toNat 0).toUInt32 := by
  unfold val32; rfl

theorem sym32_eq (hex : Bool) (v : UInt32) : sym32 hex v = (b32symbols hex).getD (v &&& 31).toNat 0 := by
  unfold sym32; rfl

/-- The symbol table inverts the value table on the alphabet, up to letter case. -/
theorem symbol_val32 (hex : Bool) (b : UInt8) (h : (val32 hex b).toNat < 32) : sym32 hex (val32 hex b) = upper32 b := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  have h31 : val32 hex b &&& 31 = val32 hex b := by
    have : val32 hex b < (32 : UInt32) := by rw [UInt32.lt_iff_toNat_lt]; simpa using h
    bv_decide
  rw [sym32_eq, h31, val32_eq]
  rw [val32_eq] at h
  cases hex
  · have := b32_symbol_value_std ⟨b.toNat, hb⟩
    simp only [b32values, Bool.false_eq_true, ↓reduceIte, UInt8.toNat_toUInt32] at h ⊢
    unfold b32symbols; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [this h, toUInt8_toNat]
  · have := b32_symbol_value_hex ⟨b.toNat, hb⟩
    simp only [b32values, ↓reduceIte, UInt8.toNat_toUInt32] at h ⊢
    unfold b32symbols; simp only [↓reduceIte]
    rw [this h, toUInt8_toNat]

/-- The decoder reads the same value from a byte and its upper-case form. -/
theorem val32_upper (hex : Bool) (b : UInt8) : val32 hex (upper32 b) = val32 hex b := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  rw [val32_eq, val32_eq]
  cases hex
  · have := b32_value_upper_std ⟨b.toNat, hb⟩
    rw [toUInt8_toNat] at this
    simp only [b32values, Bool.false_eq_true, ↓reduceIte, UInt8.toNat_toUInt32]
    rw [this]
  · have := b32_value_upper_hex ⟨b.toNat, hb⟩
    rw [toUInt8_toNat] at this
    simp only [b32values, ↓reduceIte, UInt8.toNat_toUInt32]
    rw [this]

theorem upper32_pad_iff (c : UInt8) : upper32 c = 61 ↔ c = 61 := by
  unfold upper32
  constructor
  · intro h; split at h
    · rename_i hc; exfalso
      have h1 : c - 32 = 61 := h
      have h2 : (c - 32).toNat = 61 := by rw [h1]; rfl
      have h3 : 32 ≤ c := UInt8.le_iff_toNat_le.mpr (by have := UInt8.le_iff_toNat_le.mp hc.1; simp at this ⊢; omega)
      rw [UInt8.toNat_sub_of_le _ _ h3] at h2
      have := UInt8.le_iff_toNat_le.mp hc.1; have := UInt8.le_iff_toNat_le.mp hc.2
      simp at *; omega
    · exact h
  · intro h; subst h; rfl

theorem upper32_zero : upper32 0 = 0 := rfl

theorem map_upper_getD (src : Array UInt8) (k : Nat) : (src.map upper32).getD k 0 = upper32 (src.getD k 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases src[k]? <;> rfl

/-! ## The padding strip on any text -/

theorem unpad_loop_gen32 (src : Array UInt8) (hsize : src.size < 2 ^ 32) (fuel : Nat) :
    ∀ p : Nat, p ≤ 6 → TrailingPads src p → 6 - p < fuel →
      ∃ pads : Nat, base32_unpadded_length.loop1 src p.toUInt32 fuel = some pads.toUInt32 ∧ pads ≤ 6 ∧ TrailingPads src pads := by
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
    unfold base32_unpadded_length.loop1
    by_cases hc : p < src.size ∧ p < 6 ∧ src.getD (src.size - 1 - p) 0 = 61
    · have hc1 : decide (p.toUInt32 < src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz, hp32]; exact hc.1
      have hc2 : decide (p.toUInt32 < (6 : UInt32)) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hp32, show (6 : UInt32).toNat = 6 by decide]; exact hc.2.1
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
    · have hstop : ((decide (p.toUInt32 < src.size.toUInt32) && decide (p.toUInt32 < (6 : UInt32))) &&
          (src.getD ((src.size.toUInt32 - 1) - p.toUInt32).toNat 0 == 61)) = false := by
        by_cases h1 : p < src.size
        · by_cases h2 : p < 6
          · have h3 : src.getD (src.size - 1 - p) 0 ≠ 61 := fun h => hc ⟨h1, h2, h⟩
            have : (src.getD ((src.size.toUInt32 - 1) - p.toUInt32).toNat 0 == 61) = false := by
              rw [beq_eq_false_iff_ne, hidx h1]; exact h3
            exact Bool.and_eq_false_iff.mpr (Or.inr this)
          · have : decide (p.toUInt32 < (6 : UInt32)) = false := by
              apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hp32, show (6 : UInt32).toNat = 6 by decide]; exact h2
            exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inr this)))
        · have : decide (p.toUInt32 < src.size.toUInt32) = false := by
            apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz, hp32]; exact h1
          exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inl this)))
      rw [if_neg (by simpa using hstop)]
      exact ⟨p, rfl, hp, htp⟩

/-- The misplaced-pad scan on any text: it reports clean only when no byte of the body is `=`. -/
theorem scan_loop_gen32 (src : Array UInt8) (body : UInt32) (hsize : body.toNat < 2 ^ 32) (fuel : Nat) :
    ∀ (m : Bool) (i : UInt32), i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      ∃ m' i', base32_unpadded_length.loop2 src body m i fuel = some (m', i') ∧
        (m' = false → m = false ∧ ∀ k, i.toNat ≤ k → k < body.toNat → src.getD k 0 ≠ 61) := by
  induction fuel with
  | zero => intro m i _ hf; omega
  | succ fuel ih =>
    intro m i hi hf
    unfold base32_unpadded_length.loop2
    by_cases hc : (decide (i < body) && !m) = true
    · rw [if_pos hc]
      have hc' := Bool.and_eq_true_iff.mp hc
      have hlt : i.toNat < body.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc'.1)
      have hm : m = false := by cases m <;> simp at hc' ⊢
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      obtain ⟨m', i', h, hclean⟩ := ih (src.getD i.toNat 0 == 61) (i + 1) (by omega) (by omega)
      refine ⟨m', i', h, fun hm' => ⟨hm, ?_⟩⟩
      obtain ⟨hb, hrest⟩ := hclean hm'
      intro k hk1 hk2
      by_cases hki : k = i.toNat
      · subst hki; exact beq_eq_false_iff_ne.mp hb
      · exact hrest k (by omega) hk2
    · rw [if_neg hc]
      refine ⟨m, i, rfl, fun hm => ⟨hm, ?_⟩⟩
      intro k hk1 hk2
      exfalso; apply hc
      rw [hm]; simp only [Bool.not_false, Bool.and_true]
      apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; omega

/-- The padding strip on any text: `InvalidPadding`, or a clean body with consistent padding. -/
theorem unpadded_length_gen32 (src : Array UInt8) (hsize : src.size < 2 ^ 32) (fuel : Nat) (hf : src.size + 8 < fuel) :
    (base32_unpadded_length src fuel = some (.Err .InvalidPadding)) ∨
    ∃ pads : Nat, pads ≤ 6 ∧ TrailingPads src pads ∧
      (pads = 0 ∨ (src.size % 8 = 0 ∧ (src.size - pads) % 8 ≠ 0 ∧ pads = 8 - (src.size - pads) % 8)) ∧
      base32_unpadded_length src fuel = some (.Ok (src.size - pads).toUInt32) := by
  have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ hsize
  obtain ⟨pads, hloop, hp6, htp⟩ :=
    unpad_loop_gen32 src hsize fuel 0 (by omega) ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ (by omega)
  have hp32 : (pads.toUInt32).toNat = pads := toUInt32_toNat_of_lt _ (by omega)
  have hbody : (src.size.toUInt32 - pads.toUInt32).toNat = src.size - pads := by
    rw [UInt32.toNat_sub_of_le, hsz, hp32]; rw [UInt32.le_iff_toNat_le, hsz, hp32]; exact htp.1
  have hbody' : src.size.toUInt32 - pads.toUInt32 = (src.size - pads).toUInt32 :=
    UInt32.toNat.inj (by rw [hbody, toUInt32_toNat_of_lt _ (by omega)])
  have hb32 : ((src.size - pads).toUInt32).toNat = src.size - pads := toUInt32_toNat_of_lt _ (by omega)
  have hrest : ((src.size - pads).toUInt32 % 8).toNat = (src.size - pads) % 8 := by
    rw [UInt32.toNat_mod, hb32, show (8 : UInt32).toNat = 8 by decide]
  have hmod8 : (src.size.toUInt32 % 8).toNat = src.size % 8 := by
    rw [UInt32.toNat_mod, hsz, show (8 : UInt32).toNat = 8 by decide]
  have hloop0 : base32_unpadded_length.loop1 src 0 fuel = some pads.toUInt32 := hloop
  obtain ⟨m, i, hscan, hclean⟩ := scan_loop_gen32 src (src.size - pads).toUInt32 (by omega) fuel false 0 (by simp)
    (by rw [hb32]; simp; omega)
  unfold base32_unpadded_length
  simp only [Option.pure_def, Option.bind_eq_bind, hloop0, Option.bind_some]
  rw [hbody', hscan]
  simp only [Option.bind_some]
  cases m
  · -- no misplaced pad
    simp only [Bool.false_or]
    by_cases hbad : pads = 0 ∨ (src.size % 8 = 0 ∧ (src.size - pads) % 8 ≠ 0 ∧ pads = 8 - (src.size - pads) % 8)
    · right
      refine ⟨pads, hp6, htp, hbad, ?_⟩
      rcases hbad with h0 | ⟨h8, hr0, hpe⟩
      · have hp : decide (pads.toUInt32 > (0 : UInt32)) = false := by
          apply decide_eq_false; rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hp32, h0]; simp
        simp only [hp, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      · have h1 : (src.size.toUInt32 % 8 != 0) = false := by
          rw [bne_eq_false_iff_eq]; apply UInt32.toNat.inj; rw [hmod8, h8]; rfl
        have h2 : ((src.size - pads).toUInt32 % 8 == 0) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; exact hr0 h'
        have h3 : (pads.toUInt32 != (8 - (src.size - pads).toUInt32 % 8)) = false := by
          rw [bne_eq_false_iff_eq]; apply UInt32.toNat.inj
          rw [hp32, UInt32.toNat_sub_of_le, hrest, show (8 : UInt32).toNat = 8 by decide]
          · exact hpe
          · rw [UInt32.le_iff_toNat_le, hrest, show (8 : UInt32).toNat = 8 by decide]; omega
        simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, Bool.or_self, Bool.and_false]
    · left
      have hpos : 0 < pads := by omega
      have hp : decide (pads.toUInt32 > (0 : UInt32)) = true := by
        apply decide_eq_true; rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hp32]; exact hpos
      simp only [hp, Bool.true_and]
      by_cases h8 : src.size % 8 = 0
      · have h1 : (src.size.toUInt32 % 8 != 0) = false := by
          rw [bne_eq_false_iff_eq]; apply UInt32.toNat.inj; rw [hmod8, h8]; rfl
        simp only [h1, Bool.false_or]
        by_cases hr0 : (src.size - pads) % 8 = 0
        · have h2 : ((src.size - pads).toUInt32 % 8 == 0) = true := by
            rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, hr0]; rfl
          have h3 : (pads.toUInt32 != (0 : UInt32)) = true := by
            rw [bne_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hp32] at h'; simp at h'; omega
          simp only [h2, ↓reduceIte, h3]
        · have h2 : ((src.size - pads).toUInt32 % 8 == 0) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; exact hr0 h'
          have hne : pads ≠ 8 - (src.size - pads) % 8 := fun h => hbad (Or.inr ⟨h8, hr0, h⟩)
          have h3 : (pads.toUInt32 != (8 - (src.size - pads).toUInt32 % 8)) = true := by
            rw [bne_iff_ne]; intro h; have h' := congrArg UInt32.toNat h
            rw [hp32, UInt32.toNat_sub_of_le, hrest, show (8 : UInt32).toNat = 8 by decide] at h'
            · exact hne h'
            · rw [UInt32.le_iff_toNat_le, hrest, show (8 : UInt32).toNat = 8 by decide]; omega
          simp only [h2, Bool.false_eq_true, ↓reduceIte, h3]
      · have h1 : (src.size.toUInt32 % 8 != 0) = true := by
          rw [bne_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hmod8] at h'; simp at h'; exact h8 h'
        simp only [h1, Bool.true_or, ↓reduceIte]
  · left
    simp only [Bool.true_or, ↓reduceIte]

/-! ## The validity scan on any text -/

theorem valid_loop_gen32 (src : Array UInt8) (hex : Bool) (body : UInt32) (hsize : body.toNat < 2 ^ 32) (fuel : Nat) :
    ∀ (v0 : Bool) (i : UInt32), i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      ∃ v i', base32_decoded_size.loop1 src hex body v0 i fuel = some (v, i') ∧
        (v = true → v0 = true ∧ ∀ k, i.toNat ≤ k → k < body.toNat → (val32 hex (src.getD k 0)).toNat < 32) := by
  induction fuel with
  | zero => intro v0 i _ hf; omega
  | succ fuel ih =>
    intro v0 i hi hf
    unfold base32_decoded_size.loop1
    by_cases hc : (decide (i < body) && v0) = true
    · rw [if_pos hc]
      have hc' := Bool.and_eq_true_iff.mp hc
      have hlt : i.toNat < body.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc'.1)
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      simp only [base32_value_def, Option.bind_eq_bind, Option.bind_some]
      obtain ⟨v, i', h, hvalid⟩ := ih (decide (val32 hex (src.getD i.toNat 0) < 32)) (i + 1) (by omega) (by omega)
      refine ⟨v, i', h, fun hv => ⟨hc'.2, ?_⟩⟩
      obtain ⟨hd, hrest⟩ := hvalid hv
      intro k hk1 hk2
      by_cases hki : k = i.toNat
      · subst hki
        have := of_decide_eq_true hd
        rw [UInt32.lt_iff_toNat_lt, show (32 : UInt32).toNat = 32 by decide] at this; exact this
      · exact hrest k (by omega) hk2
    · rw [if_neg hc]
      refine ⟨v0, i, rfl, fun hv => ⟨hv, ?_⟩⟩
      intro k hk1 hk2
      exfalso; apply hc
      rw [hv, Bool.and_true]
      apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; omega

/-! ## The decoded size on any text -/

/-- Bytes a partial group of `r` symbols carries, as `base32_partial_bytes` computes it. -/
def pbytes32 (r : Nat) : Nat := if r = 2 then 1 else if r = 4 then 2 else if r = 5 then 3 else if r = 7 then 4 else 0

theorem pbytes32_lt (r : Nat) : pbytes32 r < 5 := by
  unfold pbytes32; split <;> (try split) <;> (try split) <;> (try split) <;> omega
theorem pbytes32_le (r : Nat) : pbytes32 r ≤ r := by
  unfold pbytes32; split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- The byte count the decoder reports for a body of `body` symbols. -/
def decSize32 (body : Nat) : Nat := body / 8 * 5 + pbytes32 (body % 8)

theorem base32_partial_bytes_gen (r : Nat) (r32 : UInt32) (hr : r32.toNat = r) (hr8 : r < 8) (fuel : Nat) :
    base32_partial_bytes r32 fuel = some (pbytes32 r).toUInt32 := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 by omega) with h | h | h | h | h | h | h | h <;> subst h
  · have : r32 = 0 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl
  · have : r32 = 1 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl
  · have : r32 = 2 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl
  · have : r32 = 3 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl
  · have : r32 = 4 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl
  · have : r32 = 5 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl
  · have : r32 = 6 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl
  · have : r32 = 7 := UInt32.toNat.inj (by rw [hr]; rfl); subst this; rfl

theorem decoded_size_of_err32 (src : Array UInt8) (hex : Bool) (fuel : Nat)
    (h : base32_unpadded_length src fuel = some (.Err .InvalidPadding)) :
    base32_decoded_size src hex fuel = some (.Err .InvalidPadding) := by
  unfold base32_decoded_size; rw [h]; rfl

/-- `base32_decoded_size` on any text: an error, or the facts that make the body an encoding up to case. -/
theorem decoded_size_gen32 (src : Array UInt8) (hex : Bool) (fuel : Nat) (hsize : src.size + 8 < 2 ^ 32) (hf : src.size + 8 < fuel) :
    (∃ reason, base32_decoded_size src hex fuel = some (.Err reason)) ∨
    ∃ pads : Nat, pads ≤ 6 ∧ TrailingPads src pads ∧
      (pads = 0 ∨ (src.size % 8 = 0 ∧ (src.size - pads) % 8 ≠ 0 ∧ pads = 8 - (src.size - pads) % 8)) ∧
      (src.size - pads) % 8 ≠ 1 ∧ (src.size - pads) % 8 ≠ 3 ∧ (src.size - pads) % 8 ≠ 6 ∧
      (∀ k, k < src.size - pads → (val32 hex (src.getD k 0)).toNat < 32) ∧
      ((src.size - pads) % 8 = 2 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 3) = 0) ∧
      ((src.size - pads) % 8 = 4 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 15) = 0) ∧
      ((src.size - pads) % 8 = 5 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 1) = 0) ∧
      ((src.size - pads) % 8 = 7 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 7) = 0) ∧
      base32_decoded_size src hex fuel = some (.Ok (decSize32 (src.size - pads)).toUInt32) := by
  rcases unpadded_length_gen32 src (by omega) fuel (by omega) with herr | ⟨pads, hp6, htp, hbad, hlen⟩
  · left; exact ⟨_, decoded_size_of_err32 src hex fuel herr⟩
  obtain ⟨body, hbody⟩ : ∃ body, body = src.size - pads := ⟨_, rfl⟩
  rw [← hbody] at hlen hbad
  have hb32 : (body.toUInt32).toNat = body := toUInt32_toNat_of_lt _ (by omega)
  have hrest : (body.toUInt32 % 8).toNat = body % 8 := by rw [UInt32.toNat_mod, hb32, show (8 : UInt32).toNat = 8 by decide]
  have hdiv : (body.toUInt32 / 8).toNat = body / 8 := by rw [UInt32.toNat_div, hb32, show (8 : UInt32).toNat = 8 by decide]
  have hr8 : body % 8 < 8 := Nat.mod_lt _ (by omega)
  unfold base32_decoded_size
  rw [hlen]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- the length check
  by_cases hL : body % 8 = 1 ∨ body % 8 = 3 ∨ body % 8 = 6
  · left
    have hb : (((body.toUInt32 % 8 == 1) || (body.toUInt32 % 8 == 3)) || (body.toUInt32 % 8 == 6)) = true := by
      rcases hL with h | h | h
      · rw [rest_eq body 1 1 rfl (by omega) h]; decide
      · rw [rest_eq body 3 3 rfl (by omega) h]; decide
      · rw [rest_eq body 6 6 rfl (by omega) h]; decide
    simp only [hb, ↓reduceIte]
    exact ⟨_, rfl⟩
  have hbL : (((body.toUInt32 % 8 == 1) || (body.toUInt32 % 8 == 3)) || (body.toUInt32 % 8 == 6)) = false := by
    have h1 : (body.toUInt32 % 8 == 1) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
    have h3 : (body.toUInt32 % 8 == 3) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
    have h6 : (body.toUInt32 % 8 == 6) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'; simp at h'; omega
    rw [h1, h3, h6]; rfl
  simp only [hbL, Bool.false_eq_true, ↓reduceIte]
  -- the validity scan
  obtain ⟨v, i', hvl, hvalid⟩ :=
    valid_loop_gen32 src hex body.toUInt32 (by omega) fuel true 0 (by simp) (by rw [hb32]; simp; omega)
  rw [hvl]
  simp only [Option.bind_some]
  -- the last symbol
  obtain ⟨last, hlast, hlastv⟩ : ∃ last : UInt32,
      (if (body.toUInt32 == 0) then some (0 : UInt32) else base32_value (src.getD (body.toUInt32 - 1).toNat 0) hex fuel) = some last ∧
      (body ≠ 0 → last = val32 hex (src.getD (body - 1) 0)) := by
    by_cases h0 : body = 0
    · have hb : (body.toUInt32 == 0) = true := by rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hb32, h0]; rfl
      exact ⟨0, by rw [if_pos hb], fun h => absurd h0 h⟩
    · have hb : (body.toUInt32 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hb32] at h'; simp at h'; exact h0 h'
      have hidx : (body.toUInt32 - 1).toNat = body - 1 := by
        rw [UInt32.toNat_sub_of_le, hb32, show (1 : UInt32).toNat = 1 by decide]
        rw [UInt32.le_iff_toNat_le, hb32, show (1 : UInt32).toNat = 1 by decide]; omega
      exact ⟨_, by rw [if_neg (by simpa using hb), base32_value_def], fun _ => by rw [hidx]⟩
  rw [hlast]
  simp only [Option.bind_some]
  cases v
  · -- a byte outside the alphabet
    simp only [Bool.not_false, ↓reduceIte]
    left; exact ⟨_, rfl⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hall : ∀ k, k < body → (val32 hex (src.getD k 0)).toNat < 32 := by
      intro k hk; exact (hvalid rfl).2 k (by simp) (by rw [hb32]; exact hk)
    rw [unused32_eq]
    split
    · left; exact ⟨_, rfl⟩
    · rename_i hcan
      right
      have hq := base32_partial_bytes_gen (body % 8) (body.toUInt32 % 8) hrest hr8 fuel
      rw [hq]
      simp only [Option.bind_some]
      refine ⟨pads, hp6, htp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hbody]
      · exact hbad
      · omega
      · omega
      · omega
      · exact hall
      · intro h2
        rw [rest_eq body 2 2 rfl (by omega) h2, show unused32 2 = 3 from rfl, hlastv (by omega)] at hcan
        simpa using hcan
      · intro h4
        rw [rest_eq body 4 4 rfl (by omega) h4, show unused32 4 = 15 from rfl, hlastv (by omega)] at hcan
        simpa using hcan
      · intro h5
        rw [rest_eq body 5 5 rfl (by omega) h5, show unused32 5 = 1 from rfl, hlastv (by omega)] at hcan
        simpa using hcan
      · intro h7
        rw [rest_eq body 7 7 rfl (by omega) h7, show unused32 7 = 7 from rfl, hlastv (by omega)] at hcan
        simpa using hcan
      · congr 3
        apply UInt32.toNat.inj
        have hpb := pbytes32_lt (body % 8)
        have hmul : (body.toUInt32 / 8 * 5).toNat = body / 8 * 5 := by
          rw [UInt32.toNat_mul, hdiv, show (5 : UInt32).toNat = 5 by decide, Nat.mod_eq_of_lt (by omega)]
        unfold decSize32
        rw [toUInt32_toNat_of_lt _ (by omega), UInt32.toNat_add, hmul, toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The decoder on an accepted text -/

/-- The value the decoder reads at offset `s` of symbol group `g`, zero past the body. -/
def dvb (src : Array UInt8) (hex : Bool) (body g s : Nat) : UInt64 :=
  if 8 * g + s < body then (val32 hex (src.getD (8 * g + s) 0)).toUInt64 else 0

/-- The decoder's word of symbol group `g`. -/
def decWord32 (src : Array UInt8) (hex : Bool) (body g : Nat) : UInt64 :=
  mk8 (dvb src hex body g 0) (dvb src hex body g 1) (dvb src hex body g 2) (dvb src hex body g 3)
    (dvb src hex body g 4) (dvb src hex body g 5) (dvb src hex body g 6) (dvb src hex body g 7)

theorem dec_word_gen (src : Array UInt8) (hex : Bool) (body : Nat) (i take : UInt32) (g : Nat)
    (hi : i.toNat = 8 * g) (hi8 : i.toNat + 7 < 2 ^ 32) (htake : take.toNat = min 8 (body - 8 * g)) :
    mk8 (dv src hex i take 0) (dv src hex i take 1) (dv src hex i take 2) (dv src hex i take 3)
      (dv src hex i take 4) (dv src hex i take 5) (dv src hex i take 6) (dv src hex i take 7) = decWord32 src hex body g := by
  have hd : ∀ s : UInt32, s.toNat < 8 → dv src hex i take s = dvb src hex body g s.toNat := by
    intro s hs
    unfold dv dvb
    by_cases hlt : s < take
    · have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
      rw [if_pos (decide_eq_true hlt), uadd i s s.toNat rfl (by omega), hi, if_pos (by omega)]
    · have : ¬ s.toNat < take.toNat := fun h => hlt (UInt32.lt_iff_toNat_lt.mpr h)
      rw [if_neg (by simpa using hlt), if_neg (by omega)]
  unfold decWord32
  rw [hd 0 (by decide), hd 1 (by decide), hd 2 (by decide), hd 3 (by decide), hd 4 (by decide), hd 5 (by decide),
    hd 6 (by decide), hd 7 (by decide)]
  rfl

/-- The decoder's group loop on an accepted text writes the bytes of its words. -/
theorem dec_loop1_gen (src : Array UInt8) (hex : Bool) (body : Nat) (hb8 : body + 8 < 2 ^ 32)
    (_h1 : body % 8 ≠ 1) (_h3 : body % 8 ≠ 3) (_h6 : body % 8 ≠ 6) (body32 : UInt32) (hbody : body32.toNat = body) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32) (g : Nat), i.toNat = 8 * g → out.toNat = 5 * g → 8 * g ≤ body →
      decSize32 body ≤ dst.size → dst.size < 2 ^ 32 → body - 8 * g + 10 < fuel →
      ∃ dst' i' out', base32_decode.loop1 dst src hex body32 i out fuel = some (dst', i', out') ∧ dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 = if 5 * g ≤ k ∧ k < decSize32 body then byteAt (decWord32 src hex body (k / 5)) (k % 5).toUInt32
          else dst.getD k 0 := by
  have hpb := pbytes32_lt (body % 8)
  have hpb' := pbytes32_le (body % 8)
  have hds : decSize32 body = body / 8 * 5 + pbytes32 (body % 8) := rfl
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out g hi hout hg hroom hdst hf
    unfold base32_decode.loop1
    rcases Nat.lt_or_ge (8 * g) body with hlt | hge
    · have hc : decide (i < body32) = true := by apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hbody, hi]; exact hlt
      rw [if_pos hc]
      simp only [Option.pure_def, Option.bind_eq_bind]
      obtain ⟨m, hm⟩ : ∃ m, fuel = m + 9 := ⟨fuel - 9, by omega⟩
      have hsub : (body32 - i).toNat = body - 8 * g := by
        rw [UInt32.toNat_sub_of_le, hbody, hi]; rw [UInt32.le_iff_toNat_le, hbody, hi]; omega
      have htake : (if decide (body32 - i < 8) then body32 - i else (8 : UInt32)).toNat = min 8 (body - 8 * g) := by
        by_cases h8 : body - 8 * g < 8
        · have hc8 : decide (body32 - i < (8 : UInt32)) = true := by
            apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsub, show (8 : UInt32).toNat = 8 by decide]; exact h8
          rw [if_pos hc8, hsub]; omega
        · have hc8 : decide (body32 - i < (8 : UInt32)) = false := by
            apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsub, show (8 : UInt32).toNat = 8 by decide]; exact h8
          rw [if_neg (by simpa using hc8)]; show 8 = _; omega
      rw [hm, dec_loop2_unroll, dec_word_gen src hex body i _ g hi (by omega) htake, ← hm]
      simp only [Option.bind_some]
      have hout5 : out.toNat + 5 < 2 ^ 32 := by omega
      rcases Nat.lt_or_ge (body - 8 * g) 8 with hpart | hfull
      · -- the partial final group
        have hgq : g = body / 8 := by omega
        have hr : body % 8 = body - 8 * g := by omega
        obtain ⟨r, hr'⟩ : ∃ r, r = body - 8 * g := ⟨_, rfl⟩
        have hr8 : r < 8 := by omega
        have htake' : (if decide (body32 - i < 8) then body32 - i else (8 : UInt32)).toNat = r := by rw [htake]; omega
        have hne8 : ((if decide (body32 - i < 8) then body32 - i else (8 : UInt32)) == 8) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [htake'] at h'
          change r = 8 at h'; omega
        have hpb_eq := base32_partial_bytes_gen r _ htake' hr8 fuel
        rw [hne8]
        simp only [Bool.false_eq_true, ↓reduceIte, hpb_eq, Option.bind_some]
        have hpbr := pbytes32_lt r
        have hq32 : ((pbytes32 r).toUInt32).toNat = pbytes32 r := toUInt32_toNat_of_lt _ (by omega)
        have hds' : decSize32 body = 5 * g + pbytes32 r := by rw [hds, ← hgq, hr, ← hr']; omega
        obtain ⟨dst1, hloop3, hsize1, hget1⟩ := dec_loop3_spec out (decWord32 src hex body g) (pbytes32 r).toUInt32 fuel dst 0
          (by omega) (by rw [hq32]; omega) hout5 (by rw [hq32]; omega) (by omega)
        rw [show (0 : UInt32) = (0 : Nat).toUInt32 from rfl, hloop3]
        simp only [Option.bind_some]
        have hi' : (i + (if decide (body32 - i < 8) then body32 - i else (8 : UInt32))).toNat = body := by
          rw [uadd i _ r htake' (by omega), hi]; omega
        obtain ⟨m', hm'⟩ : ∃ m', fuel = m' + 1 := ⟨fuel - 1, by omega⟩
        rw [hm']
        unfold base32_decode.loop1
        have hc' : decide (i + (if decide (body32 - i < 8) then body32 - i else (8 : UInt32)) < body32) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hi', hbody]; omega
        rw [if_neg (by simpa using hc')]
        refine ⟨dst1, _, _, rfl, hsize1, ?_⟩
        intro k
        rw [hget1 k, hout, hq32]
        by_cases hin : 5 * g ≤ k ∧ k < decSize32 body
        · rw [if_pos ⟨by omega, by omega⟩, if_pos hin, show k / 5 = g by omega, show k - 5 * g = k % 5 by omega]
        · rw [if_neg hin, if_neg]
          intro ⟨hk1, hk2⟩; apply hin; exact ⟨by omega, by omega⟩
      · -- a full group: five bytes, then the rest
        have htake' : (if decide (body32 - i < 8) then body32 - i else (8 : UInt32)).toNat = 8 := by rw [htake]; omega
        have heq8 : ((if decide (body32 - i < 8) then body32 - i else (8 : UInt32)) == 8) = true := by
          rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [htake']; rfl
        rw [heq8]
        simp only [↓reduceIte, Option.bind_some]
        have hg1 : 5 * (g + 1) ≤ decSize32 body := by rw [hds]; omega
        obtain ⟨dst1, hloop3, hsize1, hget1⟩ := dec_loop3_spec out (decWord32 src hex body g) 5 fuel dst 0 (by decide) (by decide)
          hout5 (by show out.toNat + 5 ≤ dst.size; omega) (by show 5 - 0 < fuel; omega)
        rw [show (0 : UInt32) = (0 : Nat).toUInt32 from rfl, hloop3]
        simp only [Option.bind_some]
        have hi' : (i + (if decide (body32 - i < 8) then body32 - i else (8 : UInt32))).toNat = 8 * (g + 1) := by
          rw [uadd i _ 8 htake' (by omega), hi]; omega
        have hout' : (out + 5).toNat = 5 * (g + 1) := by rw [uadd out 5 5 (by decide) (by omega), hout]; omega
        obtain ⟨dst', i', out', hrest, hsize', hget'⟩ := ih dst1 _ (out + 5) (g + 1) hi' hout' (by omega)
          (by rw [hsize1]; exact hroom) (by rw [hsize1]; exact hdst) (by omega)
        rw [hrest]
        refine ⟨dst', i', out', rfl, by rw [hsize', hsize1], ?_⟩
        intro k
        rw [hget' k, hget1 k, hout]
        simp only [Nat.add_zero]
        by_cases hin : 5 * (g + 1) ≤ k ∧ k < decSize32 body
        · rw [if_pos hin, if_pos ⟨by omega, hin.2⟩]
        · rw [if_neg hin]
          by_cases hk : 5 * g ≤ k ∧ k < 5 * g + (5 : UInt32).toNat
          · have hk2 : k < 5 * g + 5 := hk.2
            rw [if_pos hk, if_pos ⟨hk.1, by omega⟩, show k / 5 = g by omega, show k - 5 * g = k % 5 by omega]
          · rw [if_neg hk, if_neg]
            intro ⟨hk1, hk2⟩; apply hk; refine ⟨hk1, ?_⟩; show k < 5 * g + 5; omega
    · -- nothing remains
      have hc : decide (i < body32) = false := by apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hbody, hi]; omega
      rw [if_neg (by simpa using hc)]
      refine ⟨dst, i, out, rfl, rfl, ?_⟩
      intro k
      have hn5 : decSize32 body ≤ 5 * g := by
        rw [hds]
        rcases Nat.lt_or_ge (body / 8) g with h | h
        · omega
        · have hr0 : body % 8 = 0 := by omega
          rw [hr0]; show body / 8 * 5 + 0 ≤ 5 * g; omega
      rw [if_neg (by omega)]

/-- The decoder on a text the size pass accepted: the bytes of the words, group by group. -/
theorem b32_decode_of_size (src dst : Array UInt8) (hex : Bool) (fuel : Nat) (body : Nat) (hb8 : body + 8 < 2 ^ 32)
    (h1 : body % 8 ≠ 1) (h3 : body % 8 ≠ 3) (h6 : body % 8 ≠ 6)
    (hsz : base32_decoded_size src hex fuel = some (.Ok (decSize32 body).toUInt32))
    (hdst : decSize32 body ≤ dst.size) (hdst_small : dst.size < 2 ^ 32) (hf : body + 10 < fuel) :
    ∃ dst', base32_decode dst src hex fuel = some (.Ok (decSize32 body).toUInt32, dst') ∧ dst'.size = dst.size ∧
      ∀ k, k < decSize32 body → dst'.getD k 0 = byteAt (decWord32 src hex body (k / 5)) (k % 5).toUInt32 := by
  have hpb := pbytes32_lt (body % 8)
  have hpb' := pbytes32_le (body % 8)
  have hds : decSize32 body = body / 8 * 5 + pbytes32 (body % 8) := rfl
  have hn32 : ((decSize32 body).toUInt32).toNat = decSize32 body := toUInt32_toNat_of_lt _ (by omega)
  have hfits : decide ((decSize32 body).toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false; intro h; have := UInt32.lt_iff_toNat_lt.mp h
    rw [hn32, toUInt32_toNat_of_lt _ hdst_small] at this; omega
  have hmod : ((decSize32 body).toUInt32 % 5).toNat = pbytes32 (body % 8) := by
    rw [UInt32.toNat_mod, hn32, show (5 : UInt32).toNat = 5 by decide, hds]; omega
  have hdiv : ((decSize32 body).toUInt32 / 5).toNat = body / 8 := by
    rw [UInt32.toNat_div, hn32, show (5 : UInt32).toNat = 5 by decide, hds]; omega
  -- the symbol count the decoder recomputes from the size
  have hr4 : (if ((decSize32 body).toUInt32 % 5 == 0) then some (0 : UInt32)
      else base32_partial ((decSize32 body).toUInt32 % 5) fuel) = some (body % 8).toUInt32 := by
    by_cases h0 : body % 8 = 0
    · have hb : ((decSize32 body).toUInt32 % 5 == 0) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hmod, h0]; rfl
      rw [if_pos hb, h0]; rfl
    · have hpos : 1 ≤ pbytes32 (body % 8) := by
        have : body % 8 < 8 := Nat.mod_lt _ (by omega)
        unfold pbytes32; split <;> (try split) <;> (try split) <;> (try split) <;> omega
      have hb : ((decSize32 body).toUInt32 % 5 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hmod] at h'; simp at h'; omega
      rw [if_neg (by simpa using hb), base32_partial_eq _ (by rw [hmod]; exact hpos) (by rw [hmod]; exact hpb), hmod]
      have : partial32 (pbytes32 (body % 8)) = body % 8 := by
        rcases (show body % 8 = 2 ∨ body % 8 = 4 ∨ body % 8 = 5 ∨ body % 8 = 7 by omega) with h | h | h | h <;> rw [h] <;> rfl
      rw [this]
  have hbodyN : ((decSize32 body).toUInt32 / 5 * 8 + (body % 8).toUInt32).toNat = body := by
    rw [UInt32.toNat_add, UInt32.toNat_mul, hdiv, show (8 : UInt32).toNat = 8 by decide, toUInt32_toNat_of_lt _ (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  unfold base32_decode
  rw [hsz]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hfits, Bool.false_eq_true, ↓reduceIte]
  rw [hr4]
  simp only [Option.bind_some]
  obtain ⟨dst', i', out', hloop, hsize', hget⟩ := dec_loop1_gen src hex body hb8 h1 h3 h6 _ hbodyN fuel dst 0 0 0 (by simp) (by simp)
    (Nat.zero_le _) hdst hdst_small (by simp only [Nat.mul_zero, Nat.sub_zero]; omega)
  rw [hloop]
  simp only [Option.bind_some]
  exact ⟨dst', rfl, hsize', fun k hk => by rw [hget k, if_pos ⟨by omega, hk⟩]⟩

/-! ## The witness: the decoded bytes encode to the text, up to case -/

/-- The word the encoder would form from the decoded bytes of a full group. -/
def reW8 (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32) : UInt64 :=
  let w := mk8 v0.toUInt64 v1.toUInt64 v2.toUInt64 v3.toUInt64 v4.toUInt64 v5.toUInt64 v6.toUInt64 v7.toUInt64
  w40of (byteAt w 0) (byteAt w 1) (byteAt w 2) (byteAt w 3) (byteAt w 4)

theorem fld_reW8 (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32) (h0 : v0 < 32) (h1 : v1 < 32) (h2 : v2 < 32) (h3 : v3 < 32)
    (h4 : v4 < 32) (h5 : v5 < 32) (h6 : v6 < 32) (h7 : v7 < 32) :
    fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 0 = v0.toUInt64 ∧ fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 1 = v1.toUInt64 ∧
    fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 2 = v2.toUInt64 ∧ fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 3 = v3.toUInt64 ∧
    fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 4 = v4.toUInt64 ∧ fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 5 = v5.toUInt64 ∧
    fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 6 = v6.toUInt64 ∧ fld (reW8 v0 v1 v2 v3 v4 v5 v6 v7) 7 = v7.toUInt64 := by
  unfold reW8 fld w40of byteAt mk8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- Two symbols: one byte. -/
def reW2 (v0 v1 : UInt32) : UInt64 :=
  let w := mk8 v0.toUInt64 v1.toUInt64 0 0 0 0 0 0
  w40of (byteAt w 0) 0 0 0 0

theorem fld_reW2 (v0 v1 : UInt32) (h0 : v0 < 32) (h1 : v1 < 32) (hc : v1 &&& 3 = 0) :
    fld (reW2 v0 v1) 0 = v0.toUInt64 ∧ fld (reW2 v0 v1) 1 = v1.toUInt64 := by
  unfold reW2 fld w40of byteAt mk8
  refine ⟨?_, ?_⟩ <;> bv_decide

/-- Four symbols: two bytes. -/
def reW4 (v0 v1 v2 v3 : UInt32) : UInt64 :=
  let w := mk8 v0.toUInt64 v1.toUInt64 v2.toUInt64 v3.toUInt64 0 0 0 0
  w40of (byteAt w 0) (byteAt w 1) 0 0 0

theorem fld_reW4 (v0 v1 v2 v3 : UInt32) (h0 : v0 < 32) (h1 : v1 < 32) (h2 : v2 < 32) (h3 : v3 < 32) (hc : v3 &&& 15 = 0) :
    fld (reW4 v0 v1 v2 v3) 0 = v0.toUInt64 ∧ fld (reW4 v0 v1 v2 v3) 1 = v1.toUInt64 ∧
    fld (reW4 v0 v1 v2 v3) 2 = v2.toUInt64 ∧ fld (reW4 v0 v1 v2 v3) 3 = v3.toUInt64 := by
  unfold reW4 fld w40of byteAt mk8
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- Five symbols: three bytes. -/
def reW5 (v0 v1 v2 v3 v4 : UInt32) : UInt64 :=
  let w := mk8 v0.toUInt64 v1.toUInt64 v2.toUInt64 v3.toUInt64 v4.toUInt64 0 0 0
  w40of (byteAt w 0) (byteAt w 1) (byteAt w 2) 0 0

theorem fld_reW5 (v0 v1 v2 v3 v4 : UInt32) (h0 : v0 < 32) (h1 : v1 < 32) (h2 : v2 < 32) (h3 : v3 < 32) (h4 : v4 < 32)
    (hc : v4 &&& 1 = 0) :
    fld (reW5 v0 v1 v2 v3 v4) 0 = v0.toUInt64 ∧ fld (reW5 v0 v1 v2 v3 v4) 1 = v1.toUInt64 ∧
    fld (reW5 v0 v1 v2 v3 v4) 2 = v2.toUInt64 ∧ fld (reW5 v0 v1 v2 v3 v4) 3 = v3.toUInt64 ∧
    fld (reW5 v0 v1 v2 v3 v4) 4 = v4.toUInt64 := by
  unfold reW5 fld w40of byteAt mk8
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- Seven symbols: four bytes. -/
def reW7 (v0 v1 v2 v3 v4 v5 v6 : UInt32) : UInt64 :=
  let w := mk8 v0.toUInt64 v1.toUInt64 v2.toUInt64 v3.toUInt64 v4.toUInt64 v5.toUInt64 v6.toUInt64 0
  w40of (byteAt w 0) (byteAt w 1) (byteAt w 2) (byteAt w 3) 0

theorem fld_reW7 (v0 v1 v2 v3 v4 v5 v6 : UInt32) (h0 : v0 < 32) (h1 : v1 < 32) (h2 : v2 < 32) (h3 : v3 < 32) (h4 : v4 < 32)
    (h5 : v5 < 32) (h6 : v6 < 32) (hc : v6 &&& 7 = 0) :
    fld (reW7 v0 v1 v2 v3 v4 v5 v6) 0 = v0.toUInt64 ∧ fld (reW7 v0 v1 v2 v3 v4 v5 v6) 1 = v1.toUInt64 ∧
    fld (reW7 v0 v1 v2 v3 v4 v5 v6) 2 = v2.toUInt64 ∧ fld (reW7 v0 v1 v2 v3 v4 v5 v6) 3 = v3.toUInt64 ∧
    fld (reW7 v0 v1 v2 v3 v4 v5 v6) 4 = v4.toUInt64 ∧ fld (reW7 v0 v1 v2 v3 v4 v5 v6) 5 = v5.toUInt64 ∧
    fld (reW7 v0 v1 v2 v3 v4 v5 v6) 6 = v6.toUInt64 := by
  unfold reW7 fld w40of byteAt mk8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- The decoded bytes are a source whose encoding is the text, letters uppercased. -/
theorem encoded_of_decoded32 (src dst' : Array UInt8) (hex : Bool) (pads : Nat) (hp6 : pads ≤ 6) (htp : TrailingPads src pads)
    (hbad : pads = 0 ∨ (src.size % 8 = 0 ∧ (src.size - pads) % 8 ≠ 0 ∧ pads = 8 - (src.size - pads) % 8))
    (h1 : (src.size - pads) % 8 ≠ 1) (h3 : (src.size - pads) % 8 ≠ 3) (h6 : (src.size - pads) % 8 ≠ 6)
    (hall : ∀ k, k < src.size - pads → (val32 hex (src.getD k 0)).toNat < 32)
    (hc2 : (src.size - pads) % 8 = 2 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 3) = 0)
    (hc4 : (src.size - pads) % 8 = 4 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 15) = 0)
    (hc5 : (src.size - pads) % 8 = 5 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 1) = 0)
    (hc7 : (src.size - pads) % 8 = 7 → (val32 hex (src.getD (src.size - pads - 1) 0) &&& 7) = 0)
    (hn : decSize32 (src.size - pads) ≤ dst'.size)
    (hbytes : ∀ k, k < decSize32 (src.size - pads) →
      dst'.getD k 0 = byteAt (decWord32 src hex (src.size - pads) (k / 5)) (k % 5).toUInt32) :
    ∃ pad, Encoded32 (dst'.extract 0 (decSize32 (src.size - pads))) (src.map upper32) hex pad := by
  obtain ⟨body, hbody⟩ : ∃ body, body = src.size - pads := ⟨_, rfl⟩
  rw [← hbody] at hbad h1 h3 h6 hall hc2 hc4 hc5 hc7 hn hbytes ⊢
  have hpb := pbytes32_lt (body % 8)
  have hpb' := pbytes32_le (body % 8)
  have hds : decSize32 body = body / 8 * 5 + pbytes32 (body % 8) := rfl
  obtain ⟨n, hn_def⟩ : ∃ n, n = decSize32 body := ⟨_, rfl⟩
  rw [← hn_def] at hn hbytes ⊢
  have hsize_ex : (dst'.extract 0 n).size = n := by rw [Array.size_extract]; omega
  have hsrc_size : (src.map upper32).size = src.size := Array.size_map
  have hv : ∀ k, k < body → val32 hex (src.getD k 0) < (32 : UInt32) := fun k hk => by
    rw [UInt32.lt_iff_toNat_lt]; simpa using hall k hk
  have hb : ∀ k, (dst'.extract 0 n).getD k 0 = if k < n then byteAt (decWord32 src hex body (k / 5)) (k % 5).toUInt32 else 0 := by
    intro k; rw [extract_getD _ _ _ hn]
    by_cases hk : k < n
    · rw [if_pos hk, if_pos hk]; exact hbytes k hk
    · rw [if_neg hk, if_neg hk]
  have hG : n / 5 = body / 8 := by rw [hn_def, hds]; omega
  have hR : n % 5 = pbytes32 (body % 8) := by rw [hn_def, hds]; omega
  have hcount : symCount32 n = body := by
    rw [symCount32_eq, hG, hR]
    rcases (show body % 8 = 0 ∨ body % 8 = 2 ∨ body % 8 = 4 ∨ body % 8 = 5 ∨ body % 8 = 7 by omega) with h | h | h | h | h <;> rw [h]
    · rw [show pbytes32 0 = 0 from rfl, if_pos rfl]; omega
    · rw [show pbytes32 2 = 1 from rfl, if_neg (by omega)]; show 8 * (body / 8) + 2 = body; omega
    · rw [show pbytes32 4 = 2 from rfl, if_neg (by omega)]; show 8 * (body / 8) + 4 = body; omega
    · rw [show pbytes32 5 = 3 from rfl, if_neg (by omega)]; show 8 * (body / 8) + 5 = body; omega
    · rw [show pbytes32 7 = 4 from rfl, if_neg (by omega)]; show 8 * (body / 8) + 7 = body; omega
  -- every symbol reads back from the decoded bytes, up to case
  have hsyms : ∀ k, k < body → (src.map upper32).getD k 0 = encSym32 (dst'.extract 0 n) hex k := by
    intro k hk
    rw [map_upper_getD]
    unfold encSym32
    obtain ⟨g, hg⟩ : ∃ g, g = k / 8 := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s, s = k % 8 := ⟨_, rfl⟩
    have hks : k = 8 * g + s := by omega
    have hs8 : s < 8 := by omega
    rw [← hg, ← hs]
    have hw40 : w40 (dst'.extract 0 n) g = w40of ((dst'.extract 0 n).getD (5 * g) 0) ((dst'.extract 0 n).getD (5 * g + 1) 0)
        ((dst'.extract 0 n).getD (5 * g + 2) 0) ((dst'.extract 0 n).getD (5 * g + 3) 0) ((dst'.extract 0 n).getD (5 * g + 4) 0) := rfl
    have hbt0 : (dst'.extract 0 n).getD (5 * g) 0 = if 5 * g < n then byteAt (decWord32 src hex body g) 0 else 0 := by
      rw [hb, show 5 * g / 5 = g by omega, show 5 * g % 5 = 0 by omega]; rfl
    have hbt : ∀ t, t < 5 → (dst'.extract 0 n).getD (5 * g + t) 0 =
        if 5 * g + t < n then byteAt (decWord32 src hex body g) t.toUInt32 else 0 := by
      intro t ht; rw [hb, show (5 * g + t) / 5 = g by omega, show (5 * g + t) % 5 = t by omega]
    have hfld : (fld (w40 (dst'.extract 0 n) g) s.toUInt32).toUInt32 = val32 hex (src.getD (8 * g + s) 0) := by
      rcases Nat.lt_or_ge (8 * g + 7) body with hfull | hpart
      · -- a full group
        have hn5 : 5 * g + 5 ≤ n := by rw [hn_def, hds]; omega
        have hw : decWord32 src hex body g = mk8 (val32 hex (src.getD (8 * g) 0)).toUInt64 (val32 hex (src.getD (8 * g + 1) 0)).toUInt64
            (val32 hex (src.getD (8 * g + 2) 0)).toUInt64 (val32 hex (src.getD (8 * g + 3) 0)).toUInt64
            (val32 hex (src.getD (8 * g + 4) 0)).toUInt64 (val32 hex (src.getD (8 * g + 5) 0)).toUInt64
            (val32 hex (src.getD (8 * g + 6) 0)).toUInt64 (val32 hex (src.getD (8 * g + 7) 0)).toUInt64 := by
          unfold decWord32 dvb
          rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
            if_pos (by omega), if_pos (by omega)]
          rfl
        rw [hw40, hbt0, hbt 1 (by omega), hbt 2 (by omega), hbt 3 (by omega), hbt 4 (by omega), if_pos (by omega), if_pos (by omega),
          if_pos (by omega), if_pos (by omega), if_pos (by omega), hw]
        have hf := fld_reW8 _ _ _ _ _ _ _ _ (hv (8 * g) (by omega)) (hv (8 * g + 1) (by omega)) (hv (8 * g + 2) (by omega))
          (hv (8 * g + 3) (by omega)) (hv (8 * g + 4) (by omega)) (hv (8 * g + 5) (by omega)) (hv (8 * g + 6) (by omega))
          (hv (8 * g + 7) (by omega))
        change (fld (reW8 (val32 hex (src.getD (8 * g) 0)) (val32 hex (src.getD (8 * g + 1) 0)) (val32 hex (src.getD (8 * g + 2) 0))
          (val32 hex (src.getD (8 * g + 3) 0)) (val32 hex (src.getD (8 * g + 4) 0)) (val32 hex (src.getD (8 * g + 5) 0))
          (val32 hex (src.getD (8 * g + 6) 0)) (val32 hex (src.getD (8 * g + 7) 0))) s.toUInt32).toUInt32 = _
        rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 by omega) with h | h | h | h | h | h | h | h <;> subst h
        · show (fld _ (0 : UInt32)).toUInt32 = val32 hex (src.getD (8 * g) 0); rw [hf.1, UInt32.toUInt32_toUInt64]
        · show (fld _ (1 : UInt32)).toUInt32 = _; rw [hf.2.1, UInt32.toUInt32_toUInt64]
        · show (fld _ (2 : UInt32)).toUInt32 = _; rw [hf.2.2.1, UInt32.toUInt32_toUInt64]
        · show (fld _ (3 : UInt32)).toUInt32 = _; rw [hf.2.2.2.1, UInt32.toUInt32_toUInt64]
        · show (fld _ (4 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2.1, UInt32.toUInt32_toUInt64]
        · show (fld _ (5 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2.2.1, UInt32.toUInt32_toUInt64]
        · show (fld _ (6 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2.2.2.1, UInt32.toUInt32_toUInt64]
        · show (fld _ (7 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2.2.2.2, UInt32.toUInt32_toUInt64]
      · -- the partial final group
        have hgq : g = body / 8 := by omega
        have hr : body % 8 = body - 8 * g := by omega
        rcases (show body - 8 * g = 2 ∨ body - 8 * g = 4 ∨ body - 8 * g = 5 ∨ body - 8 * g = 7 by omega) with h | h | h | h
        · have hnv : n = 5 * g + 1 := by rw [hn_def, hds, ← hgq, hr, h]; show g * 5 + 1 = 5 * g + 1; omega
          have hw : decWord32 src hex body g = mk8 (val32 hex (src.getD (8 * g) 0)).toUInt64 (val32 hex (src.getD (8 * g + 1) 0)).toUInt64
              0 0 0 0 0 0 := by
            unfold decWord32 dvb
            rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega)]
            rfl
          rw [hw40, hbt0, hbt 1 (by omega), hbt 2 (by omega), hbt 3 (by omega), hbt 4 (by omega), if_pos (by omega),
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hw]
          have hf := fld_reW2 _ _ (hv (8 * g) (by omega)) (hv (8 * g + 1) (by omega))
            (by have := hc2 (by omega); rwa [show body - 1 = 8 * g + 1 by omega] at this)
          change (fld (reW2 (val32 hex (src.getD (8 * g) 0)) (val32 hex (src.getD (8 * g + 1) 0))) s.toUInt32).toUInt32 = _
          rcases (show s = 0 ∨ s = 1 by omega) with h' | h' <;> subst h'
          · show (fld _ (0 : UInt32)).toUInt32 = val32 hex (src.getD (8 * g) 0); rw [hf.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (1 : UInt32)).toUInt32 = _; rw [hf.2, UInt32.toUInt32_toUInt64]
        · have hnv : n = 5 * g + 2 := by rw [hn_def, hds, ← hgq, hr, h]; show g * 5 + 2 = 5 * g + 2; omega
          have hw : decWord32 src hex body g = mk8 (val32 hex (src.getD (8 * g) 0)).toUInt64 (val32 hex (src.getD (8 * g + 1) 0)).toUInt64
              (val32 hex (src.getD (8 * g + 2) 0)).toUInt64 (val32 hex (src.getD (8 * g + 3) 0)).toUInt64 0 0 0 0 := by
            unfold decWord32 dvb
            rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega)]
            rfl
          rw [hw40, hbt0, hbt 1 (by omega), hbt 2 (by omega), hbt 3 (by omega), hbt 4 (by omega), if_pos (by omega),
            if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hw]
          have hf := fld_reW4 _ _ _ _ (hv (8 * g) (by omega)) (hv (8 * g + 1) (by omega)) (hv (8 * g + 2) (by omega))
            (hv (8 * g + 3) (by omega)) (by have := hc4 (by omega); rwa [show body - 1 = 8 * g + 3 by omega] at this)
          change (fld (reW4 (val32 hex (src.getD (8 * g) 0)) (val32 hex (src.getD (8 * g + 1) 0)) (val32 hex (src.getD (8 * g + 2) 0))
            (val32 hex (src.getD (8 * g + 3) 0))) s.toUInt32).toUInt32 = _
          rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 by omega) with h' | h' | h' | h' <;> subst h'
          · show (fld _ (0 : UInt32)).toUInt32 = val32 hex (src.getD (8 * g) 0); rw [hf.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (1 : UInt32)).toUInt32 = _; rw [hf.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (2 : UInt32)).toUInt32 = _; rw [hf.2.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (3 : UInt32)).toUInt32 = _; rw [hf.2.2.2, UInt32.toUInt32_toUInt64]
        · have hnv : n = 5 * g + 3 := by rw [hn_def, hds, ← hgq, hr, h]; show g * 5 + 3 = 5 * g + 3; omega
          have hw : decWord32 src hex body g = mk8 (val32 hex (src.getD (8 * g) 0)).toUInt64 (val32 hex (src.getD (8 * g + 1) 0)).toUInt64
              (val32 hex (src.getD (8 * g + 2) 0)).toUInt64 (val32 hex (src.getD (8 * g + 3) 0)).toUInt64
              (val32 hex (src.getD (8 * g + 4) 0)).toUInt64 0 0 0 := by
            unfold decWord32 dvb
            rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega)]
            rfl
          rw [hw40, hbt0, hbt 1 (by omega), hbt 2 (by omega), hbt 3 (by omega), hbt 4 (by omega), if_pos (by omega),
            if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), hw]
          have hf := fld_reW5 _ _ _ _ _ (hv (8 * g) (by omega)) (hv (8 * g + 1) (by omega)) (hv (8 * g + 2) (by omega))
            (hv (8 * g + 3) (by omega)) (hv (8 * g + 4) (by omega))
            (by have := hc5 (by omega); rwa [show body - 1 = 8 * g + 4 by omega] at this)
          change (fld (reW5 (val32 hex (src.getD (8 * g) 0)) (val32 hex (src.getD (8 * g + 1) 0)) (val32 hex (src.getD (8 * g + 2) 0))
            (val32 hex (src.getD (8 * g + 3) 0)) (val32 hex (src.getD (8 * g + 4) 0))) s.toUInt32).toUInt32 = _
          rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 by omega) with h' | h' | h' | h' | h' <;> subst h'
          · show (fld _ (0 : UInt32)).toUInt32 = val32 hex (src.getD (8 * g) 0); rw [hf.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (1 : UInt32)).toUInt32 = _; rw [hf.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (2 : UInt32)).toUInt32 = _; rw [hf.2.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (3 : UInt32)).toUInt32 = _; rw [hf.2.2.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (4 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2, UInt32.toUInt32_toUInt64]
        · have hnv : n = 5 * g + 4 := by rw [hn_def, hds, ← hgq, hr, h]; show g * 5 + 4 = 5 * g + 4; omega
          have hw : decWord32 src hex body g = mk8 (val32 hex (src.getD (8 * g) 0)).toUInt64 (val32 hex (src.getD (8 * g + 1) 0)).toUInt64
              (val32 hex (src.getD (8 * g + 2) 0)).toUInt64 (val32 hex (src.getD (8 * g + 3) 0)).toUInt64
              (val32 hex (src.getD (8 * g + 4) 0)).toUInt64 (val32 hex (src.getD (8 * g + 5) 0)).toUInt64
              (val32 hex (src.getD (8 * g + 6) 0)).toUInt64 0 := by
            unfold decWord32 dvb
            rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
              if_pos (by omega), if_neg (by omega)]
            rfl
          rw [hw40, hbt0, hbt 1 (by omega), hbt 2 (by omega), hbt 3 (by omega), hbt 4 (by omega), if_pos (by omega),
            if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), hw]
          have hf := fld_reW7 _ _ _ _ _ _ _ (hv (8 * g) (by omega)) (hv (8 * g + 1) (by omega)) (hv (8 * g + 2) (by omega))
            (hv (8 * g + 3) (by omega)) (hv (8 * g + 4) (by omega)) (hv (8 * g + 5) (by omega)) (hv (8 * g + 6) (by omega))
            (by have := hc7 (by omega); rwa [show body - 1 = 8 * g + 6 by omega] at this)
          change (fld (reW7 (val32 hex (src.getD (8 * g) 0)) (val32 hex (src.getD (8 * g + 1) 0)) (val32 hex (src.getD (8 * g + 2) 0))
            (val32 hex (src.getD (8 * g + 3) 0)) (val32 hex (src.getD (8 * g + 4) 0)) (val32 hex (src.getD (8 * g + 5) 0))
            (val32 hex (src.getD (8 * g + 6) 0))) s.toUInt32).toUInt32 = _
          rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 by omega) with h' | h' | h' | h' | h' | h' | h' <;> subst h'
          · show (fld _ (0 : UInt32)).toUInt32 = val32 hex (src.getD (8 * g) 0); rw [hf.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (1 : UInt32)).toUInt32 = _; rw [hf.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (2 : UInt32)).toUInt32 = _; rw [hf.2.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (3 : UInt32)).toUInt32 = _; rw [hf.2.2.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (4 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (5 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2.2.1, UInt32.toUInt32_toUInt64]
          · show (fld _ (6 : UInt32)).toUInt32 = _; rw [hf.2.2.2.2.2.2, UInt32.toUInt32_toUInt64]
    rw [hfld, ← hks, symbol_val32 _ _ (hall k hk)]
  -- the padding choice
  by_cases hp0 : pads = 0
  · have hsz : src.size = body := by omega
    have hE : encSize32 n false = symCount32 n := by
      rw [encSize32_eq, symCount32_eq]
      by_cases h : n % 5 = 0
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, if_neg Bool.false_ne_true]
    refine ⟨false, ?_, ?_, ?_⟩
    · rw [hsize_ex, hE, hcount, hsrc_size, hsz]
    · intro k hk; rw [hsize_ex, hcount] at hk; exact hsyms k hk
    · intro k hk1 hk2; rw [hsize_ex] at hk1 hk2; rw [hE] at hk2; exact absurd hk2 (Nat.not_lt.mpr hk1)
  · have hp4 : src.size % 8 = 0 ∧ body % 8 ≠ 0 ∧ pads = 8 - body % 8 := by
      rcases hbad with h | h; exact absurd h hp0; exact h
    have hsz : src.size = 8 * (body / 8) + 8 := by omega
    have hR0 : n % 5 ≠ 0 := by
      rw [hR]; intro h
      have : body % 8 < 8 := Nat.mod_lt _ (by omega)
      unfold pbytes32 at h; split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> omega
    have hE : encSize32 n true = 8 * (body / 8) + 8 := by rw [encSize32_eq, hG, if_neg hR0, if_pos rfl]
    refine ⟨true, ?_, ?_, ?_⟩
    · rw [hsize_ex, hE, hsrc_size, hsz]
    · intro k hk; rw [hsize_ex, hcount] at hk; exact hsyms k hk
    · intro k hk1 hk2
      rw [hsize_ex, hcount] at hk1
      rw [hsize_ex, hE] at hk2
      rw [map_upper_getD]
      have := htp.2 (src.size - 1 - k) (by omega)
      rw [show src.size - 1 - (src.size - 1 - k) = k by omega] at this
      rw [this]; rfl

/-! ## Strictness -/

/-- What `base32_decode` accepts is an encoding up to letter case: the bytes it
wrote (the first `n` of the destination) are a source whose encoding —
padded iff the text carries padding — is the text with its letters uppercased. -/
theorem base32_decode_strict (src dst : Array UInt8) (hex : Bool) (fuel : Nat) (n : UInt32) (dst' : Array UInt8)
    (hsize : src.size + 8 < 2 ^ 32) (hdst_small : dst.size < 2 ^ 32) (hf : src.size + 10 < fuel)
    (h : base32_decode dst src hex fuel = some (.Ok n, dst')) :
    n.toNat ≤ dst.size ∧ dst'.size = dst.size ∧ ∃ pad, Encoded32 (dst'.extract 0 n.toNat) (src.map upper32) hex pad := by
  rcases decoded_size_gen32 src hex fuel hsize (by omega) with ⟨reason, herr⟩ | ⟨pads, hp6, htp, hbad, h1, h3, h6, hall, hc2, hc4, hc5, hc7, hok⟩
  · have : base32_decode dst src hex fuel = some (.Err reason, dst) := by unfold base32_decode; rw [herr]; rfl
    rw [this] at h; simp at h
  · have hpb' := pbytes32_le ((src.size - pads) % 8)
    have hle : decSize32 (src.size - pads) ≤ src.size - pads := by unfold decSize32; omega
    have hn32 : ((decSize32 (src.size - pads)).toUInt32).toNat = decSize32 (src.size - pads) := toUInt32_toNat_of_lt _ (by omega)
    by_cases hfit : decSize32 (src.size - pads) ≤ dst.size
    · obtain ⟨dst'', hdec, hsize', hbytes⟩ :=
        b32_decode_of_size src dst hex fuel (src.size - pads) (by omega) h1 h3 h6 hok hfit hdst_small (by omega)
      rw [hdec] at h
      simp only [Option.some.injEq, Prod.mk.injEq, Result_u32_EncodingError.Ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hn32]
      exact ⟨hfit, hsize', encoded_of_decoded32 src dst'' hex pads hp6 htp hbad h1 h3 h6 hall hc2 hc4 hc5 hc7
        (by rw [hsize']; exact hfit) hbytes⟩
    · have hfits : decide ((decSize32 (src.size - pads)).toUInt32 > dst.size.toUInt32) = true := by
        apply decide_eq_true; rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hn32, toUInt32_toNat_of_lt _ hdst_small]; omega
      have : base32_decode dst src hex fuel = some (.Err .DestinationTooSmall, dst) := by
        unfold base32_decode; rw [hok]
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hfits, ↓reduceIte]
      rw [this] at h; simp at h

/-- An encoding up to case reads, to the decoder, as the encoding itself. -/
theorem Encoded32V_of_upper {b src : Array UInt8} {hex pad : Bool} (he : Encoded32 b (src.map upper32) hex pad) :
    Encoded32V b src hex pad := by
  have hsz : (src.map upper32).size = src.size := Array.size_map
  refine ⟨by rw [← hsz]; exact he.size, ?_, ?_, ?_⟩
  · intro k hk
    have := he.syms k hk
    rw [map_upper_getD] at this
    rw [← val32_upper, this, val32_encSym32]
  · intro k hk
    have := he.syms k hk
    rw [map_upper_getD] at this
    intro h; apply encSym32_ne_pad b hex k
    rw [← this, h]; rfl
  · intro k hk1 hk2
    have := he.pads k hk1 hk2
    rw [map_upper_getD] at this
    exact (upper32_pad_iff _).mp this

/-- Strictness: `base32_decode` succeeds iff the text, letters uppercased, is an
encoding (of a source the destination holds), for a text of fewer than
`2^32 - 8` bytes and enough fuel. -/
theorem base32_decode_ok_iff (src dst : Array UInt8) (hex : Bool) (fuel : Nat)
    (hsize : src.size + 8 < 2 ^ 32) (hdst_small : dst.size < 2 ^ 32) (hf : 2 * src.size + 16 < fuel) :
    (∃ n dst', base32_decode dst src hex fuel = some (.Ok n, dst')) ↔
      ∃ b pad, Encoded32 b (src.map upper32) hex pad ∧ b.size ≤ dst.size := by
  constructor
  · intro ⟨n, dst', h⟩
    obtain ⟨hn, hsize', pad, he⟩ := base32_decode_strict src dst hex fuel n dst' hsize hdst_small (by omega) h
    refine ⟨_, pad, he, ?_⟩
    rw [Array.size_extract]; omega
  · intro ⟨b, pad, he, hb⟩
    have hbsize : 8 * (b.size / 5) ≤ src.size := by
      have := he.size; rw [Array.size_map] at this; rw [encSize32_eq] at this; omega
    have hb' : b.size ≤ 2684354555 := by omega
    have hbs : b.size ≤ src.size := by
      have hs := he.size; rw [Array.size_map] at hs; unfold encSize32 at hs
      have hp := partial32_lt (b.size % 5)
      have hp2 : b.size % 5 ≤ partial32 (b.size % 5) := by
        have := Nat.mod_lt b.size (by decide : 0 < 5)
        unfold partial32; split <;> (try split) <;> (try split) <;> omega
      split at hs <;> (try split at hs) <;> omega
    obtain ⟨dst', h, -, -⟩ := base32_decode_encoded b src dst hex pad fuel (Encoded32V_of_upper he) hb' hb hdst_small (by omega)
    exact ⟨_, dst', h⟩

end Oak.Stdlib.Encoding
