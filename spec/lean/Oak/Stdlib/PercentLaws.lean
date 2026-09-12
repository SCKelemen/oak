import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.EncodingLaws
import Oak.Stdlib.Base64Laws

/-!
# Oak.Stdlib.PercentLaws — the percent-encoding round trip on the extracted `encoding` package

`percent_decode dst (percent_encode src keep) plus = src` for every source
below the size limit and every keep set that holds neither `%` nor, when
`+` decodes as a space, `+`. The proof follows the extraction: the encoder
keeps a byte that is unreserved or in the keep set and spells every other
byte as `%` and two upper-case hexadecimal digits; the decoder's size scan
accepts each spelled byte (two digits below sixteen, three bytes available)
and its loop reads them back through the hexadecimal table. Both loops are
handled by fuel induction over the encoded text as a list of per-byte
blocks (`encFrom`).
-/

namespace Oak.Stdlib.Encoding

set_option maxRecDepth 65536

/-! ## Facts about the tables and single bytes, decided in the kernel -/

/-- The upper-case digit of a nibble. -/
def hexUpper (v : UInt8) : UInt8 := HEX_UPPER_SYMBOLS.getD ((v &&& 15).toUInt32).toNat 0

theorem hex_digit_upper (v : UInt8) (fuel : Nat) : hex_digit v true fuel = some (hexUpper v) := rfl

theorem hex_value_def (b : UInt8) (fuel : Nat) : hex_value b fuel = some ((HEX_VALUES.getD (b.toUInt32).toNat 0).toUInt32) := rfl

theorem upper_digits_lt : ∀ b : Fin 256,
    (HEX_VALUES.getD ((hexUpper (b.val.toUInt8 >>> 4)).toUInt32).toNat 0).toUInt32 < 16 ∧
    (HEX_VALUES.getD ((hexUpper (b.val.toUInt8 &&& 15)).toUInt32).toNat 0).toUInt32 < 16 := by
  decide +kernel

theorem upper_digits_join : ∀ b : Fin 256,
    (((HEX_VALUES.getD ((hexUpper (b.val.toUInt8 >>> 4)).toUInt32).toNat 0).toUInt32 <<< 4) |||
      (HEX_VALUES.getD ((hexUpper (b.val.toUInt8 &&& 15)).toUInt32).toNat 0).toUInt32).toUInt8 = b.val.toUInt8 := by
  decide +kernel

theorem upper_digits_lt' (b : UInt8) :
    (HEX_VALUES.getD ((hexUpper (b >>> 4)).toUInt32).toNat 0).toUInt32 < 16 ∧
    (HEX_VALUES.getD ((hexUpper (b &&& 15)).toUInt32).toNat 0).toUInt32 < 16 := by
  have := upper_digits_lt ⟨b.toNat, UInt8.toNat_lt b⟩
  rwa [toUInt8_toNat] at this

theorem upper_digits_join' (b : UInt8) :
    (((HEX_VALUES.getD ((hexUpper (b >>> 4)).toUInt32).toNat 0).toUInt32 <<< 4) |||
      (HEX_VALUES.getD ((hexUpper (b &&& 15)).toUInt32).toNat 0).toUInt32).toUInt8 = b := by
  have := upper_digits_join ⟨b.toNat, UInt8.toNat_lt b⟩
  rwa [toUInt8_toNat] at this

/-- `getD` past a prefix of an append. -/
theorem getD_append_right_of_le (l m : List UInt8) (n : Nat) (h : l.length ≤ n) :
    (l ++ m).getD n 0 = m.getD (n - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- `getD` inside the prefix of an append. -/
theorem getD_append_left_of_lt (l m : List UInt8) (n : Nat) (h : n < l.length) :
    (l ++ m).getD n 0 = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-! ## The keep test -/

/-- `percent_unreserved` as a Boolean on the byte (RFC 3986 unreserved set). -/
def unres (b : UInt8) : Bool :=
  (((((((decide (b ≥ 65)) && (decide (b ≤ 90))) || ((decide (b ≥ 97)) && (decide (b ≤ 122)))) ||
    ((decide (b ≥ 48)) && (decide (b ≤ 57)))) || (b == 45)) || (b == 46)) || (b == 95)) || (b == 126)

theorem unreserved_spec (b : UInt8) (fuel : Nat) : percent_unreserved b fuel = some (unres b) := rfl

theorem unres_percent : unres 37 = false := by decide
theorem unres_plus : unres 43 = false := by decide

/-- Whether some byte of `keep` at or after index `j` is `b`. -/
def anyFrom (keep : Array UInt8) (b : UInt8) (j : Nat) : Bool :=
  if h : j < keep.size then (keep.getD j 0 == b) || anyFrom keep b (j + 1) else false
termination_by keep.size - j

theorem anyFrom_of_ge (keep : Array UInt8) (b : UInt8) (j : Nat) (h : keep.size ≤ j) : anyFrom keep b j = false := by
  rw [anyFrom, dif_neg (by omega)]

theorem anyFrom_of_lt (keep : Array UInt8) (b : UInt8) (j : Nat) (h : j < keep.size) :
    anyFrom keep b j = ((keep.getD j 0 == b) || anyFrom keep b (j + 1)) := by
  rw [anyFrom, dif_pos h]

theorem anyFrom_true_aux (keep : Array UInt8) (b : UInt8) :
    ∀ n j, keep.size - j = n → anyFrom keep b j = true → ∃ t, j ≤ t ∧ t < keep.size ∧ keep.getD t 0 = b := by
  intro n
  induction n with
  | zero =>
    intro j hn h
    rw [anyFrom_of_ge keep b j (by omega)] at h; simp at h
  | succ n ih =>
    intro j hn h
    have hj : j < keep.size := by omega
    rw [anyFrom_of_lt keep b j hj, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨j, Nat.le_refl _, hj, h⟩
    · obtain ⟨t, ht1, ht2, ht3⟩ := ih (j + 1) (by omega) h
      exact ⟨t, by omega, ht2, ht3⟩

theorem anyFrom_true (keep : Array UInt8) (b : UInt8) (j : Nat) (h : anyFrom keep b j = true) :
    ∃ t, j ≤ t ∧ t < keep.size ∧ keep.getD t 0 = b :=
  anyFrom_true_aux keep b (keep.size - j) j rfl h

/-- The byte is written as itself. -/
def keptB (keep : Array UInt8) (b : UInt8) : Bool := unres b || anyFrom keep b 0

theorem kept_loop (unit : UInt8) (keep : Array UInt8) (hkeep : keep.size + 1 < 2 ^ 32) (fuel : Nat) :
    ∀ (found : Bool) (i : UInt32), i.toNat ≤ keep.size → keep.size - i.toNat < fuel →
      ∃ i', percent_kept.loop1 unit keep found i fuel = some ((found || anyFrom keep unit i.toNat), i') := by
  induction fuel with
  | zero => intro _ _ _ hf; omega
  | succ fuel ih =>
    intro found i hi hf
    unfold percent_kept.loop1
    have hsz : (keep.size.toUInt32).toNat = keep.size := toUInt32_toNat_of_lt _ (by omega)
    cases found with
    | true =>
      rw [Bool.not_true, Bool.and_false, if_neg Bool.false_ne_true, Bool.true_or]
      exact ⟨i, rfl⟩
    | false =>
      rw [Bool.not_false, Bool.and_true, Bool.false_or]
      by_cases hlt : i.toNat < keep.size
      · have hc : decide (i < keep.size.toUInt32) = true := by
          apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz]; exact hlt
        rw [hc, if_pos rfl]
        have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
        obtain ⟨i', h⟩ := ih (keep.getD i.toNat 0 == unit) (i + 1) (by omega) (by omega)
        refine ⟨i', ?_⟩
        rw [h, hi1, anyFrom_of_lt keep unit i.toNat hlt]
      · have hc : decide (i < keep.size.toUInt32) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz]; exact hlt
        rw [hc, if_neg Bool.false_ne_true, anyFrom_of_ge keep unit i.toNat (by omega)]
        exact ⟨i, rfl⟩

theorem kept_spec (unit : UInt8) (keep : Array UInt8) (hkeep : keep.size + 1 < 2 ^ 32) (fuel : Nat)
    (hf : keep.size < fuel) : percent_kept unit keep fuel = some (keptB keep unit) := by
  unfold percent_kept
  obtain ⟨i', h⟩ := kept_loop unit keep hkeep fuel (unres unit) 0 (by simp) (by simp; omega)
  simp only [unreserved_spec, Option.pure_def, Option.bind_eq_bind, Option.bind_some, h]
  rfl

theorem kept_ne_percent (keep : Array UInt8) (hkeep : ∀ t, t < keep.size → keep.getD t 0 ≠ 37) (b : UInt8)
    (h : keptB keep b = true) : b ≠ 37 := by
  intro hb
  subst hb
  unfold keptB at h
  rw [unres_percent, Bool.false_or] at h
  obtain ⟨t, _, ht, heq⟩ := anyFrom_true keep 37 0 h
  exact hkeep t ht heq

theorem kept_ne_plus (keep : Array UInt8) (hkeep : ∀ t, t < keep.size → keep.getD t 0 ≠ 43) (b : UInt8)
    (h : keptB keep b = true) : b ≠ 43 := by
  intro hb
  subst hb
  unfold keptB at h
  rw [unres_plus, Bool.false_or] at h
  obtain ⟨t, _, ht, heq⟩ := anyFrom_true keep 43 0 h
  exact hkeep t ht heq

/-! ## The encoded text as blocks -/

/-- What the encoder writes for source byte `b`. -/
def block (keep : Array UInt8) (b : UInt8) : List UInt8 :=
  if keptB keep b then [b] else [37, hexUpper (b >>> 4), hexUpper (b &&& 15)]

theorem block_length (keep : Array UInt8) (b : UInt8) : (block keep b).length = if keptB keep b then 1 else 3 := by
  unfold block; split <;> rfl

theorem block_length_le (keep : Array UInt8) (b : UInt8) : (block keep b).length ≤ 3 := by
  rw [block_length]; split <;> omega

theorem block_length_pos (keep : Array UInt8) (b : UInt8) : 1 ≤ (block keep b).length := by
  rw [block_length]; split <;> omega

/-- The encoding of the source from index `j` on. -/
def encFrom (keep src : Array UInt8) (j : Nat) : List UInt8 :=
  if _h : j < src.size then block keep (src.getD j 0) ++ encFrom keep src (j + 1) else []
termination_by src.size - j

theorem encFrom_of_ge (keep src : Array UInt8) (j : Nat) (h : src.size ≤ j) : encFrom keep src j = [] := by
  rw [encFrom, dif_neg (by omega)]

theorem encFrom_of_lt (keep src : Array UInt8) (j : Nat) (h : j < src.size) :
    encFrom keep src j = block keep (src.getD j 0) ++ encFrom keep src (j + 1) := by
  rw [encFrom, dif_pos h]

theorem encFrom_length_le_aux (keep src : Array UInt8) :
    ∀ n j, src.size - j = n → (encFrom keep src j).length ≤ 3 * (src.size - j) := by
  intro n
  induction n with
  | zero => intro j hn; rw [encFrom_of_ge keep src j (by omega)]; simp
  | succ n ih =>
    intro j hn
    have hj : j < src.size := by omega
    rw [encFrom_of_lt keep src j hj, List.length_append]
    have := ih (j + 1) (by omega)
    have := block_length_le keep (src.getD j 0)
    omega

theorem encFrom_length_le (keep src : Array UInt8) (j : Nat) : (encFrom keep src j).length ≤ 3 * (src.size - j) :=
  encFrom_length_le_aux keep src (src.size - j) j rfl

/-! ## The size scan -/

theorem encoded_size_loop (keep src : Array UInt8) (hkeep : keep.size + 1 < 2 ^ 32) (hsrc : 3 * src.size < 2 ^ 32)
    (fuel : Nat) :
    ∀ (total i : UInt32), i.toNat ≤ src.size → total.toNat + (encFrom keep src i.toNat).length < 2 ^ 32 →
      src.size - i.toNat + keep.size + 1 < fuel →
      ∃ i', percent_encoded_size.loop1 src keep total i fuel = some (total + ((encFrom keep src i.toNat).length).toUInt32, i') := by
  induction fuel with
  | zero => intro _ _ _ _ hf; omega
  | succ fuel ih =>
    intro total i hi hbound hf
    unfold percent_encoded_size.loop1
    have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
    by_cases hlt : i.toNat < src.size
    · have hc : decide (i < src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz]; exact hlt
      rw [hc, if_pos rfl, kept_spec _ keep hkeep fuel (by omega)]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hsplit := encFrom_of_lt keep src i.toNat hlt
      have hblen := block_length keep (src.getD i.toNat 0)
      have hrest := encFrom_length_le keep src (i.toNat + 1)
      -- the width this byte takes, as a concrete number
      obtain ⟨w, hw1, hw2⟩ : ∃ w : Nat, (if keptB keep (src.getD i.toNat 0) then (1 : UInt32) else 3).toNat = w ∧
          (block keep (src.getD i.toNat 0)).length = w := by
        by_cases hk : keptB keep (src.getD i.toNat 0) = true
        · exact ⟨1, by rw [if_pos hk]; rfl, by rw [hblen, if_pos hk]⟩
        · exact ⟨3, by rw [if_neg hk]; rfl, by rw [hblen, if_neg hk]⟩
      have hw3 : w ≤ 3 := by rw [← hw2]; exact block_length_le keep _
      have hlen : (encFrom keep src i.toNat).length = w + (encFrom keep src (i.toNat + 1)).length := by
        rw [hsplit, List.length_append, hw2]
      have hstep : (total + (if keptB keep (src.getD i.toNat 0) then (1 : UInt32) else 3)).toNat = total.toNat + w := by
        rw [UInt32.toNat_add, hw1]; apply Nat.mod_eq_of_lt; omega
      obtain ⟨i', h⟩ := ih (total + (if keptB keep (src.getD i.toNat 0) then (1 : UInt32) else 3)) (i + 1)
        (by omega) (by rw [hstep, hi1]; omega) (by omega)
      have hval : total + (if keptB keep (src.getD i.toNat 0) then (1 : UInt32) else 3) +
          ((encFrom keep src (i.toNat + 1)).length).toUInt32 = total + ((encFrom keep src i.toNat).length).toUInt32 := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, hstep, UInt32.toNat_add, hlen, toUInt32_toNat_of_lt _ (by omega),
          toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      refine ⟨i', ?_⟩
      rw [h, hi1, hval]
    · have hc : decide (i < src.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz]; exact hlt
      rw [hc, if_neg Bool.false_ne_true]
      refine ⟨i, ?_⟩
      rw [encFrom_of_ge keep src i.toNat (by omega)]
      simp

theorem percent_encoded_size_spec (keep src : Array UInt8) (hkeep : keep.size + 1 < 2 ^ 32) (hsrc : src.size ≤ 1431655765)
    (fuel : Nat) (hf : src.size + keep.size + 1 < fuel) :
    percent_encoded_size src keep fuel = some (.Ok ((encFrom keep src 0).length).toUInt32) := by
  unfold percent_encoded_size
  have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
  have hc : decide (src.size.toUInt32 > (1431655765 : UInt32)) = false := by
    apply decide_eq_false
    show ¬ ((1431655765 : UInt32) < src.size.toUInt32)
    rw [UInt32.lt_iff_toNat_lt, hsz]
    show ¬ (1431655765 < src.size)
    omega
  rw [hc]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
  have hlen := encFrom_length_le keep src 0
  rw [Nat.sub_zero] at hlen
  obtain ⟨i', h⟩ := encoded_size_loop keep src hkeep (by omega) fuel 0 0 (by simp)
    (by simp only [UInt32.toNat_zero, Nat.zero_add]; omega) (by simp only [UInt32.toNat_zero, Nat.sub_zero]; omega)
  rw [h]
  simp

/-! ## The encoder loop -/

theorem percent_encode_loop (keep src : Array UInt8) (hkeep : keep.size + 1 < 2 ^ 32) (hsrc : 3 * src.size < 2 ^ 32)
    (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32), i.toNat ≤ src.size → dst.size < 2 ^ 32 →
      out.toNat + (encFrom keep src i.toNat).length ≤ dst.size →
      src.size - i.toNat + keep.size + 1 < fuel →
      ∃ dst' i' out', percent_encode.loop1 dst src keep i out fuel = some (dst', i', out') ∧
        dst'.size = dst.size ∧ i'.toNat = src.size ∧
        out'.toNat = out.toNat + (encFrom keep src i.toNat).length ∧
        ∀ k, dst'.getD k 0 = if out.toNat ≤ k ∧ k < out.toNat + (encFrom keep src i.toNat).length
          then (encFrom keep src i.toNat).getD (k - out.toNat) 0 else dst.getD k 0 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out hi hdst hbound hf
    unfold percent_encode.loop1
    have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
    by_cases hlt : i.toNat < src.size
    · have hc : decide (i < src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz]; exact hlt
      rw [hc, if_pos rfl, kept_spec _ keep hkeep fuel (by omega)]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hsplit := encFrom_of_lt keep src i.toNat hlt
      have hblen := block_length keep (src.getD i.toNat 0)
      -- the byte this iteration encodes
      obtain ⟨b, hb⟩ : ∃ b, b = src.getD i.toNat 0 := ⟨_, rfl⟩
      rw [← hb] at hsplit hblen ⊢
      by_cases hk : keptB keep b = true
      · rw [hk, if_pos rfl]
        simp only [Option.pure_def, Option.bind_some]
        have hlen1 : (block keep b).length = 1 := by rw [hblen, if_pos hk]
        have hlenE : (encFrom keep src i.toNat).length = 1 + (encFrom keep src (i.toNat + 1)).length := by
          rw [hsplit, List.length_append, hlen1]
        have ho1 : (out + 1).toNat = out.toNat + 1 := uadd out 1 1 (by decide) (by omega)
        obtain ⟨dst', i', out', heq, hsize, hi', hout', hget⟩ :=
          ih (dst.setIfInBounds out.toNat b) (i + 1) (out + 1)
            (by omega) (by simp only [Array.size_setIfInBounds]; exact hdst)
            (by simp only [Array.size_setIfInBounds]; rw [ho1, hi1]; rw [hsplit, List.length_append, hlen1] at hbound; omega)
            (by rw [hi1]; omega)
        refine ⟨dst', i', out', heq, by rw [hsize]; simp only [Array.size_setIfInBounds], hi', ?_, ?_⟩
        · rw [hout', ho1, hi1, hsplit, List.length_append, hlen1]; omega
        · intro k
          rw [hget k, hi1, ho1, hsplit, List.length_append, hlen1]
          by_cases hin : out.toNat + 1 ≤ k ∧ k < out.toNat + 1 + (encFrom keep src (i.toNat + 1)).length
          · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, getD_append_right_of_le _ _ _ (by rw [hlen1]; omega), hlen1]
            exact congrArg (fun n => (encFrom keep src (i.toNat + 1)).getD n 0) (by omega)
          · rw [if_neg hin]
            by_cases h0 : k = out.toNat
            · subst h0
              have hlt' : out.toNat < dst.size := by omega
              rw [if_pos ⟨Nat.le_refl _, by omega⟩, Nat.sub_self, Array.getD_eq_getD_getElem?,
                Array.getElem?_setIfInBounds]
              simp only [hlt', ↓reduceIte, Option.getD_some]
              unfold block; rw [if_pos hk]; rfl
            · rw [if_neg (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
                if_neg (fun h => h0 h.symm), ← Array.getD_eq_getD_getElem?]
      · have hk' : keptB keep b = false := by simpa using hk
        rw [hk', if_neg Bool.false_ne_true]
        simp only [Option.pure_def, Option.bind_some, hex_digit_upper]
        have hlen3 : (block keep b).length = 3 := by rw [hblen, if_neg hk]
        have hlenE : (encFrom keep src i.toNat).length = 3 + (encFrom keep src (i.toNat + 1)).length := by
          rw [hsplit, List.length_append, hlen3]
        have ho1 : (out + 1).toNat = out.toNat + 1 := uadd out 1 1 (by decide) (by omega)
        have ho2 : (out + 2).toNat = out.toNat + 2 := uadd out 2 2 (by decide) (by omega)
        have ho3 : (out + 3).toNat = out.toNat + 3 := uadd out 3 3 (by decide) (by omega)
        obtain ⟨dst', i', out', heq, hsize, hi', hout', hget⟩ :=
          ih (((dst.setIfInBounds out.toNat 37).setIfInBounds (out + 1).toNat (hexUpper (b >>> 4))).setIfInBounds
                (out + 2).toNat (hexUpper (b &&& 15)))
            (i + 1) (out + 3)
            (by omega) (by simp only [Array.size_setIfInBounds]; exact hdst)
            (by simp only [Array.size_setIfInBounds]; rw [ho3, hi1]; rw [hsplit, List.length_append, hlen3] at hbound; omega)
            (by rw [hi1]; omega)
        refine ⟨dst', i', out', heq, by rw [hsize]; simp only [Array.size_setIfInBounds], hi', ?_, ?_⟩
        · rw [hout', ho3, hi1, hsplit, List.length_append, hlen3]; omega
        · intro k
          rw [hget k, hi1, ho3, hsplit, List.length_append, hlen3]
          by_cases hin : out.toNat + 3 ≤ k ∧ k < out.toNat + 3 + (encFrom keep src (i.toNat + 1)).length
          · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, getD_append_right_of_le _ _ _ (by rw [hlen3]; omega), hlen3]
            exact congrArg (fun n => (encFrom keep src (i.toNat + 1)).getD n 0) (by omega)
          · rw [if_neg hin]
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
              Array.getElem?_setIfInBounds]
            simp only [Array.size_setIfInBounds]
            rw [ho1, ho2]
            have hblk : ∀ t, t < 3 → (block keep b ++ encFrom keep src (i.toNat + 1)).getD t 0 = (block keep b).getD t 0 := by
              intro t ht
              exact getD_append_left_of_lt _ _ _ (by rw [hlen3]; exact ht)
            by_cases h2 : out.toNat + 2 = k
            · rw [if_pos h2, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, show k - out.toNat = 2 by omega,
                hblk 2 (by omega)]
              unfold block; rw [if_neg hk]; rfl
            · rw [if_neg h2]
              by_cases h1 : out.toNat + 1 = k
              · rw [if_pos h1, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, show k - out.toNat = 1 by omega,
                  hblk 1 (by omega)]
                unfold block; rw [if_neg hk]; rfl
              · rw [if_neg h1]
                by_cases h0 : out.toNat = k
                · rw [if_pos h0, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, show k - out.toNat = 0 by omega,
                    hblk 0 (by omega)]
                  unfold block; rw [if_neg hk]; rfl
                · rw [if_neg h0, ← Array.getD_eq_getD_getElem?, if_neg (by omega)]
    · have hc : decide (i < src.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz]; exact hlt
      rw [hc, if_neg Bool.false_ne_true]
      refine ⟨dst, i, out, rfl, rfl, by omega, ?_, ?_⟩
      · rw [encFrom_of_ge keep src i.toNat (by omega)]; simp
      · intro k
        rw [encFrom_of_ge keep src i.toNat (by omega)]
        simp only [List.length_nil, Nat.add_zero]
        rw [if_neg (by omega)]

/-- `percent_encode` writes the blocks and reports their total length. -/
theorem percent_encode_spec (keep src dst : Array UInt8) (hkeep : keep.size + 1 < 2 ^ 32)
    (hsrc : src.size ≤ 1431655765) (hdst : dst.size < 2 ^ 32) (hroom : (encFrom keep src 0).length ≤ dst.size)
    (fuel : Nat) (hf : src.size + keep.size + 1 < fuel) :
    ∃ dst', percent_encode dst src keep fuel = some (.Ok ((encFrom keep src 0).length).toUInt32, dst') ∧
      dst'.size = dst.size ∧
      ∀ k, k < (encFrom keep src 0).length → dst'.getD k 0 = (encFrom keep src 0).getD k 0 := by
  have hlen := encFrom_length_le keep src 0
  rw [Nat.sub_zero] at hlen
  have hL : (((encFrom keep src 0).length).toUInt32).toNat = (encFrom keep src 0).length :=
    toUInt32_toNat_of_lt _ (by omega)
  have hsz : (dst.size.toUInt32).toNat = dst.size := toUInt32_toNat_of_lt _ hdst
  have hc : decide (((encFrom keep src 0).length).toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false
    show ¬ (dst.size.toUInt32 < ((encFrom keep src 0).length).toUInt32)
    rw [UInt32.lt_iff_toNat_lt, hL, hsz]; omega
  obtain ⟨dst', i', out', heq, hsize, _, _, hget⟩ :=
    percent_encode_loop keep src hkeep (by omega) fuel dst 0 0 (by simp) hdst
      (by simp only [UInt32.toNat_zero, Nat.zero_add]; exact hroom) (by simp only [UInt32.toNat_zero, Nat.sub_zero]; omega)
  unfold percent_encode
  simp only [percent_encoded_size_spec keep src hkeep hsrc fuel hf, Option.pure_def, bind, Option.bind, hc,
    Bool.false_eq_true, ↓reduceIte, heq]
  refine ⟨dst', rfl, hsize, ?_⟩
  intro k hk
  rw [hget k]
  simp only [UInt32.toNat_zero, Nat.zero_le, Nat.zero_add, true_and, Nat.sub_zero]
  rw [if_pos hk]

/-! ## The decoder

The decoder reads an array `enc` whose bytes are the blocks of `src`. Both
loops are stated at a source index `j`: the encoded position `i` is where the
blocks of `src[j..]` start, so `i + |encFrom j| = |enc|`, and the bytes from
`i` on are those blocks. -/

/-- The bytes of `enc` from `i` on are the blocks of `src` from `j` on. -/
def Blocks (keep src enc : Array UInt8) (i j : Nat) : Prop :=
  i + (encFrom keep src j).length = enc.size ∧
  ∀ k, k < (encFrom keep src j).length → enc.getD (i + k) 0 = (encFrom keep src j).getD k 0

theorem blocks_step (keep src enc : Array UInt8) (i j : Nat) (hj : j < src.size) (h : Blocks keep src enc i j) :
    Blocks keep src enc (i + (block keep (src.getD j 0)).length) (j + 1) := by
  obtain ⟨hsize, hget⟩ := h
  have hsplit := encFrom_of_lt keep src j hj
  refine ⟨?_, ?_⟩
  · rw [hsplit, List.length_append] at hsize; omega
  · intro k hk
    have := hget ((block keep (src.getD j 0)).length + k) (by rw [hsplit, List.length_append]; omega)
    rw [hsplit, getD_append_right_of_le _ _ _ (by omega), Nat.add_sub_cancel_left] at this
    rw [← this]; congr 1; omega

theorem blocks_head (keep src enc : Array UInt8) (i j : Nat) (hj : j < src.size) (h : Blocks keep src enc i j)
    (t : Nat) (ht : t < (block keep (src.getD j 0)).length) :
    enc.getD (i + t) 0 = (block keep (src.getD j 0)).getD t 0 := by
  obtain ⟨_, hget⟩ := h
  have hsplit := encFrom_of_lt keep src j hj
  rw [hget t (by rw [hsplit, List.length_append]; omega), hsplit, getD_append_left_of_lt _ _ _ ht]

theorem block_kept (keep : Array UInt8) (b : UInt8) (hk : keptB keep b = true) : block keep b = [b] := by
  unfold block; rw [if_pos hk]

theorem block_spelled (keep : Array UInt8) (b : UInt8) (hk : keptB keep b = false) :
    block keep b = [37, hexUpper (b >>> 4), hexUpper (b &&& 15)] := by
  unfold block; rw [if_neg (by simp [hk])]

theorem decoded_size_loop (keep src enc : Array UInt8) (hkeep : ∀ t, t < keep.size → keep.getD t 0 ≠ 37)
    (henc : enc.size < 2 ^ 32) (fuel : Nat) :
    ∀ (total i : UInt32) (j : Nat), j ≤ src.size → Blocks keep src enc i.toNat j →
      total.toNat + (src.size - j) < 2 ^ 32 → src.size - j < fuel →
      ∃ i', percent_decoded_size.loop1 enc total i true fuel = some (total + (src.size - j).toUInt32, i', true) := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro total i j hj hb htot hf
    unfold percent_decoded_size.loop1
    have hsz : (enc.size.toUInt32).toNat = enc.size := toUInt32_toNat_of_lt _ henc
    have hpos := hb.1
    rcases Nat.lt_or_ge j src.size with hlt | hge
    · have hsplit := encFrom_of_lt keep src j hlt
      have hblen := block_length keep (src.getD j 0)
      have hpos1 : 1 ≤ (encFrom keep src j).length := by
        rw [hsplit, List.length_append]; have := block_length_pos keep (src.getD j 0); omega
      have hc : decide (i < enc.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz]; omega
      rw [hc, Bool.and_true, if_pos rfl]
      have hstep := blocks_step keep src enc i.toNat j hlt hb
      by_cases hk : keptB keep (src.getD j 0) = true
      · -- a kept byte: not `%`, one position
        have hb0 : enc.getD i.toNat 0 = src.getD j 0 := by
          have := blocks_head keep src enc i.toNat j hlt hb 0 (by rw [hblen, if_pos hk]; omega)
          rw [Nat.add_zero, block_kept keep _ hk] at this; exact this
        have hne : (enc.getD i.toNat 0 == 37) = false := by
          rw [hb0]; exact beq_eq_false_iff_ne.mpr (kept_ne_percent keep hkeep _ hk)
        have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
        have ht1 : (total + 1).toNat = total.toNat + 1 := uadd total 1 1 (by decide) (by omega)
        rw [block_kept keep _ hk] at hstep
        have hstep1 : Blocks keep src enc (i + 1).toNat (j + 1) := by rw [hi1]; simpa using hstep
        obtain ⟨i', h⟩ := ih (total + 1) (i + 1) (j + 1) (by omega) hstep1 (by rw [ht1]; omega) (by omega)
        have hval : total + 1 + (src.size - (j + 1)).toUInt32 = total + (src.size - j).toUInt32 := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_add, ht1, UInt32.toNat_add, toUInt32_toNat_of_lt _ (by omega),
            toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        refine ⟨i', ?_⟩
        rw [hne, if_neg Bool.false_ne_true]
        simp only [Option.pure_def, bind, Option.bind, h, hval]
      · -- a spelled byte: `%`, two digits, three positions
        have hk' : keptB keep (src.getD j 0) = false := by simpa using hk
        have hlen3 : (block keep (src.getD j 0)).length = 3 := by rw [hblen, if_neg hk]
        have hb0 : enc.getD i.toNat 0 = 37 := by
          have := blocks_head keep src enc i.toNat j hlt hb 0 (by omega)
          rw [Nat.add_zero, block_spelled keep _ hk'] at this; exact this
        have hb1 : enc.getD (i.toNat + 1) 0 = hexUpper (src.getD j 0 >>> 4) := by
          have := blocks_head keep src enc i.toNat j hlt hb 1 (by omega)
          rw [block_spelled keep _ hk'] at this; exact this
        have hb2 : enc.getD (i.toNat + 2) 0 = hexUpper (src.getD j 0 &&& 15) := by
          have := blocks_head keep src enc i.toNat j hlt hb 2 (by omega)
          rw [block_spelled keep _ hk'] at this; exact this
        have heq : (enc.getD i.toNat 0 == 37) = true := by rw [hb0]; rfl
        have hpos3 : 3 ≤ (encFrom keep src j).length := by rw [hsplit, List.length_append, hlen3]; omega
        have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
        have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
        have hi3 : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
        have ht1 : (total + 1).toNat = total.toNat + 1 := uadd total 1 1 (by decide) (by omega)
        have hdig := upper_digits_lt' (src.getD j 0)
        have hroom : decide (enc.size.toUInt32 - i ≥ 3) = true := by
          apply decide_eq_true
          show (3 : UInt32) ≤ enc.size.toUInt32 - i
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hsz]; omega), hsz]
          show 3 ≤ enc.size - i.toNat
          omega
        rw [block_spelled keep _ hk'] at hstep
        have hstep3 : Blocks keep src enc (i + 3).toNat (j + 1) := by rw [hi3]; simpa using hstep
        obtain ⟨i', h⟩ := ih (total + 1) (i + 3) (j + 1) (by omega) hstep3 (by rw [ht1]; omega) (by omega)
        have hval : total + 1 + (src.size - (j + 1)).toUInt32 = total + (src.size - j).toUInt32 := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_add, ht1, UInt32.toNat_add, toUInt32_toNat_of_lt _ (by omega),
            toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        refine ⟨i', ?_⟩
        rw [heq, if_pos rfl, hi1, hi2, hb1, hb2]
        simp only [hex_value_def, Option.pure_def, bind, Option.bind, hroom, decide_eq_true hdig.1,
          decide_eq_true hdig.2, Bool.and_self, h, hval]
    · have hlen0 : (encFrom keep src j).length = 0 := by rw [encFrom_of_ge keep src j hge]; rfl
      have hc : decide (i < enc.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz]; omega
      rw [hc, Bool.false_and, if_neg Bool.false_ne_true]
      refine ⟨i, ?_⟩
      rw [show src.size - j = 0 by omega]
      simp

theorem percent_decoded_size_spec (keep src enc : Array UInt8) (plus : Bool)
    (hkeep : ∀ t, t < keep.size → keep.getD t 0 ≠ 37) (henc : enc.size < 2 ^ 32) (hsrc : src.size < 2 ^ 32)
    (hb : Blocks keep src enc 0 0) (fuel : Nat) (hf : src.size < fuel) :
    percent_decoded_size enc plus fuel = some (.Ok (src.size).toUInt32) := by
  obtain ⟨i', h⟩ := decoded_size_loop keep src enc hkeep henc fuel 0 0 0 (Nat.zero_le _)
    (by simpa using hb) (by simp; omega) (by simpa using hf)
  unfold percent_decoded_size
  simp only [Option.pure_def, bind, Option.bind, h]
  simp

theorem percent_decode_loop (keep src enc : Array UInt8) (plus : Bool)
    (hkeep : ∀ t, t < keep.size → keep.getD t 0 ≠ 37) (hplus : plus = true → ∀ t, t < keep.size → keep.getD t 0 ≠ 43)
    (henc : enc.size < 2 ^ 32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32) (j : Nat), j ≤ src.size → Blocks keep src enc i.toNat j →
      out.toNat = j → src.size ≤ dst.size → dst.size < 2 ^ 32 → src.size - j < fuel →
      ∃ dst' i' out', percent_decode.loop1 dst enc plus i out fuel = some (dst', i', out') ∧
        dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 = if j ≤ k ∧ k < src.size then src.getD k 0 else dst.getD k 0 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out j hj hb hout hdst hsmall hf
    unfold percent_decode.loop1
    have hsz : (enc.size.toUInt32).toNat = enc.size := toUInt32_toNat_of_lt _ henc
    have hpos := hb.1
    rcases Nat.lt_or_ge j src.size with hlt | hge
    · have hsplit := encFrom_of_lt keep src j hlt
      have hblen := block_length keep (src.getD j 0)
      have hpos1 : 1 ≤ (encFrom keep src j).length := by
        rw [hsplit, List.length_append]; have := block_length_pos keep (src.getD j 0); omega
      have hc : decide (i < enc.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz]; omega
      rw [hc, if_pos rfl]
      have hstep := blocks_step keep src enc i.toNat j hlt hb
      have ho1 : (out + 1).toNat = out.toNat + 1 := uadd out 1 1 (by decide) (by omega)
      by_cases hk : keptB keep (src.getD j 0) = true
      · have hb0 : enc.getD i.toNat 0 = src.getD j 0 := by
          have := blocks_head keep src enc i.toNat j hlt hb 0 (by rw [hblen, if_pos hk]; omega)
          rw [Nat.add_zero, block_kept keep _ hk] at this; exact this
        have hne : (enc.getD i.toNat 0 == 37) = false := by
          rw [hb0]; exact beq_eq_false_iff_ne.mpr (kept_ne_percent keep hkeep _ hk)
        have hwrite : (if (plus && (enc.getD i.toNat 0 == 43)) = true then (32 : UInt8) else enc.getD i.toNat 0) = src.getD j 0 := by
          rw [hb0]
          cases plus with
          | false => rw [Bool.false_and, if_neg Bool.false_ne_true]
          | true =>
            rw [Bool.true_and, beq_eq_false_iff_ne.mpr (kept_ne_plus keep (hplus rfl) _ hk), if_neg Bool.false_ne_true]
        have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
        rw [block_kept keep _ hk] at hstep
        have hstep1 : Blocks keep src enc (i + 1).toNat (j + 1) := by rw [hi1]; simpa using hstep
        obtain ⟨dst', i', out', h, hsize, hget⟩ := ih (dst.setIfInBounds out.toNat (src.getD j 0)) (i + 1) (out + 1) (j + 1)
          (by omega) hstep1 (by rw [ho1, hout]) (by simp only [Array.size_setIfInBounds]; exact hdst)
          (by simp only [Array.size_setIfInBounds]; exact hsmall) (by omega)
        refine ⟨dst', i', out', ?_, by rw [hsize]; simp only [Array.size_setIfInBounds], ?_⟩
        · rw [hne, if_neg Bool.false_ne_true]
          simp only [Option.pure_def, bind, Option.bind, hwrite, h]
        intro k
        rw [hget k]
        by_cases hin : j + 1 ≤ k ∧ k < src.size
        · rw [if_pos hin, if_pos ⟨by omega, hin.2⟩]
        · rw [if_neg hin]
          by_cases h0 : k = j
          · subst h0
            have hlt' : k < dst.size := by omega
            rw [if_pos ⟨Nat.le_refl _, hlt⟩, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hout]
            simp only [hlt', ↓reduceIte, Option.getD_some]
          · rw [if_neg (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hout,
              if_neg (fun h => h0 h.symm), ← Array.getD_eq_getD_getElem?]
      · have hk' : keptB keep (src.getD j 0) = false := by simpa using hk
        have hlen3 : (block keep (src.getD j 0)).length = 3 := by rw [hblen, if_neg hk]
        have hb0 : enc.getD i.toNat 0 = 37 := by
          have := blocks_head keep src enc i.toNat j hlt hb 0 (by omega)
          rw [Nat.add_zero, block_spelled keep _ hk'] at this; exact this
        have hb1 : enc.getD (i.toNat + 1) 0 = hexUpper (src.getD j 0 >>> 4) := by
          have := blocks_head keep src enc i.toNat j hlt hb 1 (by omega)
          rw [block_spelled keep _ hk'] at this; exact this
        have hb2 : enc.getD (i.toNat + 2) 0 = hexUpper (src.getD j 0 &&& 15) := by
          have := blocks_head keep src enc i.toNat j hlt hb 2 (by omega)
          rw [block_spelled keep _ hk'] at this; exact this
        have heq : (enc.getD i.toNat 0 == 37) = true := by rw [hb0]; rfl
        have hpos3 : 3 ≤ (encFrom keep src j).length := by rw [hsplit, List.length_append, hlen3]; omega
        have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
        have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
        have hi3 : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
        rw [block_spelled keep _ hk'] at hstep
        have hstep3 : Blocks keep src enc (i + 3).toNat (j + 1) := by rw [hi3]; simpa using hstep
        obtain ⟨dst', i', out', h, hsize, hget⟩ := ih (dst.setIfInBounds out.toNat (src.getD j 0)) (i + 3) (out + 1) (j + 1)
          (by omega) hstep3 (by rw [ho1, hout]) (by simp only [Array.size_setIfInBounds]; exact hdst)
          (by simp only [Array.size_setIfInBounds]; exact hsmall) (by omega)
        refine ⟨dst', i', out', ?_, by rw [hsize]; simp only [Array.size_setIfInBounds], ?_⟩
        · rw [heq, if_pos rfl, hi1, hi2, hb1, hb2]
          simp only [hex_value_def, Option.pure_def, bind, Option.bind, upper_digits_join', h]
        intro k
        rw [hget k]
        by_cases hin : j + 1 ≤ k ∧ k < src.size
        · rw [if_pos hin, if_pos ⟨by omega, hin.2⟩]
        · rw [if_neg hin]
          by_cases h0 : k = j
          · subst h0
            have hlt' : k < dst.size := by omega
            rw [if_pos ⟨Nat.le_refl _, hlt⟩, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hout]
            simp only [hlt', ↓reduceIte, Option.getD_some]
          · rw [if_neg (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hout,
              if_neg (fun h => h0 h.symm), ← Array.getD_eq_getD_getElem?]
    · have hc : decide (i < enc.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz]
        rw [encFrom_of_ge keep src j hge] at hpos; simp at hpos; omega
      rw [hc, if_neg Bool.false_ne_true]
      refine ⟨dst, i, out, rfl, rfl, ?_⟩
      intro k
      rw [if_neg (by omega)]

/-- `percent_decode` on the blocks of `src` writes `src` back and reports its length. -/
theorem percent_decode_spec (keep src enc dst : Array UInt8) (plus : Bool)
    (hkeep : ∀ t, t < keep.size → keep.getD t 0 ≠ 37) (hplus : plus = true → ∀ t, t < keep.size → keep.getD t 0 ≠ 43)
    (henc : enc.size < 2 ^ 32) (hsrc : src.size < 2 ^ 32) (hdst : dst.size < 2 ^ 32) (hroom : src.size ≤ dst.size)
    (hb : Blocks keep src enc 0 0) (fuel : Nat) (hf : src.size < fuel) :
    ∃ dst', percent_decode dst enc plus fuel = some (.Ok (src.size).toUInt32, dst') ∧ dst'.size = dst.size ∧
      ∀ k, k < src.size → dst'.getD k 0 = src.getD k 0 := by
  have hsize := percent_decoded_size_spec keep src enc plus hkeep henc hsrc hb fuel hf
  have hn : ((src.size).toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ hsrc
  have hd : (dst.size.toUInt32).toNat = dst.size := toUInt32_toNat_of_lt _ hdst
  have hc : decide ((src.size).toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false
    show ¬ (dst.size.toUInt32 < (src.size).toUInt32)
    rw [UInt32.lt_iff_toNat_lt, hn, hd]; omega
  obtain ⟨dst', i', out', heq, hsz, hget⟩ := percent_decode_loop keep src enc plus hkeep hplus henc fuel dst 0 0 0
    (Nat.zero_le _) (by simpa using hb) (by simp) hroom hdst (by simpa using hf)
  unfold percent_decode
  simp only [hsize, Option.pure_def, bind, Option.bind, hc, Bool.false_eq_true, ↓reduceIte, heq]
  refine ⟨dst', rfl, hsz, ?_⟩
  intro k hk
  rw [hget k, if_pos ⟨Nat.zero_le _, hk⟩]

/-! ## The round trip -/

/-- Encoding `src` with any keep set that holds no `%` (and no `+` when `+`
    decodes as a space), then decoding the bytes written, returns `src`. -/
theorem percent_round_trip (keep src dst dec : Array UInt8) (plus : Bool) (fuel : Nat)
    (hkeep : ∀ t, t < keep.size → keep.getD t 0 ≠ 37)
    (hplus : plus = true → ∀ t, t < keep.size → keep.getD t 0 ≠ 43)
    (hkeep_small : keep.size + 1 < 2 ^ 32) (hsrc : src.size ≤ 1431655765)
    (hdst : dst.size < 2 ^ 32) (hroom : (encFrom keep src 0).length ≤ dst.size)
    (hdec : dec.size < 2 ^ 32) (hdec_room : src.size ≤ dec.size)
    (hf : src.size + keep.size + 1 < fuel) :
    ∃ dst', percent_encode dst src keep fuel = some (.Ok ((encFrom keep src 0).length).toUInt32, dst') ∧
      ∀ enc : Array UInt8, enc.size = (encFrom keep src 0).length →
        (∀ k, k < enc.size → enc.getD k 0 = dst'.getD k 0) →
        ∃ dec', percent_decode dec enc plus fuel = some (.Ok (src.size).toUInt32, dec') ∧ dec'.size = dec.size ∧
          ∀ k, k < src.size → dec'.getD k 0 = src.getD k 0 := by
  obtain ⟨dst', henc, _, hget⟩ := percent_encode_spec keep src dst hkeep_small hsrc hdst hroom fuel hf
  refine ⟨dst', henc, ?_⟩
  intro enc hsize hbytes
  have hb : Blocks keep src enc 0 0 := by
    refine ⟨by simpa using hsize.symm, ?_⟩
    intro k hk
    rw [Nat.zero_add, hbytes k (by omega), hget k hk]
  exact percent_decode_spec keep src enc dec plus hkeep hplus (by omega) (by omega) hdec hdec_room hb fuel (by omega)

end Oak.Stdlib.Encoding
