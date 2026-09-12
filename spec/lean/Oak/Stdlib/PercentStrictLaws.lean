import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.EncodingLaws
import Oak.Stdlib.Base64Laws
import Oak.Stdlib.PercentLaws

/-!
# Oak.Stdlib.PercentStrictLaws — what the percent decoder accepts

`percent_decode` succeeds on `src` exactly when every `%` in `src` is
followed by two hexadecimal digits, and then it writes the bytes the
specification function `pdec` denotes: a spelled byte for each `%XX`, a
space for `+` when `plus_as_space` is set, every other byte itself. Both
directions are proved against the extraction by fuel induction over the
decoder's two loops, with `pdec` as the reference: `pdec src plus j` is
`none` when the text from `j` is malformed and `some l` when it decodes
to `l`.
-/

namespace Oak.Stdlib.Encoding

set_option maxRecDepth 65536

/-! ## The reference decoder -/

/-- The table value of a byte as the extraction computes it. -/
def hvU (b : UInt8) : UInt32 := (HEX_VALUES.getD (b.toUInt32).toNat 0).toUInt32

theorem hex_value_hvU (b : UInt8) (fuel : Nat) : hex_value b fuel = some (hvU b) := rfl

-- The table lookup stays folded: nothing below unfolds `HEX_VALUES` by `whnf`.
attribute [irreducible] hvU

/-- The byte a spelled `%XY` denotes, exactly as the decoder joins it. -/
def spelledByte (a b : UInt8) : UInt8 := ((hvU a <<< 4) ||| hvU b).toUInt8

/-- A plain byte, with `+` read as a space when asked. -/
def plainByte (plus : Bool) (b : UInt8) : UInt8 := if plus && (b == 43) then 32 else b

/-- `pdec src plus j` decodes the text from position `j`: `none` when a `%`
    lacks two hexadecimal digits before the end, else the decoded bytes. -/
def pdec (src : Array UInt8) (plus : Bool) (j : Nat) : Option (List UInt8) :=
  if h : j < src.size then
    if src.getD j 0 = 37 then
      if j + 2 < src.size ∧ (hvU (src.getD (j + 1) 0)).toNat < 16 ∧ (hvU (src.getD (j + 2) 0)).toNat < 16 then
        (pdec src plus (j + 3)).map (fun l => spelledByte (src.getD (j + 1) 0) (src.getD (j + 2) 0) :: l)
      else none
    else (pdec src plus (j + 1)).map (fun l => plainByte plus (src.getD j 0) :: l)
  else some []
termination_by src.size - j
decreasing_by all_goals omega

theorem pdec_of_ge (src : Array UInt8) (plus : Bool) (j : Nat) (h : src.size ≤ j) :
    pdec src plus j = some [] := by
  rw [pdec, dif_neg (Nat.not_lt.mpr h)]

theorem pdec_of_pct (src : Array UInt8) (plus : Bool) (j : Nat) (hj : j < src.size) (hb : src.getD j 0 = 37) :
    pdec src plus j =
      if j + 2 < src.size ∧ (hvU (src.getD (j + 1) 0)).toNat < 16 ∧ (hvU (src.getD (j + 2) 0)).toNat < 16 then
        (pdec src plus (j + 3)).map (fun l => spelledByte (src.getD (j + 1) 0) (src.getD (j + 2) 0) :: l)
      else none := by
  rw [pdec, dif_pos hj, if_pos hb]

theorem pdec_of_plain (src : Array UInt8) (plus : Bool) (j : Nat) (hj : j < src.size) (hb : src.getD j 0 ≠ 37) :
    pdec src plus j = (pdec src plus (j + 1)).map (fun l => plainByte plus (src.getD j 0) :: l) := by
  rw [pdec, dif_pos hj, if_neg hb]

/-- A decoded suffix has at most as many bytes as positions remain. -/
theorem pdec_length_le_aux (src : Array UInt8) (plus : Bool) :
    ∀ n j l, src.size - j = n → pdec src plus j = some l → l.length ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j l hn hl
    rcases Nat.lt_or_ge j src.size with hj | hj
    · by_cases hb : src.getD j 0 = 37
      · rw [pdec_of_pct src plus j hj hb] at hl
        split at hl
        · rename_i hc
          rcases hm : pdec src plus (j + 3) with _ | l'
          · rw [hm] at hl; simp at hl
          · rw [hm] at hl
            simp only [Option.map_some, Option.some.injEq] at hl
            subst hl
            have := ih (src.size - (j + 3)) (by omega) (j + 3) l' rfl hm
            simp only [List.length_cons]; omega
        · simp at hl
      · rw [pdec_of_plain src plus j hj hb] at hl
        rcases hm : pdec src plus (j + 1) with _ | l'
        · rw [hm] at hl; simp at hl
        · rw [hm] at hl
          simp only [Option.map_some, Option.some.injEq] at hl
          subst hl
          have := ih (src.size - (j + 1)) (by omega) (j + 1) l' rfl hm
          simp only [List.length_cons]; omega
    · rw [pdec_of_ge src plus j hj] at hl
      simp only [Option.some.injEq] at hl; subst hl; simp

theorem pdec_length_le (src : Array UInt8) (plus : Bool) (j : Nat) (l : List UInt8)
    (hl : pdec src plus j = some l) : l.length ≤ src.size - j :=
  pdec_length_le_aux src plus _ j l rfl hl

/-! ## The size scan -/

/-- The decoder's size scan agrees with `pdec`: on a well-formed suffix it
    counts the decoded bytes and stays valid; on a malformed one it leaves
    the loop with `valid = false`. -/
theorem pdec_size_loop (src : Array UInt8) (plus : Bool) (hsrc : src.size + 3 < 2 ^ 32) (fuel : Nat) :
    ∀ (total i : UInt32) (j : Nat), i.toNat = j → j ≤ src.size → total.toNat + (src.size - j) < 2 ^ 32 →
      src.size - j < fuel →
      (∀ l, pdec src plus j = some l →
        ∃ i', percent_decoded_size.loop1 src total i true fuel = some (total + l.length.toUInt32, i', true)) ∧
      (pdec src plus j = none →
        ∃ t' i', percent_decoded_size.loop1 src total i true fuel = some (t', i', false)) := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro total i j hi hj htot hf
    unfold percent_decoded_size.loop1
    have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
    rcases Nat.lt_or_ge j src.size with hlt | hge
    · have hc : decide (i < src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz]; omega
      rw [hc, Bool.and_true, if_pos rfl]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
      have hi3 : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
      have ht1 : (total + 1).toNat = total.toNat + 1 := uadd total 1 1 (by decide) (by omega)
      by_cases hb : src.getD j 0 = 37
      · -- a `%`: three positions, two digits
        have heq : (src.getD i.toNat 0 == 37) = true := by rw [hi, hb]; rfl
        rw [heq, if_pos rfl, hi1, hi2, hi]
        simp only [hex_value_hvU, Option.pure_def, bind, Option.bind]
        have hroom : decide (src.size.toUInt32 - i ≥ 3) = (decide (j + 2 < src.size)) := by
          show decide ((3 : UInt32) ≤ src.size.toUInt32 - i) = _
          have hle : i ≤ src.size.toUInt32 := by rw [UInt32.le_iff_toNat_le, hsz]; omega
          by_cases h3 : j + 2 < src.size
          · rw [decide_eq_true h3]; apply decide_eq_true
            rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ hle, hsz]
            show 3 ≤ src.size - i.toNat; omega
          · rw [decide_eq_false h3]; apply decide_eq_false
            rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ hle, hsz]
            show ¬ (3 ≤ src.size - i.toNat); omega
        rw [hroom]
        constructor
        · intro l hl
          rw [pdec_of_pct src plus j hlt hb] at hl
          split at hl
          · rename_i hcond
            obtain ⟨h3, hd1, hd2⟩ := hcond
            rcases hm : pdec src plus (j + 3) with _ | l'
            · rw [hm] at hl; simp at hl
            · rw [hm] at hl
              simp only [Option.map_some, Option.some.injEq] at hl
              subst hl
              have hd1' : decide (hvU (src.getD (j + 1) 0) < 16) = true := by
                apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hd1
              have hd2' : decide (hvU (src.getD (j + 2) 0) < 16) = true := by
                apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hd2
              rw [decide_eq_true h3, hd1', hd2']
              simp only [Bool.and_self]
              obtain ⟨i', h⟩ := (ih (total + 1) (i + 3) (j + 3) (by rw [hi3, hi]) (by omega) (by omega) (by omega)).1 l' hm
              refine ⟨i', ?_⟩
              rw [h]
              have hval : total + 1 + l'.length.toUInt32 = total + (l'.length + 1).toUInt32 := by
                have hll := pdec_length_le src plus (j + 3) l' hm
                apply UInt32.toNat.inj
                rw [UInt32.toNat_add, ht1, UInt32.toNat_add, toUInt32_toNat_of_lt _ (by omega),
                  toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                omega
              simp only [List.length_cons, hval]
          · simp at hl
        · intro hn
          rw [pdec_of_pct src plus j hlt hb] at hn
          split at hn
          · rename_i hcond
            obtain ⟨h3, hd1, hd2⟩ := hcond
            rcases hm : pdec src plus (j + 3) with _ | l'
            · have hd1' : decide (hvU (src.getD (j + 1) 0) < 16) = true := by
                apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hd1
              have hd2' : decide (hvU (src.getD (j + 2) 0) < 16) = true := by
                apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hd2
              rw [decide_eq_true h3, hd1', hd2']
              simp only [Bool.and_self]
              obtain ⟨t', i', h⟩ := (ih (total + 1) (i + 3) (j + 3) (by rw [hi3, hi]) (by omega) (by omega) (by omega)).2 hm
              exact ⟨t', i', by rw [h]⟩
            · rw [hm] at hn; simp at hn
          · rename_i hcond
            -- the scan sets `valid = false` and the next iteration returns it
            have hfalse : ((decide (j + 2 < src.size) && decide (hvU (src.getD (j + 1) 0) < 16)) &&
                decide (hvU (src.getD (j + 2) 0) < 16)) = false := by
              by_cases h3 : j + 2 < src.size
              · by_cases hd1 : (hvU (src.getD (j + 1) 0)).toNat < 16
                · have hd2 : ¬ (hvU (src.getD (j + 2) 0)).toNat < 16 := fun hd2 => hcond ⟨h3, hd1, hd2⟩
                  rw [decide_eq_false (p := hvU (src.getD (j + 2) 0) < 16)
                    (fun h => hd2 (UInt32.lt_iff_toNat_lt.mp h)), Bool.and_false]
                · rw [decide_eq_false (p := hvU (src.getD (j + 1) 0) < 16)
                    (fun h => hd1 (UInt32.lt_iff_toNat_lt.mp h)), Bool.and_false, Bool.false_and]
              · rw [decide_eq_false (p := j + 2 < src.size) h3, Bool.false_and, Bool.false_and]
            rw [hfalse]
            refine ⟨total + 1, i + 3, ?_⟩
            cases fuel with
            | zero => omega
            | succ fuel =>
              rw [percent_decoded_size.loop1]
              rw [Bool.and_false, if_neg Bool.false_ne_true]
              rfl
      · -- a plain byte: one position
        have hne : (src.getD i.toNat 0 == 37) = false := by rw [hi]; exact beq_eq_false_iff_ne.mpr hb
        rw [hne, if_neg Bool.false_ne_true]
        simp only [Option.pure_def, bind, Option.bind]
        constructor
        · intro l hl
          rw [pdec_of_plain src plus j hlt hb] at hl
          rcases hm : pdec src plus (j + 1) with _ | l'
          · rw [hm] at hl; simp at hl
          · rw [hm] at hl
            simp only [Option.map_some, Option.some.injEq] at hl
            subst hl
            obtain ⟨i', h⟩ := (ih (total + 1) (i + 1) (j + 1) (by rw [hi1, hi]) (by omega) (by omega) (by omega)).1 l' hm
            refine ⟨i', ?_⟩
            rw [h]
            have hval : total + 1 + l'.length.toUInt32 = total + (l'.length + 1).toUInt32 := by
              have hll := pdec_length_le src plus (j + 1) l' hm
              apply UInt32.toNat.inj
              rw [UInt32.toNat_add, ht1, UInt32.toNat_add, toUInt32_toNat_of_lt _ (by omega),
                toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              omega
            simp only [List.length_cons, hval]
        · intro hn
          rw [pdec_of_plain src plus j hlt hb] at hn
          rcases hm : pdec src plus (j + 1) with _ | l'
          · obtain ⟨t', i', h⟩ := (ih (total + 1) (i + 1) (j + 1) (by rw [hi1, hi]) (by omega) (by omega) (by omega)).2 hm
            exact ⟨t', i', by rw [h]⟩
          · rw [hm] at hn; simp at hn
    · have hc : decide (i < src.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz]; omega
      rw [hc, Bool.false_and, if_neg Bool.false_ne_true]
      constructor
      · intro l hl
        rw [pdec_of_ge src plus j hge] at hl
        simp only [Option.some.injEq] at hl; subst hl
        exact ⟨i, by simp⟩
      · intro hn
        rw [pdec_of_ge src plus j hge] at hn
        exact absurd hn (by simp)

/-- The size scan: `Ok` with the decoded length on a well-formed text,
    `InvalidCharacter` otherwise. -/
theorem percent_decoded_size_strict (src : Array UInt8) (plus : Bool) (hsrc : src.size + 3 < 2 ^ 32)
    (fuel : Nat) (hf : src.size < fuel) :
    (∀ l, pdec src plus 0 = some l → percent_decoded_size src plus fuel = some (.Ok l.length.toUInt32)) ∧
    (pdec src plus 0 = none → percent_decoded_size src plus fuel = some (.Err .InvalidCharacter)) := by
  have h := pdec_size_loop src plus hsrc fuel 0 0 0 (by simp) (Nat.zero_le _) (by simp; omega) (by simpa using hf)
  constructor
  · intro l hl
    obtain ⟨i', hloop⟩ := h.1 l hl
    unfold percent_decoded_size
    simp only [Option.pure_def, bind, Option.bind, hloop]
    simp
  · intro hn
    obtain ⟨t', i', hloop⟩ := h.2 hn
    unfold percent_decoded_size
    simp only [Option.pure_def, bind, Option.bind, hloop]
    simp

/-- `percent_decoded_size` accepts exactly the well-formed texts. -/
theorem percent_decoded_size_ok_iff (src : Array UInt8) (plus : Bool) (hsrc : src.size + 3 < 2 ^ 32)
    (fuel : Nat) (hf : src.size < fuel) (n : UInt32) :
    percent_decoded_size src plus fuel = some (.Ok n) ↔ ∃ l, pdec src plus 0 = some l ∧ n = l.length.toUInt32 := by
  have h := percent_decoded_size_strict src plus hsrc fuel hf
  constructor
  · intro hok
    rcases hm : pdec src plus 0 with _ | l
    · rw [h.2 hm] at hok; cases hok
    · rw [h.1 l hm] at hok
      simp only [Option.some.injEq, Result_u32_EncodingError.Ok.injEq] at hok
      exact ⟨l, rfl, hok.symm⟩
  · rintro ⟨l, hl, rfl⟩
    exact h.1 l hl

/-! ## The decode loop -/

/-- On a well-formed suffix the decode loop writes `pdec`'s bytes from `out`
    and leaves every other destination byte alone. -/
theorem pdec_decode_loop (src : Array UInt8) (plus : Bool) (hsrc : src.size + 3 < 2 ^ 32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32) (j : Nat) (l : List UInt8), i.toNat = j → j ≤ src.size →
      pdec src plus j = some l → out.toNat + (src.size - j) < 2 ^ 32 → dst.size < 2 ^ 32 →
      out.toNat + l.length ≤ dst.size → src.size - j < fuel →
      ∃ dst' i' out', percent_decode.loop1 dst src plus i out fuel = some (dst', i', out') ∧
        dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 = if out.toNat ≤ k ∧ k < out.toNat + l.length then l.getD (k - out.toNat) 0 else dst.getD k 0 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out j l hi hj hl hout hdst hroom hf
    unfold percent_decode.loop1
    have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
    rcases Nat.lt_or_ge j src.size with hlt | hge
    · have hc : decide (i < src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz]; omega
      rw [hc, if_pos rfl]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
      have hi3 : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
      have ho1 : (out + 1).toNat = out.toNat + 1 := uadd out 1 1 (by decide) (by omega)
      by_cases hb : src.getD j 0 = 37
      · have heq : (src.getD i.toNat 0 == 37) = true := by rw [hi, hb]; rfl
        rw [pdec_of_pct src plus j hlt hb] at hl
        split at hl
        · rename_i hcond
          rcases hm : pdec src plus (j + 3) with _ | l'
          · rw [hm] at hl; simp at hl
          · rw [hm] at hl
            simp only [Option.map_some, Option.some.injEq] at hl
            subst hl
            rw [heq, if_pos rfl, hi1, hi2, hi]
            simp only [hex_value_hvU, Option.pure_def, bind, Option.bind]
            obtain ⟨dst', i', out', h, hsize, hget⟩ := ih
              (dst.setIfInBounds out.toNat (spelledByte (src.getD (j + 1) 0) (src.getD (j + 2) 0)))
              (i + 3) (out + 1) (j + 3) l' (by rw [hi3, hi]) (by omega) hm (by rw [ho1]; omega)
              (by simp only [Array.size_setIfInBounds]; exact hdst)
              (by simp only [Array.size_setIfInBounds, List.length_cons] at hroom ⊢; omega) (by omega)
            refine ⟨dst', i', out', ?_, by rw [hsize]; simp only [Array.size_setIfInBounds], ?_⟩
            · simpa only [spelledByte] using h
            intro k
            rw [hget k, ho1]
            simp only [List.length_cons]
            by_cases hin : out.toNat + 1 ≤ k ∧ k < out.toNat + 1 + l'.length
            · rw [if_pos hin, if_pos ⟨by omega, by omega⟩]
              have : k - out.toNat = (k - (out.toNat + 1)) + 1 := by omega
              rw [this, List.getD_cons_succ]
            · rw [if_neg hin]
              by_cases h0 : k = out.toNat
              · subst h0
                have hk : out.toNat < dst.size := by simp only [List.length_cons] at hroom; omega
                rw [if_pos ⟨Nat.le_refl _, by omega⟩, Nat.sub_self, List.getD_cons_zero,
                  Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
                simp only [hk, ↓reduceIte, Option.getD_some]
              · rw [if_neg (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
                  if_neg (fun h => h0 h.symm), ← Array.getD_eq_getD_getElem?]
        · simp at hl
      · have hne : (src.getD i.toNat 0 == 37) = false := by rw [hi]; exact beq_eq_false_iff_ne.mpr hb
        rw [pdec_of_plain src plus j hlt hb] at hl
        rcases hm : pdec src plus (j + 1) with _ | l'
        · rw [hm] at hl; simp at hl
        · rw [hm] at hl
          simp only [Option.map_some, Option.some.injEq] at hl
          subst hl
          rw [hne, if_neg Bool.false_ne_true]
          simp only [Option.pure_def, bind, Option.bind]
          have hwrite : (if (plus && (src.getD i.toNat 0 == 43)) = true then (32 : UInt8) else src.getD i.toNat 0) =
              plainByte plus (src.getD j 0) := by
            rw [hi]; rfl
          rw [hwrite]
          obtain ⟨dst', i', out', h, hsize, hget⟩ := ih
            (dst.setIfInBounds out.toNat (plainByte plus (src.getD j 0)))
            (i + 1) (out + 1) (j + 1) l' (by rw [hi1, hi]) (by omega) hm (by rw [ho1]; omega)
            (by simp only [Array.size_setIfInBounds]; exact hdst)
            (by simp only [Array.size_setIfInBounds, List.length_cons] at hroom ⊢; omega) (by omega)
          refine ⟨dst', i', out', ?_, by rw [hsize]; simp only [Array.size_setIfInBounds], ?_⟩
          · rw [h]
          intro k
          rw [hget k, ho1]
          simp only [List.length_cons]
          by_cases hin : out.toNat + 1 ≤ k ∧ k < out.toNat + 1 + l'.length
          · rw [if_pos hin, if_pos ⟨by omega, by omega⟩]
            have : k - out.toNat = (k - (out.toNat + 1)) + 1 := by omega
            rw [this, List.getD_cons_succ]
          · rw [if_neg hin]
            by_cases h0 : k = out.toNat
            · subst h0
              have hk : out.toNat < dst.size := by simp only [List.length_cons] at hroom; omega
              rw [if_pos ⟨Nat.le_refl _, by omega⟩, Nat.sub_self, List.getD_cons_zero,
                Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
              simp only [hk, ↓reduceIte, Option.getD_some]
            · rw [if_neg (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
                if_neg (fun h => h0 h.symm), ← Array.getD_eq_getD_getElem?]
    · have hc : decide (i < src.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz]; omega
      rw [hc, if_neg Bool.false_ne_true]
      rw [pdec_of_ge src plus j hge] at hl
      simp only [Option.some.injEq] at hl; subst hl
      refine ⟨dst, i, out, rfl, rfl, ?_⟩
      intro k
      simp only [List.length_nil, Nat.add_zero]
      rw [if_neg (by omega)]

/-! ## Strictness of the decoder -/

/-- `percent_decode` accepts `src` exactly when every `%` is followed by two
    hexadecimal digits; then it writes `pdec`'s bytes and reports their count,
    provided the destination holds them. A malformed text is
    `InvalidCharacter`; a well-formed text with too small a destination is
    `DestinationTooSmall`, and the destination is untouched in both cases. -/
theorem percent_decode_strict (src dst : Array UInt8) (plus : Bool) (hsrc : src.size + 3 < 2 ^ 32)
    (hdst : dst.size < 2 ^ 32) (fuel : Nat) (hf : src.size < fuel) :
    (pdec src plus 0 = none → percent_decode dst src plus fuel = some (.Err .InvalidCharacter, dst)) ∧
    (∀ l, pdec src plus 0 = some l → dst.size < l.length →
      percent_decode dst src plus fuel = some (.Err .DestinationTooSmall, dst)) ∧
    (∀ l, pdec src plus 0 = some l → l.length ≤ dst.size →
      ∃ dst', percent_decode dst src plus fuel = some (.Ok l.length.toUInt32, dst') ∧ dst'.size = dst.size ∧
        (∀ k, k < l.length → dst'.getD k 0 = l.getD k 0) ∧
        (∀ k, l.length ≤ k → dst'.getD k 0 = dst.getD k 0)) := by
  have hstrict := percent_decoded_size_strict src plus hsrc fuel hf
  have hd : (dst.size.toUInt32).toNat = dst.size := toUInt32_toNat_of_lt _ hdst
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    unfold percent_decode
    simp only [hstrict.2 hn, Option.pure_def, bind, Option.bind]
  · intro l hl hsmall
    have hll := pdec_length_le src plus 0 l hl
    have hn : (l.length.toUInt32).toNat = l.length := toUInt32_toNat_of_lt _ (by omega)
    have hc : decide (l.length.toUInt32 > dst.size.toUInt32) = true := by
      apply decide_eq_true
      show dst.size.toUInt32 < l.length.toUInt32
      rw [UInt32.lt_iff_toNat_lt, hn, hd]; exact hsmall
    unfold percent_decode
    simp only [hstrict.1 l hl, Option.pure_def, bind, Option.bind, hc, ↓reduceIte]
  · intro l hl hroom
    have hll := pdec_length_le src plus 0 l hl
    have hn : (l.length.toUInt32).toNat = l.length := toUInt32_toNat_of_lt _ (by omega)
    have hc : decide (l.length.toUInt32 > dst.size.toUInt32) = false := by
      apply decide_eq_false
      show ¬ (dst.size.toUInt32 < l.length.toUInt32)
      rw [UInt32.lt_iff_toNat_lt, hn, hd]; omega
    obtain ⟨dst', i', out', heq, hsz, hget⟩ := pdec_decode_loop src plus hsrc fuel dst 0 0 0 l (by simp)
      (Nat.zero_le _) hl (by simp; omega) hdst (by simpa using hroom) (by simpa using hf)
    unfold percent_decode
    simp only [hstrict.1 l hl, Option.pure_def, bind, Option.bind, hc, Bool.false_eq_true, ↓reduceIte, heq]
    refine ⟨dst', rfl, hsz, ?_, ?_⟩
    · intro k hk
      rw [hget k]; simp only [UInt32.toNat_zero, Nat.zero_le, Nat.zero_add, hk, and_self, ↓reduceIte, Nat.sub_zero]
    · intro k hk
      rw [hget k]; simp only [UInt32.toNat_zero, Nat.zero_add]
      rw [if_neg (by omega)]

/-- The iff form: the decoder returns `Ok` exactly on the well-formed texts
    that fit the destination. -/
theorem percent_decode_ok_iff (src dst : Array UInt8) (plus : Bool) (hsrc : src.size + 3 < 2 ^ 32)
    (hdst : dst.size < 2 ^ 32) (fuel : Nat) (hf : src.size < fuel) (n : UInt32) :
    (∃ dst', percent_decode dst src plus fuel = some (.Ok n, dst')) ↔
      ∃ l, pdec src plus 0 = some l ∧ n = l.length.toUInt32 ∧ l.length ≤ dst.size := by
  have h := percent_decode_strict src dst plus hsrc hdst fuel hf
  constructor
  · rintro ⟨dst', hok⟩
    rcases hm : pdec src plus 0 with _ | l
    · rw [h.1 hm] at hok; cases hok
    · rcases Nat.lt_or_ge dst.size l.length with hsmall | hroom
      · rw [h.2.1 l hm hsmall] at hok; cases hok
      · obtain ⟨dst'', heq, _, _, _⟩ := h.2.2 l hm hroom
        rw [heq] at hok
        simp only [Option.some.injEq, Prod.mk.injEq, Result_u32_EncodingError.Ok.injEq] at hok
        exact ⟨l, rfl, hok.1.symm, hroom⟩
  · rintro ⟨l, hl, rfl, hroom⟩
    obtain ⟨dst', heq, _, _, _⟩ := h.2.2 l hl hroom
    exact ⟨dst', heq⟩

end Oak.Stdlib.Encoding
