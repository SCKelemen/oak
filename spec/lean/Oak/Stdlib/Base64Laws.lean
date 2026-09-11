import Std.Tactic.BVDecide
import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.EncodingLaws

/-!
# Oak.Stdlib.Base64Laws — the base64 round trip on the extracted `encoding` package

`base64_decode (base64_encode src) = src` for every source below the size
limit, both alphabets, padded or not. The proof follows the extraction:
the encoder's group loop (three bytes to four symbols) and its one- or
two-byte tail, then the decoder's padding strip, its validation scan (the
`or` of every symbol value stays below 64 because each is), the canonical
check on the last symbol's low bits, and the decoder's group loop (four
symbols to three bytes) and tail. The 24-bit word identities that make a
group round-trip are bit-vector facts (`bv_decide`); the symbol tables are
read in the kernel (`decide +kernel`).
-/

namespace Oak.Stdlib.Encoding

set_option maxRecDepth 65536

/-! ## Tables -/

def b64symbols (url : Bool) : Array UInt8 := if url then BASE64_URL_SYMBOLS else BASE64_STD_SYMBOLS
def b64values (url : Bool) : Array UInt8 := if url then BASE64_URL_VALUES else BASE64_STD_VALUES

theorem b64_roundtrip_std : ∀ v : Fin 64,
    BASE64_STD_VALUES.getD ((BASE64_STD_SYMBOLS.getD v.val 0).toUInt32).toNat 0 = v.val.toUInt8 := by decide +kernel
theorem b64_roundtrip_url : ∀ v : Fin 64,
    BASE64_URL_VALUES.getD ((BASE64_URL_SYMBOLS.getD v.val 0).toUInt32).toNat 0 = v.val.toUInt8 := by decide +kernel
theorem b64_not_pad_std : ∀ v : Fin 64, BASE64_STD_SYMBOLS.getD v.val 0 ≠ 61 := by decide +kernel
theorem b64_not_pad_url : ∀ v : Fin 64, BASE64_URL_SYMBOLS.getD v.val 0 ≠ 61 := by decide +kernel
theorem b64_pad_value_std : (BASE64_STD_VALUES.getD 61 0).toNat = 64 := by decide +kernel
theorem b64_pad_value_url : (BASE64_URL_VALUES.getD 61 0).toNat = 64 := by decide +kernel

theorem b64_roundtrip (url : Bool) (v : Nat) (hv : v < 64) :
    (b64values url).getD (((b64symbols url).getD v 0).toUInt32).toNat 0 = v.toUInt8 := by
  unfold b64values b64symbols
  cases url
  · exact b64_roundtrip_std ⟨v, hv⟩
  · exact b64_roundtrip_url ⟨v, hv⟩

theorem b64_not_pad (url : Bool) (v : Nat) (hv : v < 64) : (b64symbols url).getD v 0 ≠ 61 := by
  unfold b64symbols
  cases url
  · exact b64_not_pad_std ⟨v, hv⟩
  · exact b64_not_pad_url ⟨v, hv⟩

/-- A symbol's value, as the scan and decoder read it. -/
def symValue (url : Bool) (b : UInt8) : UInt32 := ((b64values url).getD (b.toUInt32).toNat 0).toUInt32

theorem symValue_roundtrip (url : Bool) (v : UInt32) (hv : v.toNat < 64) :
    symValue url ((b64symbols url).getD v.toNat 0) = v := by
  unfold symValue
  rw [b64_roundtrip url v.toNat hv]
  apply UInt32.toNat.inj
  rw [UInt8.toNat_toUInt32, toUInt8_toNat_of_lt _ (by omega)]

/-! ## The encoder -/

/-- The 24-bit word of source group `j`. -/
def encWord (src : Array UInt8) (j : Nat) : UInt32 :=
  ((src.getD (3 * j) 0).toUInt32 <<< 16) ||| ((src.getD (3 * j + 1) 0).toUInt32 <<< 8) ||| (src.getD (3 * j + 2) 0).toUInt32

/-- The `t`-th six-bit field of a word, `t < 4`. -/
def sixbit (w : UInt32) (t : Nat) : UInt32 :=
  if t = 0 then w >>> 18 else if t = 1 then (w >>> 12) &&& 63 else if t = 2 then (w >>> 6) &&& 63 else w &&& 63

/-- The symbol the encoder writes at output position `k` of the group region. -/
def encSym (src symbols : Array UInt8) (k : Nat) : UInt8 :=
  symbols.getD (sixbit (encWord src (k / 4)) (k % 4)).toNat 0

theorem encWord_lt (src : Array UInt8) (j : Nat) : (encWord src j).toNat < 2 ^ 24 := by
  have h : ∀ a b c : UInt8, ((a.toUInt32 <<< 16) ||| (b.toUInt32 <<< 8) ||| c.toUInt32) < (16777216 : UInt32) := by
    intro a b c; bv_decide
  have := h (src.getD (3 * j) 0) (src.getD (3 * j + 1) 0) (src.getD (3 * j + 2) 0)
  rw [UInt32.lt_iff_toNat_lt] at this
  simpa [encWord] using this

theorem sixbit_lt (w : UInt32) (hw : w.toNat < 2 ^ 24) (t : Nat) : (sixbit w t).toNat < 64 := by
  have hw' : w < (16777216 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt]; simpa using hw
  have h0 : w >>> 18 < (64 : UInt32) := by bv_decide
  have h1 : (w >>> 12) &&& 63 < (64 : UInt32) := by bv_decide
  have h2 : (w >>> 6) &&& 63 < (64 : UInt32) := by bv_decide
  have h3 : w &&& 63 < (64 : UInt32) := by bv_decide
  unfold sixbit
  split
  · rw [UInt32.lt_iff_toNat_lt] at h0; simpa using h0
  · split
    · rw [UInt32.lt_iff_toNat_lt] at h1; simpa using h1
    · split
      · rw [UInt32.lt_iff_toNat_lt] at h2; simpa using h2
      · rw [UInt32.lt_iff_toNat_lt] at h3; simpa using h3

/-- Adding a small constant to a `UInt32` that stays in range. -/
theorem uadd (i c : UInt32) (n : Nat) (hc : c.toNat = n) (h : i.toNat + n < 2 ^ 32) : (i + c).toNat = i.toNat + n := by
  rw [UInt32.toNat_add, hc]; exact Nat.mod_eq_of_lt h

theorem b64_encode_loop (src symbols : Array UInt8) (g : Nat) (hg : src.size / 3 = g) (hsrc : src.size + 4 < 2 ^ 32)
    (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32),
      4 * g ≤ dst.size → dst.size < 2 ^ 32 → i.toNat ≤ 3 * g → i.toNat % 3 = 0 → out.toNat = 4 * (i.toNat / 3) →
      g - i.toNat / 3 < fuel →
      ∃ dst' i' out', base64_encode.loop1 dst src symbols i out fuel = some (dst', i', out') ∧
        dst'.size = dst.size ∧ i'.toNat = 3 * g ∧ out'.toNat = 4 * g ∧
        ∀ k, dst'.getD k 0 = if out.toNat ≤ k ∧ k < 4 * g then encSym src symbols k else dst.getD k 0 := by
  induction fuel with
  | zero => intro dst i out _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out hdst hsmall hi hi3 hout hf
    unfold base64_encode.loop1
    have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
    have hi3' : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
    by_cases hlt : i.toNat / 3 < g
    · have hc : decide (i + 3 ≤ src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.le_iff_toNat_le, hsz, hi3']; omega
      simp only [hc, ↓reduceIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
      have ho1 : (out + 1).toNat = out.toNat + 1 := uadd out 1 1 (by decide) (by omega)
      have ho2 : (out + 2).toNat = out.toNat + 2 := uadd out 2 2 (by decide) (by omega)
      have ho3 : (out + 3).toNat = out.toNat + 3 := uadd out 3 3 (by decide) (by omega)
      have hout4 : (out + 4).toNat = out.toNat + 4 := uadd out 4 4 (by decide) (by omega)
      have ho4 : (out + 4).toNat = 4 * ((i + 3).toNat / 3) := by
        rw [hout4, hout, hi3']; omega
      -- the word this iteration reads is the word of group i/3
      obtain ⟨j, hj⟩ : ∃ j, j = i.toNat / 3 := ⟨_, rfl⟩
      have hij : i.toNat = 3 * j := by omega
      have hword : (((src.getD i.toNat 0).toUInt32 <<< (16 : UInt32)) ||| ((src.getD (i + 1).toNat 0).toUInt32 <<< (8 : UInt32))) |||
          (src.getD (i + 2).toNat 0).toUInt32 = encWord src j := by
        unfold encWord; rw [hi1, hi2, hij]
      rw [hword]
      obtain ⟨dst', i', out', heq, hsize, hi', hout', hget⟩ :=
        ih ((((dst.setIfInBounds out.toNat (symbols.getD (encWord src j >>> 18).toNat 0)).setIfInBounds
              (out + 1).toNat (symbols.getD ((encWord src j >>> 12) &&& 63).toNat 0)).setIfInBounds
              (out + 2).toNat (symbols.getD ((encWord src j >>> 6) &&& 63).toNat 0)).setIfInBounds
              (out + 3).toNat (symbols.getD (encWord src j &&& 63).toNat 0))
          (i + 3) (out + 4)
          (by simp only [Array.size_setIfInBounds]; exact hdst)
          (by simp only [Array.size_setIfInBounds]; exact hsmall)
          (by rw [hi3']; omega) (by rw [hi3']; omega) ho4 (by rw [hi3']; omega)
      refine ⟨dst', i', out', heq, by rw [hsize]; simp only [Array.size_setIfInBounds], hi', hout', ?_⟩
      intro k
      rw [hget k]
      by_cases hk : (out + 4).toNat ≤ k ∧ k < 4 * g
      · rw [if_pos hk, if_pos ⟨by omega, hk.2⟩]
      · rw [if_neg hk]
        have hk4 : k < out.toNat + 4 ∨ 4 * g ≤ k := by omega
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds]
        rw [ho1, ho2, ho3]
        have hkj : ∀ t, t < 4 → k = out.toNat + t → encSym src symbols k = symbols.getD (sixbit (encWord src j) t).toNat 0 := by
          intro t ht hkt
          unfold encSym
          rw [hkt, hout, ← hj, show (4 * j + t) / 4 = j by omega, show (4 * j + t) % 4 = t by omega]
        by_cases h3 : out.toNat + 3 = k
        · rw [if_pos h3, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, hkj 3 (by omega) h3.symm]; rfl
        · rw [if_neg h3]
          by_cases h2 : out.toNat + 2 = k
          · rw [if_pos h2, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, hkj 2 (by omega) h2.symm]; rfl
          · rw [if_neg h2]
            by_cases h1 : out.toNat + 1 = k
            · rw [if_pos h1, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, hkj 1 (by omega) h1.symm]; rfl
            · rw [if_neg h1]
              by_cases h0 : out.toNat = k
              · rw [if_pos h0, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, hkj 0 (by omega) h0.symm]; rfl
              · rw [if_neg h0, ← Array.getD_eq_getD_getElem?, if_neg (by omega)]
    · have hc : decide (i + 3 ≤ src.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.le_iff_toNat_le, hsz, hi3']; omega
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine ⟨dst, i, out, rfl, rfl, by omega, by rw [hout]; omega, ?_⟩
      intro k
      rw [if_neg (by omega)]

/-- The symbols the encoder writes for `n` bytes (padding excluded). -/
def symCount (n : Nat) : Nat := 4 * (n / 3) + (if n % 3 = 0 then 0 else n % 3 + 1)

/-- The encoded size the library reports: the symbols, padded to a multiple of four when asked. -/
def encSize (n : Nat) (pad : Bool) : Nat := 4 * (n / 3) + (if n % 3 = 0 then 0 else if pad then 4 else n % 3 + 1)

theorem symCount_le (n : Nat) (pad : Bool) : symCount n ≤ encSize n pad := by
  unfold symCount encSize
  split <;> (try split) <;> omega

theorem encSize_lt (n : Nat) (pad : Bool) (hn : n ≤ 3221225469) : encSize n pad < 2 ^ 32 := by
  unfold encSize
  split <;> (try split) <;> omega

theorem encoded_size_spec (n : Nat) (pad : Bool) (fuel : Nat) (hn : n ≤ 3221225469) :
    base64_encoded_size n.toUInt32 pad fuel = some (.Ok (encSize n pad).toUInt32) := by
  have hn' : (n.toUInt32).toNat = n := toUInt32_toNat_of_lt _ (by omega)
  have hnot : decide (n.toUInt32 > (3221225469 : UInt32)) = false := by
    apply decide_eq_false
    intro h
    have := UInt32.lt_iff_toNat_lt.mp h
    rw [hn', show (3221225469 : UInt32).toNat = 3221225469 by decide] at this
    omega
  have hgroups : (n.toUInt32 / 3).toNat = n / 3 := by
    rw [UInt32.toNat_div, hn', show (3 : UInt32).toNat = 3 by decide]
  have hrest : (n.toUInt32 % 3).toNat = n % 3 := by
    rw [UInt32.toNat_mod, hn', show (3 : UInt32).toNat = 3 by decide]
  have hsize := encSize_lt n pad hn
  unfold base64_encoded_size
  simp only [hnot, Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq,
    Result_u32_EncodingError.Ok.injEq]
  apply UInt32.toNat.inj
  rw [toUInt32_toNat_of_lt _ hsize]
  unfold encSize
  by_cases h0 : n % 3 = 0
  · have hb : (n.toUInt32 % 3 == 0) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h0]; decide
    simp only [hb, ↓reduceIte, if_pos h0]
    rw [UInt32.toNat_add, UInt32.toNat_mul, hgroups, show (4 : UInt32).toNat = 4 by decide,
      show (0 : UInt32).toNat = 0 by decide]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · have hb : (n.toUInt32 % 3 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg UInt32.toNat h; rw [hrest, show (0 : UInt32).toNat = 0 by decide] at this; exact h0 this
    simp only [hb, Bool.false_eq_true, ↓reduceIte, if_neg h0]
    cases pad
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [UInt32.toNat_add, UInt32.toNat_mul, hgroups, show (4 : UInt32).toNat = 4 by decide, UInt32.toNat_add,
        hrest, show (1 : UInt32).toNat = 1 by decide]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [↓reduceIte]
      rw [UInt32.toNat_add, UInt32.toNat_mul, hgroups, show (4 : UInt32).toNat = 4 by decide]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- A read past the end of a source is the default. -/
theorem getD_past (src : Array UInt8) (k : Nat) (h : src.size ≤ k) : src.getD k 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none_iff.mpr h]; rfl

theorem tail_word1 (src : Array UInt8) (g : Nat) (h : src.size = 3 * g + 1) :
    (src.getD (3 * g) 0).toUInt32 <<< (16 : UInt32) = encWord src g := by
  unfold encWord
  rw [getD_past src (3 * g + 1) (by omega), getD_past src (3 * g + 2) (by omega)]
  bv_decide

theorem tail_word2 (src : Array UInt8) (g : Nat) (h : src.size = 3 * g + 2) :
    ((src.getD (3 * g) 0).toUInt32 <<< (16 : UInt32)) ||| ((src.getD (3 * g + 1) 0).toUInt32 <<< (8 : UInt32)) = encWord src g := by
  unfold encWord
  rw [getD_past src (3 * g + 2) (by omega)]
  bv_decide

/-- `base64_encode` into a destination that holds the encoding: the size is
reported, the symbols are the six-bit fields of the source words in order,
the padding follows, and nothing else moves. -/
theorem b64_encode_spec (src dst : Array UInt8) (url pad : Bool) (fuel : Nat)
    (hsrc : src.size ≤ 3221225469) (hdst : encSize src.size pad ≤ dst.size) (hdst_small : dst.size < 2 ^ 32)
    (hf : src.size / 3 < fuel) :
    ∃ dst', base64_encode dst src url pad fuel = some (.Ok (encSize src.size pad).toUInt32, dst') ∧
      dst'.size = dst.size ∧
      (∀ k, k < symCount src.size → dst'.getD k 0 = encSym src (b64symbols url) k) ∧
      (∀ k, symCount src.size ≤ k → k < encSize src.size pad → dst'.getD k 0 = 61) ∧
      (∀ k, encSize src.size pad ≤ k → dst'.getD k 0 = dst.getD k 0) := by
  obtain ⟨g, hg⟩ : ∃ g, g = src.size / 3 := ⟨_, rfl⟩
  have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
  have hsize := encSize_lt src.size pad hsrc
  have hneeded : ((encSize src.size pad).toUInt32).toNat = encSize src.size pad := toUInt32_toNat_of_lt _ hsize
  have hfits : decide ((encSize src.size pad).toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false
    intro h
    have := UInt32.lt_iff_toNat_lt.mp h
    rw [hneeded, toUInt32_toNat_of_lt _ hdst_small] at this
    omega
  have hsym : (if url then BASE64_URL_SYMBOLS else BASE64_STD_SYMBOLS) = b64symbols url := rfl
  have h4g : 4 * g ≤ dst.size := by
    have := symCount_le src.size pad
    unfold symCount at this; omega
  obtain ⟨dst1, i1, out1, hloop, hsize1, hi1, hout1, hget1⟩ :=
    b64_encode_loop src (b64symbols url) g hg.symm (by omega) fuel dst 0 0 h4g hdst_small (by simp)
      (by simp) (by simp) (by simp; omega)
  have hrest : (src.size.toUInt32 - i1).toNat = src.size % 3 := by
    rw [UInt32.toNat_sub_of_le, hsz, hi1]
    · omega
    · rw [UInt32.le_iff_toNat_le, hsz, hi1]; omega
  have hout1' : out1 = (4 * g).toUInt32 := by
    apply UInt32.toNat.inj; rw [hout1, toUInt32_toNat_of_lt _ (by omega)]
  unfold base64_encode
  rw [encoded_size_spec src.size pad fuel hsrc]
  simp only [Option.pure_def, Option.bind_some, hfits, Bool.false_eq_true, ↓reduceIte, hsym, hloop,
    Option.bind_eq_bind]
  -- the tail
  have hg3 : 3 * g ≤ src.size := by omega
  have hsymcount : symCount src.size = 4 * g + (if src.size % 3 = 0 then 0 else src.size % 3 + 1) := by
    unfold symCount; rw [hg]
  have hencsize : encSize src.size pad = 4 * g + (if src.size % 3 = 0 then 0 else if pad then 4 else src.size % 3 + 1) := by
    unfold encSize; rw [hg]
  have hi1' : i1 = (3 * g).toUInt32 := by
    apply UInt32.toNat.inj; rw [hi1, toUInt32_toNat_of_lt _ (by omega)]
  have hi1n : i1.toNat = 3 * g := hi1
  have ho1 : (out1 + 1).toNat = 4 * g + 1 := by rw [uadd out1 1 1 (by decide) (by omega), hout1]
  have ho2 : (out1 + 2).toNat = 4 * g + 2 := by rw [uadd out1 2 2 (by decide) (by omega), hout1]
  have ho3 : (out1 + 3).toNat = 4 * g + 3 := by rw [uadd out1 3 3 (by decide) (by omega), hout1]
  have hi1p : (i1 + 1).toNat = 3 * g + 1 := by rw [uadd i1 1 1 (by decide) (by omega), hi1]
  -- the three remainders
  rcases (show src.size % 3 = 0 ∨ src.size % 3 = 1 ∨ src.size % 3 = 2 by omega) with h0 | h1 | h2
  · have hne1 : (src.size.toUInt32 - i1 == 1) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, h0] at this; exact absurd this (by decide)
    have hne2 : (src.size.toUInt32 - i1 == 2) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, h0] at this; exact absurd this (by decide)
    simp only [hne1, hne2, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
    refine ⟨_, rfl, hsize1, ?_, ?_, ?_⟩
    · intro k hk; rw [hget1 k, if_pos ⟨by simp, by rw [hsymcount, if_pos h0] at hk; omega⟩]
    · intro k hk1 hk2; rw [hsymcount, if_pos h0] at hk1; rw [hencsize, if_pos h0] at hk2; omega
    · intro k hk; rw [hget1 k, if_neg (by rw [hencsize, if_pos h0] at hk; omega)]
  · -- one byte left: two symbols, then two pads when asked
    have heq1 : (src.size.toUInt32 - i1 == 1) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h1]; decide
    have hne2 : (src.size.toUInt32 - i1 == 2) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, h1] at this; exact absurd this (by decide)
    have hword : (src.getD i1.toNat 0).toUInt32 <<< (16 : UInt32) = encWord src g := by
      rw [hi1n]; exact tail_word1 src g (by omega)
    have hlt24 := encWord_lt src g
    simp only [heq1, hne2, Bool.false_eq_true, ↓reduceIte, hword, Option.bind_some]
    have hsym0 : (b64symbols url).getD (encWord src g >>> 18).toNat 0 = encSym src (b64symbols url) (4 * g) := by
      unfold encSym sixbit; rw [show 4 * g / 4 = g by omega, show 4 * g % 4 = 0 by omega]; simp
    have hsym1 : (b64symbols url).getD ((encWord src g >>> 12) &&& 63).toNat 0 = encSym src (b64symbols url) (4 * g + 1) := by
      unfold encSym sixbit; rw [show (4 * g + 1) / 4 = g by omega, show (4 * g + 1) % 4 = 1 by omega]; simp
    rw [hsym0, hsym1]
    have hcount : symCount src.size = 4 * g + 2 := by rw [hsymcount, if_neg (by omega), h1]
    cases pad
    · have henc : encSize src.size false = 4 * g + 2 := by rw [hencsize, if_neg (by omega), h1]; simp
      simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some]
      refine ⟨_, rfl, by simp [Array.size_setIfInBounds, hsize1], ?_, ?_, ?_⟩
      · intro k hk
        rw [hcount] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1]
        by_cases hk1 : 4 * g + 1 = k
        · rw [if_pos hk1, if_pos (by omega), Option.getD_some, ← hk1]
        · rw [if_neg hk1]
          by_cases hk0 : 4 * g = k
          · rw [if_pos hk0, if_pos (by omega), Option.getD_some, ← hk0]
          · rw [if_neg hk0, ← Array.getD_eq_getD_getElem?, hget1 k, if_pos ⟨by simp, by omega⟩]
      · intro k hk1 hk2; rw [hcount] at hk1; rw [henc] at hk2; omega
      · intro k hk
        rw [henc] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1]
        rw [if_neg (by omega), if_neg (by omega), ← Array.getD_eq_getD_getElem?, hget1 k, if_neg (by omega)]
    · have henc : encSize src.size true = 4 * g + 4 := by rw [hencsize, if_neg (by omega)]; simp
      simp only [↓reduceIte, Option.bind_some]
      refine ⟨_, rfl, by simp [Array.size_setIfInBounds, hsize1], ?_, ?_, ?_⟩
      · intro k hk
        rw [hcount] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1, ho2, ho3]
        rw [if_neg (by omega), if_neg (by omega)]
        by_cases hk1 : 4 * g + 1 = k
        · rw [if_pos hk1, if_pos (by omega), Option.getD_some, ← hk1]
        · rw [if_neg hk1]
          by_cases hk0 : 4 * g = k
          · rw [if_pos hk0, if_pos (by omega), Option.getD_some, ← hk0]
          · rw [if_neg hk0, ← Array.getD_eq_getD_getElem?, hget1 k, if_pos ⟨by simp, by omega⟩]
      · intro k hk1 hk2
        rw [hcount] at hk1; rw [henc] at hk2
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1, ho2, ho3]
        by_cases hk3 : 4 * g + 3 = k
        · rw [if_pos hk3, if_pos (by omega), Option.getD_some]
        · rw [if_neg hk3, if_pos (by omega), if_pos (by omega), Option.getD_some]
      · intro k hk
        rw [henc] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1, ho2, ho3]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          ← Array.getD_eq_getD_getElem?, hget1 k, if_neg (by omega)]
  · -- two bytes left: three symbols, then one pad when asked
    have hne1 : (src.size.toUInt32 - i1 == 1) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, h2] at this; exact absurd this (by decide)
    have heq2 : (src.size.toUInt32 - i1 == 2) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h2]; decide
    have hword : ((src.getD i1.toNat 0).toUInt32 <<< (16 : UInt32)) ||| ((src.getD (i1 + 1).toNat 0).toUInt32 <<< (8 : UInt32)) =
        encWord src g := by
      rw [hi1n, hi1p]; exact tail_word2 src g (by omega)
    simp only [hne1, heq2, Bool.false_eq_true, ↓reduceIte, hword, Option.bind_some]
    have hsym0 : (b64symbols url).getD (encWord src g >>> 18).toNat 0 = encSym src (b64symbols url) (4 * g) := by
      unfold encSym sixbit; rw [show 4 * g / 4 = g by omega, show 4 * g % 4 = 0 by omega]; simp
    have hsym1 : (b64symbols url).getD ((encWord src g >>> 12) &&& 63).toNat 0 = encSym src (b64symbols url) (4 * g + 1) := by
      unfold encSym sixbit; rw [show (4 * g + 1) / 4 = g by omega, show (4 * g + 1) % 4 = 1 by omega]; simp
    have hsym2 : (b64symbols url).getD ((encWord src g >>> 6) &&& 63).toNat 0 = encSym src (b64symbols url) (4 * g + 2) := by
      unfold encSym sixbit; rw [show (4 * g + 2) / 4 = g by omega, show (4 * g + 2) % 4 = 2 by omega]; simp
    rw [hsym0, hsym1, hsym2]
    have hcount : symCount src.size = 4 * g + 3 := by rw [hsymcount, if_neg (by omega), h2]
    cases pad
    · have henc : encSize src.size false = 4 * g + 3 := by rw [hencsize, if_neg (by omega), h2]; simp
      simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some]
      refine ⟨_, rfl, by simp [Array.size_setIfInBounds, hsize1], ?_, ?_, ?_⟩
      · intro k hk
        rw [hcount] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1, ho2]
        by_cases hk2 : 4 * g + 2 = k
        · rw [if_pos hk2, if_pos (by omega), Option.getD_some, ← hk2]
        · rw [if_neg hk2]
          by_cases hk1 : 4 * g + 1 = k
          · rw [if_pos hk1, if_pos (by omega), Option.getD_some, ← hk1]
          · rw [if_neg hk1]
            by_cases hk0 : 4 * g = k
            · rw [if_pos hk0, if_pos (by omega), Option.getD_some, ← hk0]
            · rw [if_neg hk0, ← Array.getD_eq_getD_getElem?, hget1 k, if_pos ⟨by simp, by omega⟩]
      · intro k hk1 hk2; rw [hcount] at hk1; rw [henc] at hk2; omega
      · intro k hk
        rw [henc] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1, ho2]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), ← Array.getD_eq_getD_getElem?, hget1 k,
          if_neg (by omega)]
    · have henc : encSize src.size true = 4 * g + 4 := by rw [hencsize, if_neg (by omega)]; simp
      simp only [↓reduceIte, Option.bind_some]
      refine ⟨_, rfl, by simp [Array.size_setIfInBounds, hsize1], ?_, ?_, ?_⟩
      · intro k hk
        rw [hcount] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1, ho2, ho3]
        rw [if_neg (by omega)]
        by_cases hk2 : 4 * g + 2 = k
        · rw [if_pos hk2, if_pos (by omega), Option.getD_some, ← hk2]
        · rw [if_neg hk2]
          by_cases hk1 : 4 * g + 1 = k
          · rw [if_pos hk1, if_pos (by omega), Option.getD_some, ← hk1]
          · rw [if_neg hk1]
            by_cases hk0 : 4 * g = k
            · rw [if_pos hk0, if_pos (by omega), Option.getD_some, ← hk0]
            · rw [if_neg hk0, ← Array.getD_eq_getD_getElem?, hget1 k, if_pos ⟨by simp, by omega⟩]
      · intro k hk1 hk2
        rw [hcount] at hk1; rw [henc] at hk2
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, ho3]
        rw [if_pos (by omega), if_pos (by omega), Option.getD_some]
      · intro k hk
        rw [henc] at hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds, hsize1, hout1, ho1, ho2, ho3]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          ← Array.getD_eq_getD_getElem?, hget1 k, if_neg (by omega)]

/-! ## The 24-bit word identities -/

theorem word_reassemble (w : UInt32) (hw : w < 16777216) :
    ((w >>> 18) <<< 18) ||| (((w >>> 12) &&& 63) <<< 12) ||| (((w >>> 6) &&& 63) <<< 6) ||| (w &&& 63) = w := by
  bv_decide

theorem bytes_of_word (a b c : UInt8) :
    let w : UInt32 := ((a.toUInt32 <<< 16) ||| (b.toUInt32 <<< 8)) ||| c.toUInt32
    (w >>> 16).toUInt8 = a ∧ (w >>> 8).toUInt8 = b ∧ w.toUInt8 = c := by
  intro w
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

theorem tail1_byte (a : UInt8) :
    let w : UInt32 := a.toUInt32 <<< 16
    ((((w >>> 18) <<< 18) ||| (((w >>> 12) &&& 63) <<< 12)) >>> 16).toUInt8 = a ∧
    (((w >>> 12) &&& 63) &&& 15) = 0 := by
  intro w
  refine ⟨?_, ?_⟩ <;> bv_decide

theorem tail2_bytes (a b : UInt8) :
    let w : UInt32 := (a.toUInt32 <<< 16) ||| (b.toUInt32 <<< 8)
    let w3 : UInt32 := ((w >>> 18) <<< 18) ||| (((w >>> 12) &&& 63) <<< 12) ||| (((w >>> 6) &&& 63) <<< 6)
    (w3 >>> 16).toUInt8 = a ∧ (w3 >>> 8).toUInt8 = b ∧ (((w >>> 6) &&& 63) &&& 3) = 0 := by
  intro w w3
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-! ## The encoded text, as the decoder sees it -/

/-- What `b64_encode_spec` establishes about the encoding `enc` of `src`. -/
structure Encoded (src enc : Array UInt8) (url pad : Bool) : Prop where
  size : enc.size = encSize src.size pad
  syms : ∀ k, k < symCount src.size → enc.getD k 0 = encSym src (b64symbols url) k
  pads : ∀ k, symCount src.size ≤ k → k < encSize src.size pad → enc.getD k 0 = 61

theorem encSym_value (src : Array UInt8) (url : Bool) (k : Nat) :
    symValue url (encSym src (b64symbols url) k) = sixbit (encWord src (k / 4)) (k % 4) := by
  unfold encSym
  exact symValue_roundtrip url _ (sixbit_lt _ (encWord_lt src (k / 4)) _)

theorem encSym_lt (src : Array UInt8) (url : Bool) (k : Nat) : (symValue url (encSym src (b64symbols url) k)).toNat < 64 := by
  rw [encSym_value]; exact sixbit_lt _ (encWord_lt src (k / 4)) _

theorem encSym_ne_pad (src : Array UInt8) (url : Bool) (k : Nat) : encSym src (b64symbols url) k ≠ 61 := by
  unfold encSym
  exact b64_not_pad url _ (sixbit_lt _ (encWord_lt src (k / 4)) _)

theorem symCount_eq (n : Nat) : symCount n = 4 * (n / 3) + (if n % 3 = 0 then 0 else n % 3 + 1) := rfl

/-- The padding strip: the count of trailing `=` is exactly the padding written. -/
theorem unpad_loop (src enc : Array UInt8) (url pad : Bool) (he : Encoded src enc url pad) (hsrc : src.size ≤ 3221225469)
    (fuel : Nat) :
    ∀ pads : UInt32, pads.toNat ≤ encSize src.size pad - symCount src.size →
      (encSize src.size pad - symCount src.size) - pads.toNat < fuel →
      base64_unpadded_length.loop1 enc pads fuel = some (encSize src.size pad - symCount src.size).toUInt32 := by
  have hle := symCount_le src.size pad
  have hsize := encSize_lt src.size pad hsrc
  have hp2 : encSize src.size pad - symCount src.size ≤ 2 := by
    unfold encSize symCount; split <;> (try split) <;> omega
  have hsz : (enc.size.toUInt32).toNat = enc.size := toUInt32_toNat_of_lt _ (by rw [he.size]; exact hsize)
  induction fuel with
  | zero => intro pads _ hf; omega
  | succ fuel ih =>
    intro pads hpads hf
    unfold base64_unpadded_length.loop1
    by_cases hlt : pads.toNat < encSize src.size pad - symCount src.size
    · -- a pad byte remains at the end
      have hidx : ((enc.size.toUInt32 - 1) - pads).toNat = enc.size - 1 - pads.toNat := by
        rw [UInt32.toNat_sub_of_le, UInt32.toNat_sub_of_le, hsz, show (1 : UInt32).toNat = 1 by decide]
        · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; rw [he.size]; omega
        · rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, hsz, show (1 : UInt32).toNat = 1 by decide]
          · rw [he.size]; omega
          · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; rw [he.size]; omega
      have hbyte : enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 = 61 := by
        rw [hidx]; apply he.pads <;> rw [he.size] <;> omega
      have hc1 : decide (pads < enc.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsz, he.size]; omega
      have hc2 : decide (pads < (2 : UInt32)) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, show (2 : UInt32).toNat = 2 by decide]; omega
      have hc3 : (enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 == 61) = true := by rw [beq_iff_eq]; exact hbyte
      simp only [hc1, hc2, hc3, Bool.and_self, ↓reduceIte]
      have hp1 : (pads + 1).toNat = pads.toNat + 1 := uadd pads 1 1 (by decide) (by omega)
      exact ih (pads + 1) (by rw [hp1]; omega) (by rw [hp1]; omega)
    · -- the padding is exhausted: stop with the count
      have hpe : pads.toNat = encSize src.size pad - symCount src.size := by omega
      have hstop : ((decide (pads < enc.size.toUInt32) && decide (pads < (2 : UInt32))) &&
          (enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 == 61)) = false := by
        by_cases hsym0 : symCount src.size = 0
        · -- nothing to read: the text is all padding or empty
          have hn0 : src.size = 0 := by unfold symCount at hsym0; split at hsym0 <;> omega
          have henc0 : encSize src.size pad = 0 := by unfold encSize; rw [hn0]; simp
          have : decide (pads < enc.size.toUInt32) = false := by
            apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz, he.size, henc0]; omega
          exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inl this)))
        · by_cases h2 : pads.toNat = 2
          · have : decide (pads < (2 : UInt32)) = false := by
              apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, show (2 : UInt32).toNat = 2 by decide]; omega
            exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inr this)))
          · have hidx : ((enc.size.toUInt32 - 1) - pads).toNat = enc.size - 1 - pads.toNat := by
              rw [UInt32.toNat_sub_of_le, UInt32.toNat_sub_of_le, hsz, show (1 : UInt32).toNat = 1 by decide]
              · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; rw [he.size]; omega
              · rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, hsz, show (1 : UInt32).toNat = 1 by decide]
                · rw [he.size]; omega
                · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; rw [he.size]; omega
            have hbyte : enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 = encSym src (b64symbols url) (symCount src.size - 1) := by
              rw [hidx, he.size, hpe, show encSize src.size pad - 1 - (encSize src.size pad - symCount src.size) = symCount src.size - 1 by omega]
              exact he.syms _ (by omega)
            have : (enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 == 61) = false := by
              rw [beq_eq_false_iff_ne, hbyte]; exact encSym_ne_pad src url _
            exact Bool.and_eq_false_iff.mpr (Or.inr this)
      rw [if_neg (by simpa using hstop)]
      simp only [Option.pure_def, Option.some.injEq]
      apply UInt32.toNat.inj
      rw [hpe, toUInt32_toNat_of_lt _ (by omega)]

theorem unpadded_length_spec (src enc : Array UInt8) (url pad : Bool) (he : Encoded src enc url pad)
    (hsrc : src.size ≤ 3221225469) (fuel : Nat) (hf : 3 < fuel) :
    base64_unpadded_length enc fuel = some (.Ok (symCount src.size).toUInt32) := by
  have hle := symCount_le src.size pad
  have hsize := encSize_lt src.size pad hsrc
  have hsz : (enc.size.toUInt32).toNat = enc.size := toUInt32_toNat_of_lt _ (by rw [he.size]; exact hsize)
  have hp2 : encSize src.size pad - symCount src.size ≤ 2 := by
    unfold encSize symCount; split <;> (try split) <;> omega
  have hloop := unpad_loop src enc url pad he hsrc fuel 0 (by simp) (by simp; omega)
  unfold base64_unpadded_length
  simp only [hloop, Option.pure_def, bind, Option.bind]
  have hpads : ((encSize src.size pad - symCount src.size).toUInt32).toNat = encSize src.size pad - symCount src.size :=
    toUInt32_toNat_of_lt _ (by omega)
  have hbody : (enc.size.toUInt32 - (encSize src.size pad - symCount src.size).toUInt32).toNat = symCount src.size := by
    rw [UInt32.toNat_sub_of_le, hsz, hpads, he.size]
    · omega
    · rw [UInt32.le_iff_toNat_le, hsz, hpads, he.size]; omega
  have hbody' : enc.size.toUInt32 - (encSize src.size pad - symCount src.size).toUInt32 = (symCount src.size).toUInt32 := by
    apply UInt32.toNat.inj; rw [hbody, toUInt32_toNat_of_lt _ (by omega)]
  rw [hbody']
  -- the padding is consistent: either none, or the text is a multiple of four ending in two or three symbols
  have hbad : ((decide ((encSize src.size pad - symCount src.size).toUInt32 > (0 : UInt32))) &&
      ((((enc.size.toUInt32 % 4) != 0) || ((symCount src.size).toUInt32 % 4 == 0)) || ((symCount src.size).toUInt32 % 4 == 1))) = false := by
    by_cases hp0 : encSize src.size pad - symCount src.size = 0
    · have : decide ((encSize src.size pad - symCount src.size).toUInt32 > (0 : UInt32)) = false := by
        apply decide_eq_false; rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hpads, hp0]; simp
      simp [this]
    · -- padding was written: pad = true and the byte count is not a multiple of three
      have hpad : pad = true ∧ src.size % 3 ≠ 0 := by
        refine ⟨?_, ?_⟩
        · cases pad
          · exfalso; apply hp0
            by_cases h3 : src.size % 3 = 0 <;> simp [encSize, symCount, h3]
          · rfl
        · intro h3; apply hp0; simp [encSize, symCount, h3]
      have hsz4 : enc.size.toUInt32 % 4 = 0 := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_mod, hsz, he.size, show (4 : UInt32).toNat = 4 by decide, show (0 : UInt32).toNat = 0 by decide]
        unfold encSize; rw [if_neg hpad.2, if_pos hpad.1]; omega
      have hrest : ((symCount src.size).toUInt32 % 4).toNat = src.size % 3 + 1 := by
        rw [UInt32.toNat_mod, toUInt32_toNat_of_lt _ (by omega), show (4 : UInt32).toNat = 4 by decide]
        unfold symCount; rw [if_neg hpad.2]; omega
      have h1 : ((enc.size.toUInt32 % 4) != 0) = false := by rw [hsz4]; decide
      have h2 : ((symCount src.size).toUInt32 % 4 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest] at this; simp at this
      have h3 : ((symCount src.size).toUInt32 % 4 == 1) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest] at this
        simp at this; omega
      simp [h1, h2, h3]
  simp [hbad]

/-! ## The validation scan -/

/-- Every symbol below `body` has a value below 64. -/
def AllSymbols (enc values : Array UInt8) (body : Nat) : Prop :=
  ∀ k, k < body → (values.getD ((enc.getD k 0).toUInt32).toNat 0).toNat < 64

theorem or_lt64 {a b : Nat} (ha : a < 64) (hb : b < 64) : a ||| b < 64 :=
  Nat.or_lt_two_pow (n := 6) ha hb

theorem b64_scan_loop1 (enc values : Array UInt8) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32)
    (hv : AllSymbols enc values body.toNat) (fuel : Nat) :
    ∀ (acc i : UInt32), acc.toNat < 64 → i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      ∃ acc' i', base64_scan.loop1 enc body values acc i fuel = some (acc', i') ∧
        acc'.toNat < 64 ∧ i'.toNat ≤ body.toNat := by
  induction fuel with
  | zero => intro acc i _ _ hf; omega
  | succ fuel ih =>
    intro acc i hacc hi hf
    unfold base64_scan.loop1
    have hi4 : (i + 4).toNat = i.toNat + 4 := uadd i 4 4 (by decide) (by omega)
    by_cases hle : i.toNat + 4 ≤ body.toNat
    · have hc : decide (i + 4 ≤ body) = true := by
        apply decide_eq_true; rw [UInt32.le_iff_toNat_le, hi4]; exact hle
      simp only [hc, ↓reduceIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
      have hi3 : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
      have v0 := hv i.toNat (by omega)
      have v1 := hv (i.toNat + 1) (by omega)
      have v2 := hv (i.toNat + 2) (by omega)
      have v3 := hv (i.toNat + 3) (by omega)
      rw [← hi1] at v1; rw [← hi2] at v2; rw [← hi3] at v3
      apply ih _ (i + 4) _ (by rw [hi4]; exact hle) (by omega)
      simp only [UInt32.toNat_or, UInt8.toNat_toUInt32]
      exact or_lt64 (or_lt64 (or_lt64 (or_lt64 hacc v0) v1) v2) v3
    · have hc : decide (i + 4 ≤ body) = false := by
        apply decide_eq_false; rw [UInt32.le_iff_toNat_le, hi4]; exact hle
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨acc, i, rfl, hacc, hi⟩

theorem b64_scan_loop2 (enc values : Array UInt8) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32)
    (hv : AllSymbols enc values body.toNat) (fuel : Nat) :
    ∀ (acc i : UInt32), acc.toNat < 64 → i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      ∃ acc' i', base64_scan.loop2 enc body values acc i fuel = some (acc', i') ∧ acc'.toNat < 64 := by
  induction fuel with
  | zero => intro acc i _ _ hf; omega
  | succ fuel ih =>
    intro acc i hacc hi hf
    unfold base64_scan.loop2
    by_cases hlt : i.toNat < body.toNat
    · have hc : decide (i < body) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, ↓reduceIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have v0 := hv i.toNat hlt
      apply ih _ (i + 1) _ (by rw [hi1]; omega) (by omega)
      rw [UInt32.toNat_or, UInt8.toNat_toUInt32]
      exact or_lt64 hacc v0
    · have hc : decide (i < body) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨acc, i, rfl, hacc⟩

theorem b64_scan_spec (enc : Array UInt8) (url : Bool) (body : UInt32) (hsize : body.toNat + 4 < 2 ^ 32)
    (hv : AllSymbols enc (b64values url) body.toNat) (fuel : Nat) (hf : body.toNat < fuel) :
    ∃ acc, base64_scan enc body url fuel = some acc ∧ acc.toNat < 64 := by
  obtain ⟨acc1, i1, h1, hacc1, hi1⟩ := b64_scan_loop1 enc (b64values url) body hsize hv fuel 0 0 (by decide) (by simp) (by simp; omega)
  obtain ⟨acc2, i2, h2, hacc2⟩ := b64_scan_loop2 enc (b64values url) body hsize hv fuel acc1 i1 hacc1 hi1 (by omega)
  refine ⟨acc2, ?_, hacc2⟩
  unfold base64_scan
  have : (if url then BASE64_URL_VALUES else BASE64_STD_VALUES) = b64values url := rfl
  rw [this]
  simp [h1, h2]

/-! ## The decoded size -/

theorem encoded_symbols_valid (src enc : Array UInt8) (url pad : Bool) (he : Encoded src enc url pad) :
    AllSymbols enc (b64values url) (symCount src.size) := by
  intro k hk
  rw [he.syms k hk]
  have := encSym_lt src url k
  unfold symValue at this
  rw [UInt8.toNat_toUInt32] at this
  exact this

theorem decoded_size_spec (src enc : Array UInt8) (url pad : Bool) (he : Encoded src enc url pad)
    (hsrc : src.size + 8 < 2 ^ 31) (fuel : Nat) (hf : 2 * src.size + 16 < fuel) :
    base64_decoded_size enc url fuel = some (.Ok src.size.toUInt32) := by
  have hsrc' : src.size ≤ 3221225469 := by omega
  have hle := symCount_le src.size pad
  have hsize := encSize_lt src.size pad hsrc'
  have hcount : symCount src.size < 2 ^ 32 := by omega
  have hcount' : ((symCount src.size).toUInt32).toNat = symCount src.size := toUInt32_toNat_of_lt _ hcount
  have hcount_le : symCount src.size ≤ 4 * (src.size / 3) + 4 := by rw [symCount_eq]; split <;> omega
  have hcount4 : symCount src.size + 4 < 2 ^ 32 := by omega
  have hfuel : symCount src.size < fuel := by omega
  obtain ⟨acc, hscan, hacc⟩ := b64_scan_spec enc url (symCount src.size).toUInt32 (by simpa [hcount'] using hcount4)
    (by rw [hcount']; exact encoded_symbols_valid src enc url pad he) fuel (by simpa [hcount'] using hfuel)
  have hnot : decide (acc ≥ (64 : UInt32)) = false := by
    apply decide_eq_false; intro h
    have := UInt32.le_iff_toNat_le.mp h; rw [show (64 : UInt32).toNat = 64 by decide] at this; omega
  have hrest : ((symCount src.size).toUInt32 % 4).toNat = (if src.size % 3 = 0 then 0 else src.size % 3 + 1) := by
    rw [UInt32.toNat_mod, hcount', show (4 : UInt32).toNat = 4 by decide]
    unfold symCount; split <;> omega
  have hne1 : ((symCount src.size).toUInt32 % 4 == 1) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest] at this
    split at this <;> simp at this <;> omega
  unfold base64_decoded_size
  rw [unpadded_length_spec src enc url pad he hsrc' fuel (by omega)]
  simp only [Option.pure_def, bind, Option.bind, hscan, hnot, Bool.false_eq_true, ↓reduceIte, hne1]
  -- the size the decoder reports
  have hval : ((symCount src.size).toUInt32 / 4 * 3 +
      (if ((symCount src.size).toUInt32 % 4 == 0) then (0 : UInt32) else (symCount src.size).toUInt32 % 4 - 1)) = src.size.toUInt32 := by
    apply UInt32.toNat.inj
    rw [toUInt32_toNat_of_lt _ (by omega)]
    have hdiv : ((symCount src.size).toUInt32 / 4).toNat = src.size / 3 := by
      rw [UInt32.toNat_div, hcount', show (4 : UInt32).toNat = 4 by decide]; unfold symCount; split <;> omega
    by_cases h0 : src.size % 3 = 0
    · have hb : ((symCount src.size).toUInt32 % 4 == 0) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, if_pos h0]; decide
      simp only [hb, ↓reduceIte]
      rw [UInt32.toNat_add, UInt32.toNat_mul, hdiv, show (3 : UInt32).toNat = 3 by decide, show (0 : UInt32).toNat = 0 by decide]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · have hb : ((symCount src.size).toUInt32 % 4 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, if_neg h0] at this; simp at this
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [UInt32.toNat_add, UInt32.toNat_mul, hdiv, show (3 : UInt32).toNat = 3 by decide, UInt32.toNat_sub_of_le,
        hrest, if_neg h0, show (1 : UInt32).toNat = 1 by decide]
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      · rw [UInt32.le_iff_toNat_le, hrest, if_neg h0, show (1 : UInt32).toNat = 1 by decide]; omega
  -- the canonical check on the last symbol
  by_cases hzero : symCount src.size = 0
  · have hn0 : src.size = 0 := by unfold symCount at hzero; split at hzero <;> omega
    have hb : ((symCount src.size).toUInt32 == 0) = true := by rw [beq_iff_eq]; rw [hzero]; rfl
    have hb0 : ((symCount src.size).toUInt32 % 4 == 0) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, if_pos (by omega)]; decide
    simp only [hb, ↓reduceIte, hb0, Bool.true_or]
    rw [← hval, if_pos hb0]
  · have hb : ((symCount src.size).toUInt32 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hcount'] at this; simp at this; omega
    simp only [hb, Bool.false_eq_true, ↓reduceIte, base64_value, Option.pure_def]
    have hlastidx : ((symCount src.size).toUInt32 - 1).toNat = symCount src.size - 1 := by
      rw [UInt32.toNat_sub_of_le, hcount', show (1 : UInt32).toNat = 1 by decide]
      rw [UInt32.le_iff_toNat_le, hcount', show (1 : UInt32).toNat = 1 by decide]; omega
    have hlast : enc.getD ((symCount src.size).toUInt32 - 1).toNat 0 = encSym src (b64symbols url) (symCount src.size - 1) := by
      rw [hlastidx]; exact he.syms _ (by omega)
    have hvalues : (if url then ((BASE64_URL_VALUES.getD ((enc.getD ((symCount src.size).toUInt32 - 1).toNat 0).toUInt32).toNat 0).toUInt32)
        else ((BASE64_STD_VALUES.getD ((enc.getD ((symCount src.size).toUInt32 - 1).toNat 0).toUInt32).toNat 0).toUInt32)) =
        symValue url (enc.getD ((symCount src.size).toUInt32 - 1).toNat 0) := by
      unfold symValue b64values; cases url <;> rfl
    rw [hvalues, hlast, encSym_value]
    obtain ⟨g, hg⟩ : ∃ g, g = src.size / 3 := ⟨_, rfl⟩
    rcases (show src.size % 3 = 0 ∨ src.size % 3 = 1 ∨ src.size % 3 = 2 by omega) with h0 | h1 | h2
    · have hb0 : ((symCount src.size).toUInt32 % 4 == 0) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, if_pos h0]; decide
      simp only [hb0, Bool.true_or, ↓reduceIte]
      rw [← hval, if_pos hb0]
    · have hb0 : ((symCount src.size).toUInt32 % 4 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, if_neg (by omega), h1] at this; simp at this
      have hb2 : ((symCount src.size).toUInt32 % 4 == 2) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, if_neg (by omega), h1]; decide
      have hidx : symCount src.size - 1 = 4 * g + 1 := by rw [symCount_eq, if_neg (by omega), h1]; omega
      have hword : encWord src ((symCount src.size - 1) / 4) = (src.getD (3 * g) 0).toUInt32 <<< (16 : UInt32) := by
        rw [hidx, show (4 * g + 1) / 4 = g by omega]; exact (tail_word1 src g (by omega)).symm
      have hlow : (sixbit (encWord src ((symCount src.size - 1) / 4)) ((symCount src.size - 1) % 4) &&& (15 : UInt32)) = 0 := by
        rw [hword, hidx, show (4 * g + 1) % 4 = 1 by omega]
        unfold sixbit; simp only [Nat.one_ne_zero, ↓reduceIte]
        exact (tail1_byte (src.getD (3 * g) 0)).2
      have hb15 : ((sixbit (encWord src ((symCount src.size - 1) / 4)) ((symCount src.size - 1) % 4) &&& (15 : UInt32)) == 0) = true := by
        rw [beq_iff_eq]; exact hlow
      simp only [hb0, hb2, hb15, Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.and_true, Bool.true_or]
      rw [← hval, if_neg (by simp [hb0])]
    · have hb0 : ((symCount src.size).toUInt32 % 4 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, if_neg (by omega), h2] at this; simp at this
      have hb2 : ((symCount src.size).toUInt32 % 4 == 2) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, if_neg (by omega), h2] at this; simp at this
      have hb3 : ((symCount src.size).toUInt32 % 4 == 3) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, if_neg (by omega), h2]; decide
      have hidx : symCount src.size - 1 = 4 * g + 2 := by rw [symCount_eq, if_neg (by omega), h2]; omega
      have hword : encWord src ((symCount src.size - 1) / 4) =
          ((src.getD (3 * g) 0).toUInt32 <<< (16 : UInt32)) ||| ((src.getD (3 * g + 1) 0).toUInt32 <<< (8 : UInt32)) := by
        rw [hidx, show (4 * g + 2) / 4 = g by omega]; exact (tail_word2 src g (by omega)).symm
      have hlow : (sixbit (encWord src ((symCount src.size - 1) / 4)) ((symCount src.size - 1) % 4) &&& (3 : UInt32)) = 0 := by
        rw [hword, hidx, show (4 * g + 2) % 4 = 2 by omega]
        unfold sixbit; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.reduceEqDiff]
        exact (tail2_bytes (src.getD (3 * g) 0) (src.getD (3 * g + 1) 0)).2.2
      have hb3' : ((sixbit (encWord src ((symCount src.size - 1) / 4)) ((symCount src.size - 1) % 4) &&& (3 : UInt32)) == 0) = true := by
        rw [beq_iff_eq]; exact hlow
      simp only [hb0, hb2, hb3, hb3', Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.and_true, Bool.false_and]
      rw [← hval, if_neg (by simp [hb0])]

/-! ## The decoder -/

/-- The 24-bit word the decoder assembles from symbol group `j`. -/
def decWord (enc values : Array UInt8) (j : Nat) : UInt32 :=
  ((((values.getD ((enc.getD (4 * j) 0).toUInt32).toNat 0).toUInt32 <<< 18) |||
    ((values.getD ((enc.getD (4 * j + 1) 0).toUInt32).toNat 0).toUInt32 <<< 12)) |||
    ((values.getD ((enc.getD (4 * j + 2) 0).toUInt32).toNat 0).toUInt32 <<< 6)) |||
    (values.getD ((enc.getD (4 * j + 3) 0).toUInt32).toNat 0).toUInt32

/-- The byte the decoder writes at position `k` of the group region. -/
def decByte3 (enc values : Array UInt8) (k : Nat) : UInt8 :=
  if k % 3 = 0 then (decWord enc values (k / 3) >>> 16).toUInt8
  else if k % 3 = 1 then (decWord enc values (k / 3) >>> 8).toUInt8
  else (decWord enc values (k / 3)).toUInt8

theorem b64_decode_loop (enc values : Array UInt8) (g : Nat) (body : UInt32) (hbody : body.toNat / 4 = g)
    (hsmall : body.toNat + 4 < 2 ^ 32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32),
      3 * g ≤ dst.size → dst.size < 2 ^ 32 → i.toNat ≤ 4 * g → i.toNat % 4 = 0 → out.toNat = 3 * (i.toNat / 4) →
      g - i.toNat / 4 < fuel →
      ∃ dst' i' out', base64_decode.loop1 dst enc values body i out fuel = some (dst', i', out') ∧
        dst'.size = dst.size ∧ i'.toNat = 4 * g ∧ out'.toNat = 3 * g ∧
        ∀ k, dst'.getD k 0 = if out.toNat ≤ k ∧ k < 3 * g then decByte3 enc values k else dst.getD k 0 := by
  induction fuel with
  | zero => intro dst i out _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out hdst hsmall' hi hi4 hout hf
    unfold base64_decode.loop1
    have hi4' : (i + 4).toNat = i.toNat + 4 := uadd i 4 4 (by decide) (by omega)
    by_cases hlt : i.toNat / 4 < g
    · have hc : decide (i + 4 ≤ body) = true := by
        apply decide_eq_true; rw [UInt32.le_iff_toNat_le, hi4']; omega
      simp only [hc, ↓reduceIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      have hi2 : (i + 2).toNat = i.toNat + 2 := uadd i 2 2 (by decide) (by omega)
      have hi3 : (i + 3).toNat = i.toNat + 3 := uadd i 3 3 (by decide) (by omega)
      have ho1 : (out + 1).toNat = out.toNat + 1 := uadd out 1 1 (by decide) (by omega)
      have ho2 : (out + 2).toNat = out.toNat + 2 := uadd out 2 2 (by decide) (by omega)
      have hout3 : (out + 3).toNat = out.toNat + 3 := uadd out 3 3 (by decide) (by omega)
      have ho3 : (out + 3).toNat = 3 * ((i + 4).toNat / 4) := by rw [hout3, hout, hi4']; omega
      obtain ⟨j, hj⟩ : ∃ j, j = i.toNat / 4 := ⟨_, rfl⟩
      have hij : i.toNat = 4 * j := by omega
      have hword : (((((values.getD ((enc.getD i.toNat 0).toUInt32).toNat 0).toUInt32 <<< (18 : UInt32)) |||
          ((values.getD ((enc.getD (i + 1).toNat 0).toUInt32).toNat 0).toUInt32 <<< (12 : UInt32))) |||
          ((values.getD ((enc.getD (i + 2).toNat 0).toUInt32).toNat 0).toUInt32 <<< (6 : UInt32))) |||
          (values.getD ((enc.getD (i + 3).toNat 0).toUInt32).toNat 0).toUInt32) = decWord enc values j := by
        unfold decWord; rw [hi1, hi2, hi3, hij]
      rw [hword]
      obtain ⟨dst', i', out', heq, hsize, hi', hout', hget⟩ :=
        ih (((dst.setIfInBounds out.toNat (decWord enc values j >>> 16).toUInt8).setIfInBounds
              (out + 1).toNat (decWord enc values j >>> 8).toUInt8).setIfInBounds
              (out + 2).toNat (decWord enc values j).toUInt8)
          (i + 4) (out + 3)
          (by simp only [Array.size_setIfInBounds]; exact hdst)
          (by simp only [Array.size_setIfInBounds]; exact hsmall')
          (by rw [hi4']; omega) (by rw [hi4']; omega) ho3 (by rw [hi4']; omega)
      refine ⟨dst', i', out', heq, by rw [hsize]; simp only [Array.size_setIfInBounds], hi', hout', ?_⟩
      intro k
      rw [hget k]
      by_cases hk : (out + 3).toNat ≤ k ∧ k < 3 * g
      · rw [if_pos hk, if_pos ⟨by omega, hk.2⟩]
      · rw [if_neg hk]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds,
          Array.getElem?_setIfInBounds]
        simp only [Array.size_setIfInBounds]
        rw [ho1, ho2]
        have hkj : ∀ t, t < 3 → k = out.toNat + t → decByte3 enc values k =
            (if t = 0 then (decWord enc values j >>> 16).toUInt8 else if t = 1 then (decWord enc values j >>> 8).toUInt8
              else (decWord enc values j).toUInt8) := by
          intro t ht hkt
          unfold decByte3
          rw [hkt, hout, ← hj, show (3 * j + t) / 3 = j by omega, show (3 * j + t) % 3 = t by omega]
        by_cases h2 : out.toNat + 2 = k
        · rw [if_pos h2, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, hkj 2 (by omega) h2.symm]; rfl
        · rw [if_neg h2]
          by_cases h1 : out.toNat + 1 = k
          · rw [if_pos h1, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, hkj 1 (by omega) h1.symm]; rfl
          · rw [if_neg h1]
            by_cases h0 : out.toNat = k
            · rw [if_pos h0, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩, hkj 0 (by omega) h0.symm]; rfl
            · rw [if_neg h0, ← Array.getD_eq_getD_getElem?, if_neg (by omega)]
    · have hc : decide (i + 4 ≤ body) = false := by
        apply decide_eq_false; rw [UInt32.le_iff_toNat_le, hi4']; omega
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine ⟨dst, i, out, rfl, rfl, by omega, by rw [hout]; omega, ?_⟩
      intro k
      rw [if_neg (by omega)]

/-- A symbol's value as the decoder's expression spells it. -/
theorem symValue_def (url : Bool) (b : UInt8) :
    ((if url then BASE64_URL_VALUES else BASE64_STD_VALUES).getD (b.toUInt32).toNat 0).toUInt32 = symValue url b := rfl

/-- The decoder's word of group `j` of an encoding is the encoder's word. -/
theorem decWord_encoded (src enc : Array UInt8) (url pad : Bool) (he : Encoded src enc url pad) (j : Nat)
    (hj : j < src.size / 3) : decWord enc (b64values url) j = encWord src j := by
  have hsym : ∀ t, t < 4 → ((b64values url).getD ((enc.getD (4 * j + t) 0).toUInt32).toNat 0).toUInt32 =
      sixbit (encWord src j) t := by
    intro t ht
    have hk : 4 * j + t < symCount src.size := by unfold symCount; split <;> omega
    show symValue url (enc.getD (4 * j + t) 0) = _
    rw [he.syms _ hk, encSym_value, show (4 * j + t) / 4 = j by omega, show (4 * j + t) % 4 = t by omega]
  have h0 := hsym 0 (by omega); have h1 := hsym 1 (by omega); have h2 := hsym 2 (by omega); have h3 := hsym 3 (by omega)
  rw [Nat.add_zero] at h0
  unfold decWord
  rw [h0, h1, h2, h3]
  unfold sixbit
  simp only [↓reduceIte, Nat.succ_ne_zero, Nat.reduceEqDiff]
  have hlt : encWord src j < (16777216 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt]; simpa using encWord_lt src j
  exact word_reassemble _ hlt

theorem decByte3_encoded (src enc : Array UInt8) (url pad : Bool) (he : Encoded src enc url pad) (k : Nat)
    (hk : k < 3 * (src.size / 3)) : decByte3 enc (b64values url) k = src.getD k 0 := by
  have hj : k / 3 < src.size / 3 := by omega
  unfold decByte3
  rw [decWord_encoded src enc url pad he (k / 3) hj]
  have hw := bytes_of_word (src.getD (3 * (k / 3)) 0) (src.getD (3 * (k / 3) + 1) 0) (src.getD (3 * (k / 3) + 2) 0)
  simp only at hw
  have hword : encWord src (k / 3) =
      (((src.getD (3 * (k / 3)) 0).toUInt32 <<< 16) ||| ((src.getD (3 * (k / 3) + 1) 0).toUInt32 <<< 8)) |||
        (src.getD (3 * (k / 3) + 2) 0).toUInt32 := rfl
  rw [hword]
  by_cases h0 : k % 3 = 0
  · rw [if_pos h0, hw.1, show 3 * (k / 3) = k by omega]
  · rw [if_neg h0]
    by_cases h1 : k % 3 = 1
    · rw [if_pos h1, hw.2.1, show 3 * (k / 3) + 1 = k by omega]
    · rw [if_neg h1, hw.2.2, show 3 * (k / 3) + 2 = k by omega]

/-- The base64 round trip, for every source of fewer than `2^31 - 8` bytes,
both alphabets, padded or not, a destination that holds exactly the encoding,
and a decode destination that holds the source. -/
theorem base64_round_trip (src enc dst : Array UInt8) (url pad : Bool) (fuel : Nat)
    (hsrc : src.size + 8 < 2 ^ 31) (henc : enc.size = encSize src.size pad) (hdst : src.size ≤ dst.size)
    (hdst_small : dst.size < 2 ^ 32) (hf : 2 * src.size + 16 < fuel) :
    ∃ enc' dst', base64_encode enc src url pad fuel = some (.Ok enc.size.toUInt32, enc') ∧
      base64_decode dst enc' url fuel = some (.Ok src.size.toUInt32, dst') ∧ dst'.size = dst.size ∧
      ∀ k, k < src.size → dst'.getD k 0 = src.getD k 0 := by
  have hsrc' : src.size ≤ 3221225469 := by omega
  have hsize := encSize_lt src.size pad hsrc'
  obtain ⟨enc', hencode, hencsize, hsyms, hpads, -⟩ :=
    b64_encode_spec src enc url pad fuel hsrc' (by omega) (by rw [henc]; exact hsize) (by omega)
  have he : Encoded src enc' url pad := ⟨by rw [hencsize, henc], hsyms, hpads⟩
  rw [henc]
  refine ⟨enc', ?_⟩
  -- the decoder
  obtain ⟨g, hg⟩ : ∃ g, g = src.size / 3 := ⟨_, rfl⟩
  have hn : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
  have hfits : decide (src.size.toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false; intro h
    have := UInt32.lt_iff_toNat_lt.mp h; rw [hn, toUInt32_toNat_of_lt _ hdst_small] at this; omega
  have hcount_le : symCount src.size ≤ 4 * (src.size / 3) + 4 := by rw [symCount_eq]; split <;> omega
  have hcount : ((symCount src.size).toUInt32).toNat = symCount src.size := toUInt32_toNat_of_lt _ (by omega)
  have hbody : (src.size.toUInt32 / 3 * 4 + (if (src.size.toUInt32 % 3 == 0) then (0 : UInt32) else src.size.toUInt32 % 3 + 1)) =
      (symCount src.size).toUInt32 := by
    apply UInt32.toNat.inj
    rw [hcount, symCount_eq]
    have hdiv : (src.size.toUInt32 / 3).toNat = src.size / 3 := by
      rw [UInt32.toNat_div, hn, show (3 : UInt32).toNat = 3 by decide]
    have hmod : (src.size.toUInt32 % 3).toNat = src.size % 3 := by
      rw [UInt32.toNat_mod, hn, show (3 : UInt32).toNat = 3 by decide]
    by_cases h0 : src.size % 3 = 0
    · have hb : (src.size.toUInt32 % 3 == 0) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hmod, h0]; decide
      simp only [hb, ↓reduceIte, if_pos h0]
      rw [UInt32.toNat_add, UInt32.toNat_mul, hdiv, show (4 : UInt32).toNat = 4 by decide, show (0 : UInt32).toNat = 0 by decide]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · have hb : (src.size.toUInt32 % 3 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hmod] at this; simp at this; exact h0 this
      simp only [hb, Bool.false_eq_true, ↓reduceIte, if_neg h0]
      rw [UInt32.toNat_add, UInt32.toNat_mul, hdiv, show (4 : UInt32).toNat = 4 by decide, UInt32.toNat_add, hmod,
        show (1 : UInt32).toNat = 1 by decide]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hvalues : (if url then BASE64_URL_VALUES else BASE64_STD_VALUES) = b64values url := rfl
  obtain ⟨dst1, i1, out1, hloop, hsize1, hi1, hout1, hget1⟩ :=
    b64_decode_loop enc' (b64values url) g (symCount src.size).toUInt32 (by rw [hcount, symCount_eq]; split <;> omega)
      (by rw [hcount]; omega) fuel dst 0 0 (by omega) hdst_small (by simp) (by simp) (by simp) (by simp; omega)
  have hrest : ((symCount src.size).toUInt32 - i1).toNat = symCount src.size - 4 * g := by
    rw [UInt32.toNat_sub_of_le, hcount, hi1]
    rw [UInt32.le_iff_toNat_le, hcount, hi1]; rw [symCount_eq]; split <;> omega
  have hcount_eq : symCount src.size = 4 * g + (if src.size % 3 = 0 then 0 else src.size % 3 + 1) := by
    rw [symCount_eq, hg]
  unfold base64_decode
  rw [decoded_size_spec src enc' url pad he hsrc fuel hf]
  simp only [Option.pure_def, bind, Option.bind, hfits, Bool.false_eq_true, ↓reduceIte, hvalues, hbody, hloop]
  -- the tail
  have hi1n : i1.toNat = 4 * g := hi1
  have hi1p : (i1 + 1).toNat = 4 * g + 1 := by rw [uadd i1 1 1 (by decide) (by omega), hi1]
  have hi1q : (i1 + 2).toNat = 4 * g + 2 := by rw [uadd i1 2 2 (by decide) (by omega), hi1]
  have ho1 : (out1 + 1).toNat = 3 * g + 1 := by rw [uadd out1 1 1 (by decide) (by omega), hout1]
  have hsym : ∀ t, 4 * g + t < symCount src.size →
      ((b64values url).getD ((enc'.getD (4 * g + t) 0).toUInt32).toNat 0).toUInt32 = sixbit (encWord src g) t := by
    intro t hk
    show symValue url (enc'.getD (4 * g + t) 0) = _
    rw [he.syms _ hk, encSym_value, show (4 * g + t) / 4 = g by omega, show (4 * g + t) % 4 = t by omega]
  rcases (show src.size % 3 = 0 ∨ src.size % 3 = 1 ∨ src.size % 3 = 2 by omega) with h0 | h1 | h2
  · have hne2 : ((symCount src.size).toUInt32 - i1 == 2) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, hcount_eq, if_pos h0] at this
      simp at this
    have hne3 : ((symCount src.size).toUInt32 - i1 == 3) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, hcount_eq, if_pos h0] at this
      simp at this
    simp only [hne2, hne3, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, hencode, rfl, hsize1, ?_⟩
    intro k hk
    rw [hget1 k, if_pos ⟨by simp, by omega⟩]
    exact decByte3_encoded src enc' url pad he k (by omega)
  · -- one byte in the tail: two symbols
    have heq2 : ((symCount src.size).toUInt32 - i1 == 2) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, hcount_eq, if_neg (by omega), h1]; simp
    have hne3 : ((symCount src.size).toUInt32 - i1 == 3) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, hcount_eq, if_neg (by omega), h1] at this
      simp at this
    have hs0 := hsym 0 (by rw [hcount_eq, if_neg (by omega), h1]; omega)
    have hs1 := hsym 1 (by rw [hcount_eq, if_neg (by omega), h1]; omega)
    rw [Nat.add_zero] at hs0
    have hw1 : encWord src g = (src.getD (3 * g) 0).toUInt32 <<< (16 : UInt32) := (tail_word1 src g (by omega)).symm
    have hword2 : ((((b64values url).getD ((enc'.getD i1.toNat 0).toUInt32).toNat 0).toUInt32 <<< (18 : UInt32)) |||
        (((b64values url).getD ((enc'.getD (i1 + 1).toNat 0).toUInt32).toNat 0).toUInt32 <<< (12 : UInt32))) =
        ((encWord src g >>> 18) <<< 18) ||| (((encWord src g >>> 12) &&& 63) <<< 12) := by
      rw [hi1n, hi1p, hs0, hs1]; simp [sixbit]
    have hbyte : ((((encWord src g >>> 18) <<< 18) ||| (((encWord src g >>> 12) &&& 63) <<< 12)) >>> 16).toUInt8 =
        src.getD (3 * g) 0 := by
      rw [hw1]; exact (tail1_byte (src.getD (3 * g) 0)).1
    simp only [heq2, hne3, Bool.false_eq_true, ↓reduceIte, hword2, hbyte]
    refine ⟨_, hencode, rfl, by rw [Array.size_setIfInBounds, hsize1], ?_⟩
    intro k hk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hsize1, hout1]
    by_cases hk3 : 3 * g = k
    · rw [if_pos hk3, if_pos (by omega), Option.getD_some, ← hk3]
    · rw [if_neg hk3, ← Array.getD_eq_getD_getElem?, hget1 k, if_pos ⟨by simp, by omega⟩]
      exact decByte3_encoded src enc' url pad he k (by omega)
  · -- two bytes in the tail: three symbols
    have hne2 : ((symCount src.size).toUInt32 - i1 == 2) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest, hcount_eq, if_neg (by omega), h2] at this
      simp at this
    have heq3 : ((symCount src.size).toUInt32 - i1 == 3) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, hcount_eq, if_neg (by omega), h2]; simp
    have hs0 := hsym 0 (by rw [hcount_eq, if_neg (by omega), h2]; omega)
    have hs1 := hsym 1 (by rw [hcount_eq, if_neg (by omega), h2]; omega)
    have hs2 := hsym 2 (by rw [hcount_eq, if_neg (by omega), h2]; omega)
    rw [Nat.add_zero] at hs0
    have hw2 : encWord src g = ((src.getD (3 * g) 0).toUInt32 <<< (16 : UInt32)) ||| ((src.getD (3 * g + 1) 0).toUInt32 <<< (8 : UInt32)) :=
      (tail_word2 src g (by omega)).symm
    have hword3 : (((((b64values url).getD ((enc'.getD i1.toNat 0).toUInt32).toNat 0).toUInt32 <<< (18 : UInt32)) |||
        (((b64values url).getD ((enc'.getD (i1 + 1).toNat 0).toUInt32).toNat 0).toUInt32 <<< (12 : UInt32))) |||
        (((b64values url).getD ((enc'.getD (i1 + 2).toNat 0).toUInt32).toNat 0).toUInt32 <<< (6 : UInt32))) =
        ((encWord src g >>> 18) <<< 18) ||| (((encWord src g >>> 12) &&& 63) <<< 12) ||| (((encWord src g >>> 6) &&& 63) <<< 6) := by
      rw [hi1n, hi1p, hi1q, hs0, hs1, hs2]; simp [sixbit]
    have hbytes := tail2_bytes (src.getD (3 * g) 0) (src.getD (3 * g + 1) 0)
    simp only at hbytes
    rw [← hw2] at hbytes
    simp only [hne2, heq3, Bool.false_eq_true, ↓reduceIte, hword3, hbytes.1, hbytes.2.1]
    refine ⟨_, hencode, rfl, by rw [Array.size_setIfInBounds, Array.size_setIfInBounds, hsize1], ?_⟩
    intro k hk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
    simp only [Array.size_setIfInBounds, hsize1, hout1, ho1]
    by_cases hk4 : 3 * g + 1 = k
    · rw [if_pos hk4, if_pos (by omega), Option.getD_some, ← hk4]
    · rw [if_neg hk4]
      by_cases hk3 : 3 * g = k
      · rw [if_pos hk3, if_pos (by omega), Option.getD_some, ← hk3]
      · rw [if_neg hk3, ← Array.getD_eq_getD_getElem?, hget1 k, if_pos ⟨by simp, by omega⟩]
        exact decByte3_encoded src enc' url pad he k (by omega)

end Oak.Stdlib.Encoding
