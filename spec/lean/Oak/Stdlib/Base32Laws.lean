import Std.Tactic.BVDecide
import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.EncodingLaws
import Oak.Stdlib.Base64Laws

/-!
# Oak.Stdlib.Base32Laws — the base32 round trip on the extracted `encoding` package

`base32_decode dst (base32_encode src hex pad) hex = src` for every source
below the size limit, both alphabets (RFC 4648 §6 and §7), padded or not.
The encoder builds a 40-bit word per five-byte group in an inner loop and
writes its eight five-bit fields (fewer for a partial final group, `=` for
the rest when padding is on); the decoder strips the padding, checks every
symbol and the trailing bits of the last one, rebuilds each word from the
symbol values in an inner loop, and writes its bytes. Every loop is handled
by fuel induction, the inner word loops by unrolling their fixed trip
counts, and the bit-level identities by `bv_decide`.
-/

namespace Oak.Stdlib.Encoding

set_option maxRecDepth 65536

/-! ## Tables -/

def b32symbols (hex : Bool) : Array UInt8 := if hex then BASE32_HEX_SYMBOLS else BASE32_STD_SYMBOLS
def b32values (hex : Bool) : Array UInt8 := if hex then BASE32_HEX_VALUES else BASE32_STD_VALUES

theorem b32_roundtrip_std : ∀ v : Fin 32,
    BASE32_STD_VALUES.getD ((BASE32_STD_SYMBOLS.getD v.val 0).toUInt32).toNat 0 = v.val.toUInt8 := by decide +kernel
theorem b32_roundtrip_hex : ∀ v : Fin 32,
    BASE32_HEX_VALUES.getD ((BASE32_HEX_SYMBOLS.getD v.val 0).toUInt32).toNat 0 = v.val.toUInt8 := by decide +kernel
theorem b32_not_pad_std : ∀ v : Fin 32, BASE32_STD_SYMBOLS.getD v.val 0 ≠ 61 := by decide +kernel
theorem b32_not_pad_hex : ∀ v : Fin 32, BASE32_HEX_SYMBOLS.getD v.val 0 ≠ 61 := by decide +kernel

theorem b32_roundtrip (hex : Bool) (v : Nat) (hv : v < 32) :
    (b32values hex).getD (((b32symbols hex).getD v 0).toUInt32).toNat 0 = v.toUInt8 := by
  unfold b32values b32symbols
  cases hex
  · exact b32_roundtrip_std ⟨v, hv⟩
  · exact b32_roundtrip_hex ⟨v, hv⟩

theorem b32_not_pad (hex : Bool) (v : Nat) (hv : v < 32) : (b32symbols hex).getD v 0 ≠ 61 := by
  unfold b32symbols
  cases hex
  · exact b32_not_pad_std ⟨v, hv⟩
  · exact b32_not_pad_hex ⟨v, hv⟩

/-- The symbol of a value, as `base32_symbol` spells it. -/
def sym32 (hex : Bool) (v : UInt32) : UInt8 := (b32symbols hex).getD (v &&& 31).toNat 0

theorem base32_symbol_def (v : UInt32) (hex : Bool) (fuel : Nat) : base32_symbol v hex fuel = some (sym32 hex v) := by
  unfold sym32 b32symbols; cases hex <;> rfl

/-- The value of a symbol, as `base32_value` reads it. -/
def val32 (hex : Bool) (b : UInt8) : UInt32 := ((b32values hex).getD (b.toUInt32).toNat 0).toUInt32

theorem base32_value_def (b : UInt8) (hex : Bool) (fuel : Nat) : base32_value b hex fuel = some (val32 hex b) := by
  unfold val32 b32values; cases hex <;> rfl

theorem val32_sym32 (hex : Bool) (v : UInt32) (hv : v.toNat < 32) : val32 hex (sym32 hex v) = v := by
  unfold val32 sym32
  have hv' : v < (32 : UInt32) := by rw [UInt32.lt_iff_toNat_lt]; simpa using hv
  have hmask : v &&& 31 = v := by bv_decide
  rw [hmask, b32_roundtrip hex v.toNat hv]
  apply UInt32.toNat.inj
  rw [UInt8.toNat_toUInt32, toUInt8_toNat_of_lt _ (by omega)]

theorem sym32_ne_pad (hex : Bool) (v : UInt32) : sym32 hex v ≠ 61 := by
  unfold sym32
  apply b32_not_pad hex
  have h : v &&& 31 < (32 : UInt32) := by bv_decide
  rw [UInt32.lt_iff_toNat_lt] at h; simpa using h

-- Table lookups stay folded from here on.
attribute [irreducible] sym32 val32

/-! ## Words and fields -/

/-- The encoder's inner word loop, folded: five bytes into a 40-bit word. -/
def mk5 (a b c d e : UInt64) : UInt64 :=
  let w0 : UInt64 := ((0 : UInt64) <<< 8) ||| a
  let w1 : UInt64 := (w0 <<< 8) ||| b
  let w2 : UInt64 := (w1 <<< 8) ||| c
  let w3 : UInt64 := (w2 <<< 8) ||| d
  (w3 <<< 8) ||| e

/-- The byte the encoder's inner loop reads at offset `k` of a group. -/
def bv (src : Array UInt8) (i take : UInt32) (k : UInt32) : UInt64 :=
  if decide (k < take) then (src.getD (i + k).toNat 0).toUInt64 else 0

theorem enc_loop2_unroll (src : Array UInt8) (i take : UInt32) (fuel : Nat) :
    base32_encode.loop2 src i take 0 0 (fuel + 6) =
      some (mk5 (bv src i take 0) (bv src i take 1) (bv src i take 2) (bv src i take 3) (bv src i take 4), 5) := by
  simp [base32_encode.loop2, mk5, bv]

/-- Five bytes as a 40-bit word, most significant first. -/
def w40of (a b c d e : UInt8) : UInt64 :=
  ((((a.toUInt64 <<< 32) ||| (b.toUInt64 <<< 24)) ||| (c.toUInt64 <<< 16)) ||| (d.toUInt64 <<< 8)) ||| e.toUInt64

theorem mk5_eq (a b c d e : UInt8) : mk5 a.toUInt64 b.toUInt64 c.toUInt64 d.toUInt64 e.toUInt64 = w40of a b c d e := by
  unfold mk5 w40of; bv_decide

theorem w40of_lt (a b c d e : UInt8) : w40of a b c d e < (1099511627776 : UInt64) := by
  unfold w40of; bv_decide

/-- The word of source group `g` (bytes past the end read as zero). -/
def w40 (src : Array UInt8) (g : Nat) : UInt64 :=
  w40of (src.getD (5 * g) 0) (src.getD (5 * g + 1) 0) (src.getD (5 * g + 2) 0) (src.getD (5 * g + 3) 0) (src.getD (5 * g + 4) 0)

theorem w40_lt (src : Array UInt8) (g : Nat) : w40 src g < (1099511627776 : UInt64) := w40of_lt _ _ _ _ _

/-- Field `s` of a word, exactly as the encoder and decoder spell it. -/
def fld (w : UInt64) (s : UInt32) : UInt64 := (w >>> (((35 : UInt32) - s * 5).toUInt64)) &&& (31 : UInt64)

theorem fld_lt (w : UInt64) (s : UInt32) : (fld w s).toNat < 32 := by
  have h : fld w s < (32 : UInt64) := by unfold fld; bv_decide
  rw [UInt64.lt_iff_toNat_lt] at h; simpa using h

theorem fld_lt' (w : UInt64) (s : UInt32) : ((fld w s).toUInt32).toNat < 32 := by
  have h := fld_lt w s
  rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]; exact h

theorem fld_roundtrip (w : UInt64) (s : UInt32) : ((fld w s).toUInt32).toUInt64 = fld w s := by
  unfold fld; bv_decide

/-- The symbol the encoder writes at output position `k`. -/
def encSym32 (src : Array UInt8) (hex : Bool) (k : Nat) : UInt8 :=
  sym32 hex ((fld (w40 src (k / 8)) (k % 8).toUInt32).toUInt32)

theorem encSym32_ne_pad (src : Array UInt8) (hex : Bool) (k : Nat) : encSym32 src hex k ≠ 61 := sym32_ne_pad _ _

theorem val32_encSym32 (src : Array UInt8) (hex : Bool) (k : Nat) :
    val32 hex (encSym32 src hex k) = (fld (w40 src (k / 8)) (k % 8).toUInt32).toUInt32 := by
  unfold encSym32; exact val32_sym32 hex _ (fld_lt' _ _)

theorem val32_encSym32_lt (src : Array UInt8) (hex : Bool) (k : Nat) : (val32 hex (encSym32 src hex k)).toNat < 32 := by
  rw [val32_encSym32]; exact fld_lt' _ _

/-- The decoder's inner word loop, folded: eight five-bit values into a word. -/
def mk8 (v0 v1 v2 v3 v4 v5 v6 v7 : UInt64) : UInt64 :=
  let x0 : UInt64 := ((0 : UInt64) <<< 5) ||| v0
  let x1 : UInt64 := (x0 <<< 5) ||| v1
  let x2 : UInt64 := (x1 <<< 5) ||| v2
  let x3 : UInt64 := (x2 <<< 5) ||| v3
  let x4 : UInt64 := (x3 <<< 5) ||| v4
  let x5 : UInt64 := (x4 <<< 5) ||| v5
  let x6 : UInt64 := (x5 <<< 5) ||| v6
  (x6 <<< 5) ||| v7

/-- The value the decoder's inner loop reads at offset `s` of a symbol group. -/
def dv (enc : Array UInt8) (hex : Bool) (i take : UInt32) (s : UInt32) : UInt64 :=
  if decide (s < take) then (val32 hex (enc.getD (i + s).toNat 0)).toUInt64 else 0

theorem ite_some_bind {α β : Type} (c : Prop) [Decidable c] (a b : α) (f : α → Option β) :
    (if c then some a else some b).bind f = f (if c then a else b) := by split <;> rfl

theorem dec_loop2_unroll (enc : Array UInt8) (hex : Bool) (i take : UInt32) (fuel : Nat) :
    base32_decode.loop2 enc hex i take 0 0 (fuel + 9) =
      some (mk8 (dv enc hex i take 0) (dv enc hex i take 1) (dv enc hex i take 2) (dv enc hex i take 3)
        (dv enc hex i take 4) (dv enc hex i take 5) (dv enc hex i take 6) (dv enc hex i take 7), 8) := by
  simp [base32_decode.loop2, mk8, dv, base32_value_def, ite_some_bind]

theorem reassemble8 (w : UInt64) (hw : w < (1099511627776 : UInt64)) :
    mk8 (fld w 0) (fld w 1) (fld w 2) (fld w 3) (fld w 4) (fld w 5) (fld w 6) (fld w 7) = w := by
  unfold mk8 fld; bv_decide

/-- Byte `k` of a word, as the decoder's byte loop spells it. -/
def byteAt (w : UInt64) (k : UInt32) : UInt8 :=
  (((w >>> (((32 : UInt32) - k * 8).toUInt64)) &&& (255 : UInt64)).toUInt32).toUInt8

theorem bytes_of_w40 (a b c d e : UInt8) :
    byteAt (w40of a b c d e) 0 = a ∧ byteAt (w40of a b c d e) 1 = b ∧ byteAt (w40of a b c d e) 2 = c ∧
    byteAt (w40of a b c d e) 3 = d ∧ byteAt (w40of a b c d e) 4 = e := by
  unfold byteAt w40of
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-! The fields past a partial group are zero, and the last field's unused
low bits are zero: the canonical trailing bits the decoder checks. -/

theorem tail1_fields (a : UInt8) :
    (∀ s : UInt32, 2 ≤ s → s < 8 → fld (w40of a 0 0 0 0) s = 0) ∧ (fld (w40of a 0 0 0 0) 1 &&& 3) = 0 := by
  refine ⟨?_, ?_⟩
  · intro s h2 h8; unfold fld w40of; bv_decide
  · unfold fld w40of; bv_decide

theorem tail2_fields (a b : UInt8) :
    (∀ s : UInt32, 4 ≤ s → s < 8 → fld (w40of a b 0 0 0) s = 0) ∧ (fld (w40of a b 0 0 0) 3 &&& 15) = 0 := by
  refine ⟨?_, ?_⟩
  · intro s h2 h8; unfold fld w40of; bv_decide
  · unfold fld w40of; bv_decide

theorem tail3_fields (a b c : UInt8) :
    (∀ s : UInt32, 5 ≤ s → s < 8 → fld (w40of a b c 0 0) s = 0) ∧ (fld (w40of a b c 0 0) 4 &&& 1) = 0 := by
  refine ⟨?_, ?_⟩
  · intro s h2 h8; unfold fld w40of; bv_decide
  · unfold fld w40of; bv_decide

theorem tail4_fields (a b c d : UInt8) :
    (∀ s : UInt32, 7 ≤ s → s < 8 → fld (w40of a b c d 0) s = 0) ∧ (fld (w40of a b c d 0) 6 &&& 7) = 0 := by
  refine ⟨?_, ?_⟩
  · intro s h2 h8; unfold fld w40of; bv_decide
  · unfold fld w40of; bv_decide

/-! ## Sizes -/

/-- Symbols a partial final group of `r` bytes (1..4) occupies. -/
def partial32 (r : Nat) : Nat := if r = 1 then 2 else if r = 2 then 4 else if r = 3 then 5 else 7

theorem partial32_lt (r : Nat) : partial32 r < 8 := by
  unfold partial32; split <;> (try split) <;> (try split) <;> omega
theorem partial32_pos (r : Nat) : 2 ≤ partial32 r := by
  unfold partial32; split <;> (try split) <;> (try split) <;> omega

/-- The symbols the encoder writes for `n` bytes (padding excluded). -/
def symCount32 (n : Nat) : Nat := 8 * (n / 5) + (if n % 5 = 0 then 0 else partial32 (n % 5))
/-- The bytes the encoder writes for `n` bytes, padding included when asked. -/
def encSize32 (n : Nat) (pad : Bool) : Nat :=
  8 * (n / 5) + (if n % 5 = 0 then 0 else if pad then 8 else partial32 (n % 5))

theorem symCount32_le (n : Nat) (pad : Bool) : symCount32 n ≤ encSize32 n pad := by
  unfold symCount32 encSize32; have := partial32_lt (n % 5); split <;> (try split) <;> omega

theorem encSize32_le (n : Nat) (pad : Bool) : encSize32 n pad ≤ 8 * (n / 5) + 8 := by
  unfold encSize32; have := partial32_lt (n % 5); split <;> (try split) <;> omega

theorem encSize32_lt (n : Nat) (pad : Bool) (hn : n ≤ 2684354555) : encSize32 n pad < 2 ^ 32 := by
  unfold encSize32; have := partial32_lt (n % 5); split <;> (try split) <;> omega

theorem base32_partial_eq (rest : UInt32) (hr : 1 ≤ rest.toNat) (hr5 : rest.toNat < 5) (fuel : Nat) :
    base32_partial rest fuel = some (partial32 rest.toNat).toUInt32 := by
  rcases (show rest.toNat = 1 ∨ rest.toNat = 2 ∨ rest.toNat = 3 ∨ rest.toNat = 4 by omega) with h | h | h | h
  · have hr' : rest = 1 := UInt32.toNat.inj (by rw [h]; rfl)
    subst hr'; rfl
  · have hr' : rest = 2 := UInt32.toNat.inj (by rw [h]; rfl)
    subst hr'; rfl
  · have hr' : rest = 3 := UInt32.toNat.inj (by rw [h]; rfl)
    subst hr'; rfl
  · have hr' : rest = 4 := UInt32.toNat.inj (by rw [h]; rfl)
    subst hr'; rfl

theorem base32_partial_bytes_eq (r : Nat) (hr : 1 ≤ r) (hr5 : r < 5) (fuel : Nat) :
    base32_partial_bytes (partial32 r).toUInt32 fuel = some r.toUInt32 := by
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 by omega) with h | h | h | h <;> subst h <;> rfl

theorem encoded_size32_spec (n : Nat) (pad : Bool) (fuel : Nat) (hn : n ≤ 2684354555) :
    base32_encoded_size n.toUInt32 pad fuel = some (.Ok (encSize32 n pad).toUInt32) := by
  have hn' : (n.toUInt32).toNat = n := toUInt32_toNat_of_lt _ (by omega)
  have hbig : decide (n.toUInt32 > (2684354555 : UInt32)) = false := by
    apply decide_eq_false; intro h
    have := UInt32.lt_iff_toNat_lt.mp h; rw [hn'] at this; simp at this; omega
  have hgroups : (n.toUInt32 / 5).toNat = n / 5 := by
    rw [UInt32.toNat_div, hn', show (5 : UInt32).toNat = 5 by decide]
  have hrest : (n.toUInt32 % 5).toNat = n % 5 := by
    rw [UInt32.toNat_mod, hn', show (5 : UInt32).toNat = 5 by decide]
  unfold base32_encoded_size
  simp only [hbig, Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.bind_eq_bind]
  by_cases h0 : n % 5 = 0
  · have hb : (n.toUInt32 % 5 == 0) = true := by
      rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hrest, h0]; decide
    simp only [hb, ↓reduceIte, Option.bind_some, Option.some.injEq, Result_u32_EncodingError.Ok.injEq]
    apply UInt32.toNat.inj
    unfold encSize32; rw [if_pos h0, UInt32.toNat_add, UInt32.toNat_mul, hgroups, show (8 : UInt32).toNat = 8 by decide,
      show (0 : UInt32).toNat = 0 by decide, toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · have hb : (n.toUInt32 % 5 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg UInt32.toNat h; rw [hrest] at this; simp at this; exact h0 this
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    cases pad
    · rw [base32_partial_eq _ (by rw [hrest]; omega) (by rw [hrest]; omega)]
      simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some, Option.some.injEq, Result_u32_EncodingError.Ok.injEq]
      apply UInt32.toNat.inj
      unfold encSize32; rw [if_neg h0]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hp := partial32_lt (n % 5)
      rw [UInt32.toNat_add, UInt32.toNat_mul, hgroups, show (8 : UInt32).toNat = 8 by decide, hrest,
        toUInt32_toNat_of_lt _ (by omega), toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [↓reduceIte, Option.bind_some, Option.some.injEq, Result_u32_EncodingError.Ok.injEq]
      apply UInt32.toNat.inj
      unfold encSize32; rw [if_neg h0]; simp only [↓reduceIte]
      rw [UInt32.toNat_add, UInt32.toNat_mul, hgroups, show (8 : UInt32).toNat = 8 by decide,
        toUInt32_toNat_of_lt _ (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-! ## The encoder's symbol loop -/

/-- The byte the symbol loop leaves at slot `j` of a group: a symbol below
    `symbols`, a pad otherwise. -/
def encSlot (hex : Bool) (word : UInt64) (symbols : Nat) (j : Nat) : UInt8 :=
  if j < symbols then sym32 hex ((fld word j.toUInt32).toUInt32) else 61

theorem enc_loop3_step (dst : Array UInt8) (hex pad : Bool) (out : UInt32) (word : UInt64) (symbols s : UInt32)
    (fuel : Nat) (hs : s < 8) :
    base32_encode.loop3 dst hex pad out word symbols s (fuel + 1) =
      base32_encode.loop3
        (if decide (s < symbols) then dst.setIfInBounds (out + s).toNat (sym32 hex ((fld word s).toUInt32))
          else if pad then dst.setIfInBounds (out + s).toNat 61 else dst) hex pad out word symbols (s + 1) fuel := by
  conv => lhs; unfold base32_encode.loop3
  rw [if_pos (decide_eq_true hs)]
  simp only [base32_symbol_def, Option.pure_def, Option.bind_eq_bind, fld]
  by_cases hsym : decide (s < symbols) = true
  · rw [if_pos hsym, if_pos hsym]; rfl
  · rw [if_neg hsym, if_neg hsym]
    cases pad
    · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
    · simp only [↓reduceIte]; rfl

theorem enc_loop3_done (dst : Array UInt8) (hex pad : Bool) (out : UInt32) (word : UInt64) (symbols : UInt32) (fuel : Nat) :
    base32_encode.loop3 dst hex pad out word symbols 8 (fuel + 1) = some (dst, 8) := by
  conv => lhs; unfold base32_encode.loop3
  rfl

theorem toUInt32_succ (t : Nat) (h : t + 1 < 2 ^ 32) : t.toUInt32 + 1 = (t + 1).toUInt32 := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_add, toUInt32_toNat_of_lt _ (by omega), toUInt32_toNat_of_lt _ h, show (1 : UInt32).toNat = 1 by decide,
    Nat.mod_eq_of_lt (by omega)]

/-- The slots the symbol loop writes all lie inside the destination. -/
def SlotsFit (dst : Array UInt8) (out : UInt32) (symbols : Nat) (pad : Bool) : Prop :=
  ∀ j, j < 8 → (j < symbols ∨ pad = true) → out.toNat + j < dst.size

theorem enc_loop3_spec (hex pad : Bool) (word : UInt64) (symbols : UInt32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (out : UInt32) (t : Nat), t ≤ 8 → out.toNat + 8 < 2 ^ 32 →
      SlotsFit dst out symbols.toNat pad → 8 - t < fuel →
      ∃ dst', base32_encode.loop3 dst hex pad out word symbols t.toUInt32 fuel = some (dst', 8) ∧
        dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 =
          if out.toNat + t ≤ k ∧ k < out.toNat + 8 ∧ (k - out.toNat < symbols.toNat ∨ pad = true)
          then encSlot hex word symbols.toNat (k - out.toNat) else dst.getD k 0 := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst out t ht hout hfit hf
    have htn : (t.toUInt32).toNat = t := toUInt32_toNat_of_lt _ (by omega)
    rcases Nat.lt_or_ge t 8 with hlt | hge
    · have hlt' : t.toUInt32 < (8 : UInt32) := by rw [UInt32.lt_iff_toNat_lt, htn]; exact hlt
      rw [enc_loop3_step _ _ _ _ _ _ _ _ hlt', toUInt32_succ t (by omega)]
      have hot : (out + t.toUInt32).toNat = out.toNat + t := uadd out _ t htn (by omega)
      -- the byte this step writes, if any
      obtain ⟨dst1, hdst1, hdst1size, hdst1get⟩ : ∃ dst1,
          (if decide (t.toUInt32 < symbols) then
              dst.setIfInBounds (out + t.toUInt32).toNat (sym32 hex ((fld word t.toUInt32).toUInt32))
            else if pad then dst.setIfInBounds (out + t.toUInt32).toNat 61 else dst) = dst1 ∧ dst1.size = dst.size ∧
          ∀ k, dst1.getD k 0 = if k = out.toNat + t ∧ (t < symbols.toNat ∨ pad = true)
            then encSlot hex word symbols.toNat t else dst.getD k 0 := by
        by_cases hts : t < symbols.toNat
        · have hc : decide (t.toUInt32 < symbols) = true := by
            apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, htn]; exact hts
          have hin : out.toNat + t < dst.size := hfit t hlt (Or.inl hts)
          refine ⟨_, by rw [if_pos hc], by simp only [Array.size_setIfInBounds], ?_⟩
          intro k
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hot]
          by_cases hk : k = out.toNat + t
          · rw [if_pos hk.symm, if_pos hin, Option.getD_some, if_pos ⟨hk, Or.inl hts⟩]
            unfold encSlot; rw [if_pos hts]
          · rw [if_neg (fun h => hk h.symm), if_neg (fun h => hk h.1), ← Array.getD_eq_getD_getElem?]
        · have hc : decide (t.toUInt32 < symbols) = false := by
            apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, htn]; exact hts
          rw [if_neg (by simpa using hc)]
          cases pad
          · refine ⟨dst, by rw [if_neg Bool.false_ne_true], rfl, ?_⟩
            intro k
            rw [if_neg (by rintro ⟨_, h | h⟩; exact hts h; cases h)]
          · have hin : out.toNat + t < dst.size := hfit t hlt (Or.inr rfl)
            refine ⟨_, by rw [if_pos rfl], by simp only [Array.size_setIfInBounds], ?_⟩
            intro k
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hot]
            by_cases hk : k = out.toNat + t
            · rw [if_pos hk.symm, if_pos hin, Option.getD_some, if_pos ⟨hk, Or.inr rfl⟩]
              unfold encSlot; rw [if_neg hts]
            · rw [if_neg (fun h => hk h.symm), if_neg (fun h => hk h.1), ← Array.getD_eq_getD_getElem?]
      rw [hdst1]
      have hfit1 : SlotsFit dst1 out symbols.toNat pad := by
        intro j hj hjs; rw [hdst1size]; exact hfit j hj hjs
      obtain ⟨dst', h, hsize, hget⟩ := ih dst1 out (t + 1) (by omega) hout hfit1 (by omega)
      refine ⟨dst', h, by rw [hsize, hdst1size], ?_⟩
      intro k
      rw [hget k, hdst1get k]
      by_cases hin : out.toNat + (t + 1) ≤ k ∧ k < out.toNat + 8 ∧ (k - out.toNat < symbols.toNat ∨ pad = true)
      · rw [if_pos hin, if_pos ⟨by omega, hin.2.1, hin.2.2⟩]
      · rw [if_neg hin]
        by_cases hk : k = out.toNat + t ∧ (t < symbols.toNat ∨ pad = true)
        · rw [if_pos hk, if_pos ⟨by omega, by omega, by rw [hk.1, Nat.add_sub_cancel_left]; exact hk.2⟩]
          rw [hk.1, Nat.add_sub_cancel_left]
        · rw [if_neg hk, if_neg]
          rintro ⟨h1, h2, h3⟩
          have hlt1 : ¬ (out.toNat + (t + 1) ≤ k) := fun h => hin ⟨h, h2, h3⟩
          apply hk
          refine ⟨by omega, ?_⟩
          have : k - out.toNat = t := by omega
          rw [this] at h3; exact h3
    · have ht8 : t = 8 := by omega
      subst ht8
      rw [show (Nat.toUInt32 8) = (8 : UInt32) from rfl, enc_loop3_done]
      refine ⟨dst, rfl, rfl, ?_⟩
      intro k
      rw [if_neg (by omega)]

/-! ## The encoder's group loop -/

/-- The byte the encoder leaves at output position `k`: a symbol or a pad. -/
def encChar (src : Array UInt8) (hex : Bool) (k : Nat) : UInt8 :=
  if k < symCount32 src.size then encSym32 src hex k else 61

theorem take_val (n : Nat) (i : UInt32) (g : Nat) (hi : i.toNat = 5 * g) (hg : 5 * g ≤ n) (hn : n < 2 ^ 32) :
    (if decide (n.toUInt32 - i < 5) then n.toUInt32 - i else (5 : UInt32)).toNat = min 5 (n - 5 * g) := by
  have hn' : (n.toUInt32).toNat = n := toUInt32_toNat_of_lt _ hn
  have hle : i ≤ n.toUInt32 := by rw [UInt32.le_iff_toNat_le, hn', hi]; exact hg
  have hsub : (n.toUInt32 - i).toNat = n - 5 * g := by rw [UInt32.toNat_sub_of_le _ _ hle, hn', hi]
  by_cases hlt : n - 5 * g < 5
  · have hc : decide (n.toUInt32 - i < 5) = true := by
      apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsub]; exact hlt
    rw [if_pos hc, hsub]; omega
  · have hc : decide (n.toUInt32 - i < 5) = false := by
      apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsub]; exact hlt
    rw [if_neg (by simpa using hc)]; show 5 = _; omega

/-- The encoder's inner loop reads the word of group `g`, bytes past the end as zero. -/
theorem enc_word (src : Array UInt8) (i take : UInt32) (g : Nat) (hi : i.toNat = 5 * g) (hi5 : i.toNat + 5 < 2 ^ 32)
    (htake : take.toNat = min 5 (src.size - 5 * g)) :
    mk5 (bv src i take 0) (bv src i take 1) (bv src i take 2) (bv src i take 3) (bv src i take 4) = w40 src g := by
  have hb : ∀ k : UInt32, k.toNat < 5 → bv src i take k = (src.getD (5 * g + k.toNat) 0).toUInt64 := by
    intro k hk
    unfold bv
    by_cases hlt : k < take
    · rw [if_pos (decide_eq_true hlt), uadd i k k.toNat rfl (by omega), hi]
    · rw [if_neg (by simpa using hlt)]
      have hk' : take.toNat ≤ k.toNat := by
        rw [UInt32.lt_iff_toNat_lt] at hlt; omega
      rw [getD_past src _ (by omega)]; rfl
  rw [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide)]
  simp only [show (0 : UInt32).toNat = 0 from rfl, show (1 : UInt32).toNat = 1 from rfl, show (2 : UInt32).toNat = 2 from rfl,
    show (3 : UInt32).toNat = 3 from rfl, show (4 : UInt32).toNat = 4 from rfl, Nat.add_zero]
  exact mk5_eq _ _ _ _ _

theorem enc_loop1_exit (dst src : Array UInt8) (hex pad : Bool) (i out : UInt32) (fuel : Nat) (hsrc : src.size < 2 ^ 32)
    (hi : src.size ≤ i.toNat) :
    base32_encode.loop1 dst src hex pad i out (fuel + 1) = some (dst, i, out) := by
  conv => lhs; unfold base32_encode.loop1
  have hc : decide (i < src.size.toUInt32) = false := by
    apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, toUInt32_toNat_of_lt _ hsrc]; omega
  rw [if_neg (by simpa using hc)]; rfl

theorem symCount32_eq (n : Nat) : symCount32 n = 8 * (n / 5) + (if n % 5 = 0 then 0 else partial32 (n % 5)) := rfl
theorem encSize32_eq (n : Nat) (pad : Bool) :
    encSize32 n pad = 8 * (n / 5) + (if n % 5 = 0 then 0 else if pad then 8 else partial32 (n % 5)) := rfl

theorem enc_loop1_spec (src : Array UInt8) (hex pad : Bool) (hsrc : src.size ≤ 2684354555) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32) (g : Nat), i.toNat = 5 * g → out.toNat = 8 * g → 5 * g ≤ src.size →
      encSize32 src.size pad ≤ dst.size → dst.size < 2 ^ 32 → src.size - 5 * g + 10 < fuel →
      ∃ dst' i' out', base32_encode.loop1 dst src hex pad i out fuel = some (dst', i', out') ∧ dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 = if 8 * g ≤ k ∧ k < encSize32 src.size pad then encChar src hex k else dst.getD k 0 := by
  have hsize := encSize32_lt src.size pad hsrc
  have hn : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out g hi hout hg hroom hdst hf
    have hle8 : 8 * g ≤ encSize32 src.size pad := by rw [encSize32_eq]; omega
    rcases Nat.lt_or_ge (5 * g) src.size with hlt | hge
    · -- a group remains
      unfold base32_encode.loop1
      have hc : decide (i < src.size.toUInt32) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hn, hi]; exact hlt
      rw [if_pos hc]
      simp only [Option.pure_def, Option.bind_eq_bind]
      obtain ⟨m, hm⟩ : ∃ m, fuel = m + 9 := ⟨fuel - 9, by omega⟩
      have htake := take_val src.size i g hi hg (by omega)
      rw [hm, show m + 9 = (m + 3) + 6 from rfl, enc_loop2_unroll,
        enc_word src i _ g hi (by omega) htake, ← hm]
      simp only [Option.bind_some]
      have hout8 : out.toNat + 8 < 2 ^ 32 := by rw [hout]; omega
      rcases Nat.lt_or_ge (src.size - 5 * g) 5 with hpart | hfull
      · -- the partial final group: `r` bytes, `partial32 r` symbols, then the loop exits
        obtain ⟨r, hr⟩ : ∃ r, r = src.size - 5 * g := ⟨_, rfl⟩
        have hr1 : 1 ≤ r := by omega
        have hr5 : r < 5 := by omega
        have htake' : (if decide (src.size.toUInt32 - i < 5) then src.size.toUInt32 - i else (5 : UInt32)).toNat = r := by
          rw [htake]; omega
        have hne5 : ((if decide (src.size.toUInt32 - i < 5) then src.size.toUInt32 - i else (5 : UInt32)) == 5) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [htake'] at h'
          change r = 5 at h'; omega
        have hdiv : src.size / 5 = g := by omega
        have hmod : src.size % 5 = r := by omega
        rw [hne5]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [base32_partial_eq _ (by rw [htake']; exact hr1) (by rw [htake']; exact hr5), htake']
        simp only [Option.bind_some]
        have hp8 := partial32_lt r
        have hps : ((partial32 r).toUInt32).toNat = partial32 r := toUInt32_toNat_of_lt _ (by omega)
        have henc : encSize32 src.size pad = 8 * g + (if pad then 8 else partial32 r) := by
          rw [encSize32_eq, hdiv, hmod, if_neg (by omega)]
        have hsym : symCount32 src.size = 8 * g + partial32 r := by rw [symCount32_eq, hdiv, hmod, if_neg (by omega)]
        have hfit : SlotsFit dst out (partial32 r).toUInt32.toNat pad := by
          intro j hj hjs
          rw [hps] at hjs
          rw [hout]
          rcases hjs with hjs | hjs
          · cases pad
            · rw [if_neg Bool.false_ne_true] at henc; omega
            · rw [if_pos rfl] at henc; omega
          · rw [hjs] at henc hroom; rw [if_pos rfl] at henc; omega
        obtain ⟨m', hm'⟩ : ∃ m', fuel = m' + 1 := ⟨fuel - 1, by omega⟩
        obtain ⟨dst1, hloop3, hsize1, hget1⟩ := enc_loop3_spec hex pad (w40 src g) (partial32 r).toUInt32 fuel dst out 0
          (by omega) hout8 hfit (by omega)
        rw [show (0 : UInt32) = (0 : Nat).toUInt32 from rfl, hloop3]
        simp only [Option.bind_some]
        -- the loop exits at the next iteration
        have hi' : (i + (if decide (src.size.toUInt32 - i < 5) then src.size.toUInt32 - i else (5 : UInt32))).toNat = src.size := by
          rw [uadd i _ r htake' (by omega), hi]; omega
        rw [hm', enc_loop1_exit dst1 src hex pad _ _ m' (by omega) (by omega)]
        refine ⟨dst1, _, _, rfl, hsize1, ?_⟩
        intro k
        rw [hget1 k, hout, hps]
        by_cases hin : 8 * g ≤ k ∧ k < encSize32 src.size pad
        · have hk8 : k < 8 * g + 8 := by
            have := hin.2; rw [henc] at this; cases pad <;> simp at this <;> omega
          have hcond : k - 8 * g < partial32 r ∨ pad = true := by
            have := hin.2; rw [henc] at this
            cases pad
            · left; simp at this; omega
            · right; rfl
          rw [if_pos ⟨by omega, hk8, hcond⟩, if_pos hin]
          unfold encChar encSlot
          rw [hsym]
          by_cases hks : k < 8 * g + partial32 r
          · rw [if_pos hks, if_pos (by omega)]
            unfold encSym32
            rw [show k / 8 = g by omega, show k % 8 = k - 8 * g by omega]
          · rw [if_neg hks, if_neg (by omega)]
        · rw [if_neg hin, if_neg]
          rintro ⟨h1, h2, h3⟩
          apply hin
          refine ⟨h1, ?_⟩
          rw [henc]
          rcases h3 with h3 | h3
          · cases pad <;> simp <;> omega
          · rw [h3]; simp; omega
      · -- a full group: eight symbols, then the rest
        have htake' : (if decide (src.size.toUInt32 - i < 5) then src.size.toUInt32 - i else (5 : UInt32)).toNat = 5 := by
          rw [htake]; omega
        have heq5 : ((if decide (src.size.toUInt32 - i < 5) then src.size.toUInt32 - i else (5 : UInt32)) == 5) = true := by
          rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [htake']; rfl
        rw [heq5]
        simp only [↓reduceIte, Bool.true_or, Option.bind_some]
        have hg1 : 8 * (g + 1) ≤ encSize32 src.size pad := by rw [encSize32_eq]; omega
        have hfit : SlotsFit dst out (8 : UInt32).toNat pad := by
          intro j hj _; rw [hout]; omega
        obtain ⟨dst1, hloop3, hsize1, hget1⟩ := enc_loop3_spec hex pad (w40 src g) 8 fuel dst out 0 (by omega) hout8 hfit (by omega)
        rw [show (0 : UInt32) = (0 : Nat).toUInt32 from rfl, hloop3]
        simp only [Option.bind_some]
        have hi' : (i + (if decide (src.size.toUInt32 - i < 5) then src.size.toUInt32 - i else (5 : UInt32))).toNat = 5 * (g + 1) := by
          rw [uadd i _ 5 htake' (by omega), hi]; omega
        have hout' : (out + 8).toNat = 8 * (g + 1) := by rw [uadd out 8 8 (by decide) (by omega), hout]; omega
        obtain ⟨dst', i', out', hrest, hsize', hget'⟩ := ih dst1 _ (out + 8) (g + 1) hi' hout' (by omega)
          (by rw [hsize1]; exact hroom) (by rw [hsize1]; exact hdst) (by omega)
        rw [hrest]
        refine ⟨dst', i', out', rfl, by rw [hsize', hsize1], ?_⟩
        intro k
        rw [hget' k, hget1 k, hout]
        simp only [Nat.add_zero]
        have hsym8 : 8 * (g + 1) ≤ symCount32 src.size := by rw [symCount32_eq]; omega
        by_cases hin : 8 * (g + 1) ≤ k ∧ k < encSize32 src.size pad
        · rw [if_pos hin, if_pos ⟨by omega, hin.2⟩]
        · rw [if_neg hin]
          by_cases hk : 8 * g ≤ k ∧ k < 8 * g + 8 ∧ (k - 8 * g < (8 : UInt32).toNat ∨ pad = true)
          · rw [if_pos hk, if_pos ⟨hk.1, by omega⟩]
            unfold encChar encSlot encSym32
            have hk1 := hk.1
            have hk2 := hk.2.1
            rw [if_pos (show k - 8 * g < (8 : UInt32).toNat by change k - 8 * g < 8; omega),
              if_pos (show k < symCount32 src.size by omega),
              show k / 8 = g by omega, show k % 8 = k - 8 * g by omega]
          · rw [if_neg hk, if_neg]
            rintro ⟨h1, h2⟩
            apply hk
            refine ⟨h1, by omega, Or.inl ?_⟩
            show k - 8 * g < 8; omega
    · -- nothing remains
      have hg' : 5 * g = src.size := by omega
      unfold base32_encode.loop1
      have hc : decide (i < src.size.toUInt32) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hn, hi]; omega
      rw [if_neg (by simpa using hc)]
      refine ⟨dst, i, out, rfl, rfl, ?_⟩
      intro k
      have henc : encSize32 src.size pad = 8 * g := by
        rw [encSize32_eq, ← hg', Nat.mul_div_cancel_left _ (by decide), Nat.mul_mod_right, if_pos rfl, Nat.add_zero]
      rw [if_neg (by omega)]

/-- The encoder's contract: the size is reported, the symbols are the
five-bit fields of the source words in order, the padding follows when
asked, and nothing else moves. -/
theorem b32_encode_spec (src dst : Array UInt8) (hex pad : Bool) (fuel : Nat)
    (hsrc : src.size ≤ 2684354555) (hdst : encSize32 src.size pad ≤ dst.size) (hdst_small : dst.size < 2 ^ 32)
    (hf : src.size + 10 < fuel) :
    ∃ dst', base32_encode dst src hex pad fuel = some (.Ok (encSize32 src.size pad).toUInt32, dst') ∧
      dst'.size = dst.size ∧
      (∀ k, k < symCount32 src.size → dst'.getD k 0 = encSym32 src hex k) ∧
      (∀ k, symCount32 src.size ≤ k → k < encSize32 src.size pad → dst'.getD k 0 = 61) ∧
      (∀ k, encSize32 src.size pad ≤ k → dst'.getD k 0 = dst.getD k 0) := by
  have hsize := encSize32_lt src.size pad hsrc
  have hneeded : ((encSize32 src.size pad).toUInt32).toNat = encSize32 src.size pad := toUInt32_toNat_of_lt _ hsize
  have hfits : decide ((encSize32 src.size pad).toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false; intro h
    have := UInt32.lt_iff_toNat_lt.mp h
    rw [hneeded, toUInt32_toNat_of_lt _ hdst_small] at this; omega
  obtain ⟨dst', i', out', hloop, hsize', hget⟩ := enc_loop1_spec src hex pad hsrc fuel dst 0 0 0 (by simp) (by simp)
    (Nat.zero_le _) hdst hdst_small (by omega)
  unfold base32_encode
  rw [encoded_size32_spec src.size pad fuel hsrc]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hfits, Bool.false_eq_true, ↓reduceIte, hloop]
  refine ⟨dst', rfl, hsize', ?_, ?_, ?_⟩
  · intro k hk
    have := symCount32_le src.size pad
    rw [hget k, if_pos ⟨Nat.zero_le _, by omega⟩]; unfold encChar; rw [if_pos hk]
  · intro k hk1 hk2
    rw [hget k, if_pos ⟨Nat.zero_le _, hk2⟩]; unfold encChar; rw [if_neg (by omega)]
  · intro k hk
    rw [hget k, if_neg (by omega)]

/-! ## The encoded text, as the decoder sees it -/

/-- What `b32_encode_spec` establishes about the encoding `enc` of `src`. -/
structure Encoded32 (src enc : Array UInt8) (hex pad : Bool) : Prop where
  size : enc.size = encSize32 src.size pad
  syms : ∀ k, k < symCount32 src.size → enc.getD k 0 = encSym32 src hex k
  pads : ∀ k, symCount32 src.size ≤ k → k < encSize32 src.size pad → enc.getD k 0 = 61

/-- The encoding as the decoder reads it: it only looks at symbol values and
    at which bytes are pads, so this is what the decode laws need. A text
    that is an encoding up to letter case satisfies it. -/
structure Encoded32V (src enc : Array UInt8) (hex pad : Bool) : Prop where
  size : enc.size = encSize32 src.size pad
  vals : ∀ k, k < symCount32 src.size → val32 hex (enc.getD k 0) = (fld (w40 src (k / 8)) (k % 8).toUInt32).toUInt32
  nopad : ∀ k, k < symCount32 src.size → enc.getD k 0 ≠ 61
  pads : ∀ k, symCount32 src.size ≤ k → k < encSize32 src.size pad → enc.getD k 0 = 61

theorem Encoded32.toV {src enc : Array UInt8} {hex pad : Bool} (he : Encoded32 src enc hex pad) : Encoded32V src enc hex pad :=
  ⟨he.size, fun k hk => by rw [he.syms k hk, val32_encSym32], fun k hk => by rw [he.syms k hk]; exact encSym32_ne_pad src hex k,
    he.pads⟩

theorem pads32_le (n : Nat) (pad : Bool) : encSize32 n pad - symCount32 n ≤ 6 := by
  unfold encSize32 symCount32
  have := partial32_pos (n % 5); have := partial32_lt (n % 5)
  split <;> (try split) <;> omega

theorem symCount32_zero (n : Nat) (h : symCount32 n = 0) : n = 0 := by
  unfold symCount32 at h; have := partial32_pos (n % 5); split at h <;> omega

theorem encSize32_zero (pad : Bool) : encSize32 0 pad = 0 := by simp [encSize32]

/-- The padding strip: the count of trailing `=` is exactly the padding written. -/
theorem unpad_loop32 (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad) (hsrc : src.size ≤ 2684354555)
    (fuel : Nat) :
    ∀ pads : UInt32, pads.toNat ≤ encSize32 src.size pad - symCount32 src.size →
      (encSize32 src.size pad - symCount32 src.size) - pads.toNat < fuel →
      base32_unpadded_length.loop1 enc pads fuel = some (encSize32 src.size pad - symCount32 src.size).toUInt32 := by
  have hle := symCount32_le src.size pad
  have hsize := encSize32_lt src.size pad hsrc
  have hp6 := pads32_le src.size pad
  have hsz : (enc.size.toUInt32).toNat = enc.size := toUInt32_toNat_of_lt _ (by rw [he.size]; exact hsize)
  induction fuel with
  | zero => intro pads _ hf; omega
  | succ fuel ih =>
    intro pads hpads hf
    unfold base32_unpadded_length.loop1
    by_cases hlt : pads.toNat < encSize32 src.size pad - symCount32 src.size
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
      have hc2 : decide (pads < (6 : UInt32)) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, show (6 : UInt32).toNat = 6 by decide]; omega
      have hc3 : (enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 == 61) = true := by rw [beq_iff_eq]; exact hbyte
      simp only [hc1, hc2, hc3, Bool.and_self, ↓reduceIte]
      have hp1 : (pads + 1).toNat = pads.toNat + 1 := uadd pads 1 1 (by decide) (by omega)
      exact ih (pads + 1) (by rw [hp1]; omega) (by rw [hp1]; omega)
    · -- the padding is exhausted: stop with the count
      have hpe : pads.toNat = encSize32 src.size pad - symCount32 src.size := by omega
      have hstop : ((decide (pads < enc.size.toUInt32) && decide (pads < (6 : UInt32))) &&
          (enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 == 61)) = false := by
        by_cases hsym0 : symCount32 src.size = 0
        · have hn0 : src.size = 0 := symCount32_zero _ hsym0
          have henc0 : encSize32 src.size pad = 0 := by rw [hn0]; exact encSize32_zero pad
          have : decide (pads < enc.size.toUInt32) = false := by
            apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsz, he.size, henc0]; omega
          exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inl this)))
        · by_cases h6 : pads.toNat = 6
          · have : decide (pads < (6 : UInt32)) = false := by
              apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, show (6 : UInt32).toNat = 6 by decide]; omega
            exact Bool.and_eq_false_iff.mpr (Or.inl (Bool.and_eq_false_iff.mpr (Or.inr this)))
          · have hidx : ((enc.size.toUInt32 - 1) - pads).toNat = enc.size - 1 - pads.toNat := by
              rw [UInt32.toNat_sub_of_le, UInt32.toNat_sub_of_le, hsz, show (1 : UInt32).toNat = 1 by decide]
              · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; rw [he.size]; omega
              · rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, hsz, show (1 : UInt32).toNat = 1 by decide]
                · rw [he.size]; omega
                · rw [UInt32.le_iff_toNat_le, hsz, show (1 : UInt32).toNat = 1 by decide]; rw [he.size]; omega
            have hbyte : enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 ≠ 61 := by
              rw [hidx, he.size, hpe,
                show encSize32 src.size pad - 1 - (encSize32 src.size pad - symCount32 src.size) = symCount32 src.size - 1 by omega]
              exact he.nopad _ (by omega)
            have : (enc.getD ((enc.size.toUInt32 - 1) - pads).toNat 0 == 61) = false := by
              rw [beq_eq_false_iff_ne]; exact hbyte
            exact Bool.and_eq_false_iff.mpr (Or.inr this)
      rw [if_neg (by simpa using hstop)]
      simp only [Option.pure_def, Option.some.injEq]
      apply UInt32.toNat.inj
      rw [hpe, toUInt32_toNat_of_lt _ (by omega)]

/-- No symbol of an encoding is a pad, so the misplaced-pad scan runs to the end clean. -/
theorem scan_loop32 (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad) (body : UInt32)
    (hbody : body.toNat = symCount32 src.size) (hb32 : body.toNat < 2 ^ 32) (fuel : Nat) :
    ∀ i : UInt32, i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      base32_unpadded_length.loop2 enc body false i fuel = some (false, body) := by
  induction fuel with
  | zero => intro i _ hf; omega
  | succ fuel ih =>
    intro i hi hf
    unfold base32_unpadded_length.loop2
    by_cases hlt : i.toNat < body.toNat
    · have hc : decide (i < body) = true := by apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      have hb : (enc.getD i.toNat 0 == 61) = false := by
        rw [beq_eq_false_iff_ne]; exact he.nopad _ (by omega)
      simp only [hc, Bool.not_false, Bool.and_self, ↓reduceIte, hb]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      exact ih (i + 1) (by omega) (by omega)
    · have hc : decide (i < body) = false := by apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq]
      have : i = body := UInt32.toNat.inj (by omega)
      rw [this]

/-- Every symbol of an encoding has a value below 32, so the validity scan runs to the end. -/
theorem valid_loop32 (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad) (body : UInt32)
    (hbody : body.toNat = symCount32 src.size) (hb32 : body.toNat < 2 ^ 32) (fuel : Nat) :
    ∀ i : UInt32, i.toNat ≤ body.toNat → body.toNat - i.toNat < fuel →
      base32_decoded_size.loop1 enc hex body true i fuel = some (true, body) := by
  induction fuel with
  | zero => intro i _ hf; omega
  | succ fuel ih =>
    intro i hi hf
    unfold base32_decoded_size.loop1
    by_cases hlt : i.toNat < body.toNat
    · have hc : decide (i < body) = true := by apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      have hv : decide (val32 hex (enc.getD i.toNat 0) < (32 : UInt32)) = true := by
        apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, show (32 : UInt32).toNat = 32 by decide, he.vals _ (by omega)]
        exact fld_lt' _ _
      simp only [hc, Bool.and_true, ↓reduceIte, base32_value_def, Option.bind_eq_bind, Option.bind_some, hv]
      have hi1 : (i + 1).toNat = i.toNat + 1 := uadd i 1 1 (by decide) (by omega)
      exact ih (i + 1) (by omega) (by omega)
    · have hc : decide (i < body) = false := by apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; exact hlt
      simp only [hc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq]
      have : i = body := UInt32.toNat.inj (by omega)
      rw [this]

theorem symCount32_le' (n : Nat) : symCount32 n ≤ 8 * (n / 5) + 7 := by
  rw [symCount32_eq]; have := partial32_lt (n % 5); split <;> omega

theorem symCount32_le2 (n : Nat) : symCount32 n ≤ 2 * n := by
  rw [symCount32_eq]; unfold partial32
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem unpadded_length_spec32 (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad)
    (hsrc : src.size ≤ 2684354555) (fuel : Nat) (hf : 2 * src.size + 16 < fuel) :
    base32_unpadded_length enc fuel = some (.Ok (symCount32 src.size).toUInt32) := by
  have hle := symCount32_le src.size pad
  have hsize := encSize32_lt src.size pad hsrc
  have hsz : (enc.size.toUInt32).toNat = enc.size := toUInt32_toNat_of_lt _ (by rw [he.size]; exact hsize)
  have hp6 := pads32_le src.size pad
  have hsc_le := symCount32_le' src.size
  have hp8 := partial32_lt (src.size % 5)
  have hp2 := partial32_pos (src.size % 5)
  have hloop := unpad_loop32 src enc hex pad he hsrc fuel 0 (by simp) (by simp; omega)
  unfold base32_unpadded_length
  simp only [hloop, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  have hpads : ((encSize32 src.size pad - symCount32 src.size).toUInt32).toNat = encSize32 src.size pad - symCount32 src.size :=
    toUInt32_toNat_of_lt _ (by omega)
  have hcount' : ((symCount32 src.size).toUInt32).toNat = symCount32 src.size := toUInt32_toNat_of_lt _ (by omega)
  have hbody' : enc.size.toUInt32 - (encSize32 src.size pad - symCount32 src.size).toUInt32 = (symCount32 src.size).toUInt32 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_sub_of_le, hsz, hpads, he.size, hcount']
    · omega
    · rw [UInt32.le_iff_toNat_le, hsz, hpads, he.size]; omega
  rw [hbody', scan_loop32 src enc hex pad he _ hcount' (by omega) fuel 0 (by simp) (by rw [hcount']; simp; omega)]
  simp only [Option.bind_some]
  -- the padding is consistent: either none, or the text is a multiple of eight ending in a partial group
  have hbad : ((decide ((encSize32 src.size pad - symCount32 src.size).toUInt32 > (0 : UInt32))) &&
      ((((enc.size.toUInt32) % (8 : UInt32)) != (0 : UInt32)) ||
        ((encSize32 src.size pad - symCount32 src.size).toUInt32 !=
          (if ((symCount32 src.size).toUInt32 % (8 : UInt32) == (0 : UInt32)) then (0 : UInt32)
            else ((8 : UInt32) - (symCount32 src.size).toUInt32 % (8 : UInt32)))))) = false := by
    by_cases hp0 : encSize32 src.size pad - symCount32 src.size = 0
    · rw [hp0]; rfl
    · -- padding was written: pad = true and the byte count is not a multiple of five
      have hpad : pad = true ∧ src.size % 5 ≠ 0 := by
        refine ⟨?_, ?_⟩
        · cases pad
          · exfalso; apply hp0
            by_cases h5 : src.size % 5 = 0 <;> simp [encSize32, symCount32, h5]
          · rfl
        · intro h5; apply hp0; simp [encSize32, symCount32, h5]
      have hsz8 : enc.size.toUInt32 % 8 = 0 := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_mod, hsz, he.size, show (8 : UInt32).toNat = 8 by decide, show (0 : UInt32).toNat = 0 by decide]
        unfold encSize32; rw [if_neg hpad.2, if_pos hpad.1]; omega
      have hrest : ((symCount32 src.size).toUInt32 % 8).toNat = partial32 (src.size % 5) := by
        rw [UInt32.toNat_mod, hcount', show (8 : UInt32).toNat = 8 by decide]
        unfold symCount32; rw [if_neg hpad.2]; omega
      have h1 : ((enc.size.toUInt32 % 8) != 0) = false := by rw [hsz8]; decide
      have h2 : ((symCount32 src.size).toUInt32 % 8 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hrest] at h'
        simp at h'; omega
      have h3 : ((encSize32 src.size pad - symCount32 src.size).toUInt32 != (8 - (symCount32 src.size).toUInt32 % 8)) = false := by
        rw [bne_eq_false_iff_eq]; apply UInt32.toNat.inj
        rw [hpads, UInt32.toNat_sub_of_le, hrest, show (8 : UInt32).toNat = 8 by decide]
        · unfold encSize32 symCount32; rw [if_neg hpad.2, if_pos hpad.1, if_neg hpad.2]; omega
        · rw [UInt32.le_iff_toNat_le, hrest, show (8 : UInt32).toNat = 8 by decide]; omega
      simp [h1, h2, h3]
  rw [Bool.false_or, hbad]
  simp

/-! ## The decoded size -/

theorem and_zero32 (x : UInt32) : x &&& 0 = 0 := by bv_decide

theorem tail1_unused (a : UInt8) : ((fld (w40of a 0 0 0 0) 1).toUInt32 &&& 3) = 0 := by unfold fld w40of; bv_decide
theorem tail2_unused (a b : UInt8) : ((fld (w40of a b 0 0 0) 3).toUInt32 &&& 15) = 0 := by unfold fld w40of; bv_decide
theorem tail3_unused (a b c : UInt8) : ((fld (w40of a b c 0 0) 4).toUInt32 &&& 1) = 0 := by unfold fld w40of; bv_decide
theorem tail4_unused (a b c d : UInt8) : ((fld (w40of a b c d 0) 6).toUInt32 &&& 7) = 0 := by unfold fld w40of; bv_decide

theorem w40_tail1 (src : Array UInt8) (g : Nat) (h : src.size = 5 * g + 1) : w40 src g = w40of (src.getD (5 * g) 0) 0 0 0 0 := by
  unfold w40; rw [getD_past src (5 * g + 1) (by omega), getD_past src (5 * g + 2) (by omega),
    getD_past src (5 * g + 3) (by omega), getD_past src (5 * g + 4) (by omega)]
theorem w40_tail2 (src : Array UInt8) (g : Nat) (h : src.size = 5 * g + 2) :
    w40 src g = w40of (src.getD (5 * g) 0) (src.getD (5 * g + 1) 0) 0 0 0 := by
  unfold w40; rw [getD_past src (5 * g + 2) (by omega), getD_past src (5 * g + 3) (by omega), getD_past src (5 * g + 4) (by omega)]
theorem w40_tail3 (src : Array UInt8) (g : Nat) (h : src.size = 5 * g + 3) :
    w40 src g = w40of (src.getD (5 * g) 0) (src.getD (5 * g + 1) 0) (src.getD (5 * g + 2) 0) 0 0 := by
  unfold w40; rw [getD_past src (5 * g + 3) (by omega), getD_past src (5 * g + 4) (by omega)]
theorem w40_tail4 (src : Array UInt8) (g : Nat) (h : src.size = 5 * g + 4) :
    w40 src g = w40of (src.getD (5 * g) 0) (src.getD (5 * g + 1) 0) (src.getD (5 * g + 2) 0) (src.getD (5 * g + 3) 0) 0 := by
  unfold w40; rw [getD_past src (5 * g + 4) (by omega)]

/-- The unused-bit mask the decoder checks on the last symbol, by the body's remainder. -/
def unused32 (R : UInt32) : UInt32 :=
  if (R == 2) then 3 else if (R == 4) then 15 else if (R == 5) then 1 else if (R == 7) then 7 else 0

theorem unused32_eq (R : UInt32) :
    (if (R == 2) then (3 : UInt32) else if (R == 4) then 15 else if (R == 5) then 1 else if (R == 7) then 7 else 0) =
      unused32 R := rfl

theorem rest_eq (sc P : Nat) (P32 : UInt32) (hP : P32.toNat = P) (hsc32 : sc < 2 ^ 32) (h : sc % 8 = P) :
    sc.toUInt32 % 8 = P32 := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_mod, toUInt32_toNat_of_lt _ hsc32, show (8 : UInt32).toNat = 8 by decide, hP, h]

theorem size_arith (sc n g P q : Nat) (q32 : UInt32) (hq : q32.toNat = q) (hsc32 : sc < 2 ^ 32) (hn32 : n < 2 ^ 32)
    (hsc : sc = 8 * g + P) (hP : P < 8) (hn : n = 5 * g + q) :
    sc.toUInt32 / 8 * 5 + q32 = n.toUInt32 := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_div, toUInt32_toNat_of_lt _ hsc32, toUInt32_toNat_of_lt _ hn32, hq,
    show (8 : UInt32).toNat = 8 by decide, show (5 : UInt32).toNat = 5 by decide]
  rw [show sc / 8 = g by omega, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The value of the last symbol of an encoding with a partial final group. -/
theorem last_value (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad) (g P : Nat)
    (hsc : symCount32 src.size = 8 * g + P) (hP1 : 1 ≤ P) (hP8 : P < 8) (hsc32 : symCount32 src.size < 2 ^ 32)
    (P32 : UInt32) (hP : P32.toNat = P - 1) (fuel : Nat) :
    (if ((symCount32 src.size).toUInt32 == 0) then some (0 : UInt32)
      else base32_value (enc.getD ((symCount32 src.size).toUInt32 - 1).toNat 0) hex fuel) =
      some (fld (w40 src g) P32).toUInt32 := by
  have hcount' : ((symCount32 src.size).toUInt32).toNat = symCount32 src.size := toUInt32_toNat_of_lt _ hsc32
  have hb0 : ((symCount32 src.size).toUInt32 == 0) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hcount'] at h'; simp at h'; omega
  rw [hb0, if_neg Bool.false_ne_true, base32_value_def]
  have hidx : ((symCount32 src.size).toUInt32 - 1).toNat = symCount32 src.size - 1 := by
    rw [UInt32.toNat_sub_of_le, hcount', show (1 : UInt32).toNat = 1 by decide]
    rw [UInt32.le_iff_toNat_le, hcount', show (1 : UInt32).toNat = 1 by decide]; omega
  rw [hidx, he.vals _ (by omega), hsc, show (8 * g + P - 1) / 8 = g by omega,
    show (8 * g + P - 1) % 8 = P - 1 by omega]
  have : (P - 1).toUInt32 = P32 := UInt32.toNat.inj (by rw [toUInt32_toNat_of_lt _ (by omega), hP])
  rw [this]

/-- The tail of `base32_decoded_size` after the strip and the scan, given the
    facts it turns on: the remainder, the last symbol's value, its canonical
    bits, the partial byte count, and the size arithmetic. -/
theorem decoded_size_tail (enc : Array UInt8) (hex : Bool) (fuel : Nat) (sc32 n32 R last q : UInt32)
    (hR : sc32 % 8 = R) (hL : ((R == 1 || R == 3) || R == 6) = false)
    (hlast : (if (sc32 == 0) then some (0 : UInt32) else base32_value (enc.getD (sc32 - 1).toNat 0) hex fuel) = some last)
    (hcanon : ((last &&& unused32 R) != 0) = false)
    (hq : base32_partial_bytes R fuel = some q) (hsum : sc32 / 8 * 5 + q = n32) :
    (if ((sc32 % 8 == 1 || sc32 % 8 == 3) || sc32 % 8 == 6) then some (Result_u32_EncodingError.Err EncodingError.InvalidLength)
     else (if (sc32 == 0) then some (0 : UInt32) else base32_value (enc.getD (sc32 - 1).toNat 0) hex fuel).bind fun r5 =>
       if ((r5 &&& (if (sc32 % 8 == 2) then (3 : UInt32) else if (sc32 % 8 == 4) then 15 else if (sc32 % 8 == 5) then 1
           else if (sc32 % 8 == 7) then 7 else 0)) != 0) then some (Result_u32_EncodingError.Err EncodingError.NonCanonical)
       else (base32_partial_bytes (sc32 % 8) fuel).bind fun r9 => some (Result_u32_EncodingError.Ok (sc32 / 8 * 5 + r9)))
    = some (Result_u32_EncodingError.Ok n32) := by
  rw [hR, hL, hlast]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some]
  rw [unused32_eq, hcanon]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hq]
  simp only [Option.bind_some, hsum]

theorem decoded_size_spec32 (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad)
    (hsrc : src.size ≤ 2684354555) (fuel : Nat) (hf : 2 * src.size + 16 < fuel) :
    base32_decoded_size enc hex fuel = some (.Ok src.size.toUInt32) := by
  have hle := symCount32_le src.size pad
  have hsize := encSize32_lt src.size pad hsrc
  have hsc_le := symCount32_le' src.size
  have hp8 := partial32_lt (src.size % 5)
  have hp2 := partial32_pos (src.size % 5)
  have hcount' : ((symCount32 src.size).toUInt32).toNat = symCount32 src.size := toUInt32_toNat_of_lt _ (by omega)
  have hn : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
  obtain ⟨g, hg⟩ : ∃ g, g = src.size / 5 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = src.size % 5 := ⟨_, rfl⟩
  have hsc : symCount32 src.size = 8 * g + (if r = 0 then 0 else partial32 r) := by rw [symCount32_eq, hg, hr]
  have hr5 : r < 5 := by omega
  have hnr : src.size = 5 * g + r := by omega
  unfold base32_decoded_size
  rw [unpadded_length_spec32 src enc hex pad he hsrc fuel hf]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [valid_loop32 src enc hex pad he _ hcount' (by omega) fuel 0 (by simp) (by rw [hcount']; simp; omega)]
  simp only [Option.bind_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hsc32 : symCount32 src.size < 2 ^ 32 := by omega
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 by omega) with h | h | h | h | h <;> subst h
  · -- whole groups only: the mask is zero, whatever the last symbol is
    have hsc' : symCount32 src.size = 8 * g := by rw [hsc]; simp
    refine decoded_size_tail enc hex fuel _ _ 0
      (if ((symCount32 src.size).toUInt32 == 0) then (0 : UInt32) else val32 hex (enc.getD ((symCount32 src.size).toUInt32 - 1).toNat 0))
      0 (rest_eq _ 0 0 rfl hsc32 (by omega)) (by decide) ?_ ?_ rfl
      (size_arith _ _ g 0 0 0 rfl hsc32 (by omega) hsc' (by decide) (by omega))
    · rw [base32_value_def]; split <;> rfl
    · rw [bne_eq_false_iff_eq, show unused32 0 = 0 from rfl, and_zero32]
  · have hsc' : symCount32 src.size = 8 * g + 2 := by rw [hsc]; simp [partial32]
    exact decoded_size_tail enc hex fuel _ _ 2 _ 1 (rest_eq _ 2 2 rfl hsc32 (by omega)) (by decide)
      (last_value src enc hex pad he g 2 hsc' (by omega) (by omega) hsc32 1 rfl fuel)
      (by rw [bne_eq_false_iff_eq, show unused32 2 = 3 from rfl, w40_tail1 src g (by omega)]; exact tail1_unused _)
      rfl (size_arith _ _ g 2 1 1 rfl hsc32 (by omega) hsc' (by decide) (by omega))
  · have hsc' : symCount32 src.size = 8 * g + 4 := by rw [hsc]; simp [partial32]
    exact decoded_size_tail enc hex fuel _ _ 4 _ 2 (rest_eq _ 4 4 rfl hsc32 (by omega)) (by decide)
      (last_value src enc hex pad he g 4 hsc' (by omega) (by omega) hsc32 3 rfl fuel)
      (by rw [bne_eq_false_iff_eq, show unused32 4 = 15 from rfl, w40_tail2 src g (by omega)]; exact tail2_unused _ _)
      rfl (size_arith _ _ g 4 2 2 rfl hsc32 (by omega) hsc' (by decide) (by omega))
  · have hsc' : symCount32 src.size = 8 * g + 5 := by rw [hsc]; simp [partial32]
    exact decoded_size_tail enc hex fuel _ _ 5 _ 3 (rest_eq _ 5 5 rfl hsc32 (by omega)) (by decide)
      (last_value src enc hex pad he g 5 hsc' (by omega) (by omega) hsc32 4 rfl fuel)
      (by rw [bne_eq_false_iff_eq, show unused32 5 = 1 from rfl, w40_tail3 src g (by omega)]; exact tail3_unused _ _ _)
      rfl (size_arith _ _ g 5 3 3 rfl hsc32 (by omega) hsc' (by decide) (by omega))
  · have hsc' : symCount32 src.size = 8 * g + 7 := by rw [hsc]; simp [partial32]
    exact decoded_size_tail enc hex fuel _ _ 7 _ 4 (rest_eq _ 7 7 rfl hsc32 (by omega)) (by decide)
      (last_value src enc hex pad he g 7 hsc' (by omega) (by omega) hsc32 6 rfl fuel)
      (by rw [bne_eq_false_iff_eq, show unused32 7 = 7 from rfl, w40_tail4 src g (by omega)]; exact tail4_unused _ _ _ _)
      rfl (size_arith _ _ g 7 4 4 rfl hsc32 (by omega) hsc' (by decide) (by omega))

/-! ## The decoder -/

/-- The decoder's word of a symbol group of an encoding is the encoder's word:
    the symbols give back the fields, and the fields past a partial group are zero. -/
theorem dec_word (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad) (i take : UInt32) (g : Nat)
    (hi : i.toNat = 8 * g) (hi8 : i.toNat + 7 < 2 ^ 32) (hg : 8 * g < symCount32 src.size)
    (htake : take.toNat = min 8 (symCount32 src.size - 8 * g)) :
    mk8 (dv enc hex i take 0) (dv enc hex i take 1) (dv enc hex i take 2) (dv enc hex i take 3)
      (dv enc hex i take 4) (dv enc hex i take 5) (dv enc hex i take 6) (dv enc hex i take 7) = w40 src g := by
  have hsc := symCount32_le' src.size
  have hp8 := partial32_lt (src.size % 5)
  have hp2 := partial32_pos (src.size % 5)
  have hd : ∀ s : UInt32, s.toNat < 8 → dv enc hex i take s = fld (w40 src g) s := by
    intro s hs
    unfold dv
    by_cases hlt : s < take
    · rw [if_pos (decide_eq_true hlt), uadd i s s.toNat rfl (by omega), hi]
      have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
      rw [he.vals _ (by omega), show (8 * g + s.toNat) / 8 = g by omega,
        show (8 * g + s.toNat) % 8 = s.toNat by omega,
        show s.toNat.toUInt32 = s from UInt32.toNat.inj (toUInt32_toNat_of_lt _ (by omega)), fld_roundtrip]
    · rw [if_neg (by simpa using hlt)]
      have hge : take.toNat ≤ s.toNat := by
        have : ¬ s.toNat < take.toNat := fun h => hlt (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      -- only a partial final group leaves fields unread
      obtain ⟨q, hq⟩ : ∃ q, q = src.size / 5 := ⟨_, rfl⟩
      obtain ⟨r, hr⟩ : ∃ r, r = src.size % 5 := ⟨_, rfl⟩
      have hsceq : symCount32 src.size = 8 * q + (if r = 0 then 0 else partial32 r) := by rw [symCount32_eq, hq, hr]
      have hr0 : r ≠ 0 := by intro h0; rw [h0, if_pos rfl] at hsceq; omega
      rw [if_neg hr0] at hsceq
      have hgq : g = q := by omega
      rw [← hgq] at hsceq
      have hnr : src.size = 5 * g + r := by omega
      have h8 : s < (8 : UInt32) := UInt32.lt_iff_toNat_lt.mpr (by rw [show (8 : UInt32).toNat = 8 by decide]; exact hs)
      rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 by omega) with h | h | h | h <;> subst h
      · rw [show partial32 1 = 2 from rfl] at hsceq
        rw [w40_tail1 src g hnr, (tail1_fields _).1 s (UInt32.le_iff_toNat_le.mpr (by rw [show (2 : UInt32).toNat = 2 by decide]; omega)) h8]
      · rw [show partial32 2 = 4 from rfl] at hsceq
        rw [w40_tail2 src g hnr, (tail2_fields _ _).1 s (UInt32.le_iff_toNat_le.mpr (by rw [show (4 : UInt32).toNat = 4 by decide]; omega)) h8]
      · rw [show partial32 3 = 5 from rfl] at hsceq
        rw [w40_tail3 src g hnr, (tail3_fields _ _ _).1 s (UInt32.le_iff_toNat_le.mpr (by rw [show (5 : UInt32).toNat = 5 by decide]; omega)) h8]
      · rw [show partial32 4 = 7 from rfl] at hsceq
        rw [w40_tail4 src g hnr, (tail4_fields _ _ _ _).1 s (UInt32.le_iff_toNat_le.mpr (by rw [show (7 : UInt32).toNat = 7 by decide]; omega)) h8]
  rw [hd 0 (by decide), hd 1 (by decide), hd 2 (by decide), hd 3 (by decide), hd 4 (by decide), hd 5 (by decide),
    hd 6 (by decide), hd 7 (by decide)]
  exact reassemble8 _ (w40_lt src g)

theorem dec_loop3_step (dst : Array UInt8) (out : UInt32) (word : UInt64) (produced k : UInt32) (fuel : Nat) (hk : k < produced) :
    base32_decode.loop3 dst out word produced k (fuel + 1) =
      base32_decode.loop3 (dst.setIfInBounds (out + k).toNat (byteAt word k)) out word produced (k + 1) fuel := by
  conv => lhs; unfold base32_decode.loop3
  rw [if_pos (decide_eq_true hk)]
  rfl

theorem dec_loop3_done (dst : Array UInt8) (out : UInt32) (word : UInt64) (produced k : UInt32) (fuel : Nat) (hk : ¬ k < produced) :
    base32_decode.loop3 dst out word produced k (fuel + 1) = some (dst, k) := by
  conv => lhs; unfold base32_decode.loop3
  rw [if_neg (by simpa using decide_eq_false hk)]
  rfl

/-- The decoder's byte loop writes the top `produced` bytes of the word. -/
theorem dec_loop3_spec (out : UInt32) (word : UInt64) (produced : UInt32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (t : Nat), t ≤ produced.toNat → produced.toNat ≤ 5 → out.toNat + 5 < 2 ^ 32 →
      out.toNat + produced.toNat ≤ dst.size → produced.toNat - t < fuel →
      ∃ dst', base32_decode.loop3 dst out word produced t.toUInt32 fuel = some (dst', produced) ∧ dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 = if out.toNat + t ≤ k ∧ k < out.toNat + produced.toNat then byteAt word (k - out.toNat).toUInt32
          else dst.getD k 0 := by
  induction fuel with
  | zero => intro dst t _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst t ht hp5 hout hroom hf
    have ht32 : (t.toUInt32).toNat = t := toUInt32_toNat_of_lt _ (by omega)
    by_cases hlt : t < produced.toNat
    · have hk : t.toUInt32 < produced := UInt32.lt_iff_toNat_lt.mpr (by rw [ht32]; exact hlt)
      rw [dec_loop3_step _ _ _ _ _ _ hk, toUInt32_succ t (by omega)]
      have hidx : (out + t.toUInt32).toNat = out.toNat + t := uadd out _ t ht32 (by omega)
      obtain ⟨dst', heq, hsize, hget⟩ := ih (dst.setIfInBounds (out + t.toUInt32).toNat (byteAt word t.toUInt32)) (t + 1)
        (by omega) hp5 hout (by rw [Array.size_setIfInBounds]; exact hroom) (by omega)
      refine ⟨dst', heq, by rw [hsize, Array.size_setIfInBounds], ?_⟩
      intro k
      rw [hget k]
      by_cases hin : out.toNat + (t + 1) ≤ k ∧ k < out.toNat + produced.toNat
      · rw [if_pos hin, if_pos ⟨by omega, hin.2⟩]
      · rw [if_neg hin]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hidx]
        by_cases hk : out.toNat + t = k
        · rw [if_pos hk, if_pos (by omega), Option.getD_some, if_pos ⟨by omega, by omega⟩]
          rw [← hk, Nat.add_sub_cancel_left]
        · rw [if_neg hk, ← Array.getD_eq_getD_getElem?, if_neg]
          intro ⟨h1, h2⟩; apply hin; exact ⟨by omega, h2⟩
    · have hk : ¬ t.toUInt32 < produced := fun h => hlt (by have := UInt32.lt_iff_toNat_lt.mp h; rw [ht32] at this; exact this)
      rw [dec_loop3_done _ _ _ _ _ _ hk]
      have hteq : t.toUInt32 = produced := UInt32.toNat.inj (by rw [ht32]; omega)
      refine ⟨dst, by rw [hteq], rfl, ?_⟩
      intro k
      rw [if_neg (by omega)]

/-- Byte `t` of the word of group `g` is source byte `5 * g + t`. -/
theorem byteAt_w40 (src : Array UInt8) (g t : Nat) (ht : t < 5) : byteAt (w40 src g) t.toUInt32 = src.getD (5 * g + t) 0 := by
  have h := bytes_of_w40 (src.getD (5 * g) 0) (src.getD (5 * g + 1) 0) (src.getD (5 * g + 2) 0) (src.getD (5 * g + 3) 0)
    (src.getD (5 * g + 4) 0)
  unfold w40
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 by omega) with h' | h' | h' | h' | h' <;> subst h'
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

/-- The decoder's group loop over an encoding writes the source back, group by group. -/
theorem dec_loop1_spec (src enc : Array UInt8) (hex pad : Bool) (he : Encoded32V src enc hex pad) (hsrc : src.size ≤ 2684354555)
    (body : UInt32) (hbody : body.toNat = symCount32 src.size) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i out : UInt32) (g : Nat), i.toNat = 8 * g → out.toNat = 5 * g → 8 * g ≤ symCount32 src.size →
      src.size ≤ dst.size → dst.size < 2 ^ 32 → symCount32 src.size - 8 * g + 10 < fuel →
      ∃ dst' i' out', base32_decode.loop1 dst enc hex body i out fuel = some (dst', i', out') ∧ dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 = if 5 * g ≤ k ∧ k < src.size then src.getD k 0 else dst.getD k 0 := by
  have hsc_le := symCount32_le' src.size
  have hp8 := partial32_lt (src.size % 5)
  have hp2 := partial32_pos (src.size % 5)
  have hsc32 : symCount32 src.size < 2 ^ 32 := by omega
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i out g hi hout hg hroom hdst hf
    unfold base32_decode.loop1
    rcases Nat.lt_or_ge (8 * g) (symCount32 src.size) with hlt | hge
    · have hc : decide (i < body) = true := by apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hbody, hi]; exact hlt
      rw [if_pos hc]
      simp only [Option.pure_def, Option.bind_eq_bind]
      obtain ⟨m, hm⟩ : ∃ m, fuel = m + 9 := ⟨fuel - 9, by omega⟩
      have hsub : (body - i).toNat = symCount32 src.size - 8 * g := by
        rw [UInt32.toNat_sub_of_le, hbody, hi]; rw [UInt32.le_iff_toNat_le, hbody, hi]; omega
      have htake : (if decide (body - i < 8) then body - i else (8 : UInt32)).toNat = min 8 (symCount32 src.size - 8 * g) := by
        by_cases h8 : symCount32 src.size - 8 * g < 8
        · have hc8 : decide (body - i < (8 : UInt32)) = true := by
            apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, hsub, show (8 : UInt32).toNat = 8 by decide]; exact h8
          rw [if_pos hc8, hsub]; omega
        · have hc8 : decide (body - i < (8 : UInt32)) = false := by
            apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hsub, show (8 : UInt32).toNat = 8 by decide]; exact h8
          rw [if_neg (by simpa using hc8)]; show 8 = _; omega
      rw [hm, dec_loop2_unroll, dec_word src enc hex pad he i _ g hi (by omega) hlt htake, ← hm]
      simp only [Option.bind_some]
      have hout5 : out.toNat + 5 < 2 ^ 32 := by omega
      rcases Nat.lt_or_ge (symCount32 src.size - 8 * g) 8 with hpart | hfull
      · -- the partial final group: `r` bytes, then the loop exits
        obtain ⟨q, hq⟩ : ∃ q, q = src.size / 5 := ⟨_, rfl⟩
        obtain ⟨r, hr⟩ : ∃ r, r = src.size % 5 := ⟨_, rfl⟩
        have hsceq : symCount32 src.size = 8 * q + (if r = 0 then 0 else partial32 r) := by rw [symCount32_eq, hq, hr]
        have hr0 : r ≠ 0 := by intro h0; rw [h0, if_pos rfl] at hsceq; omega
        rw [if_neg hr0] at hsceq
        have hgq : g = q := by omega
        rw [← hgq] at hsceq
        have hnr : src.size = 5 * g + r := by omega
        have hr1 : 1 ≤ r := by omega
        have hr5 : r < 5 := by omega
        have htake' : (if decide (body - i < 8) then body - i else (8 : UInt32)).toNat = partial32 r := by rw [htake]; omega
        have hne8 : ((if decide (body - i < 8) then body - i else (8 : UInt32)) == 8) = false := by
          rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [htake'] at h'
          change partial32 r = 8 at h'; omega
        have hpb : base32_partial_bytes (if decide (body - i < 8) then body - i else (8 : UInt32)) fuel = some r.toUInt32 := by
          have : (if decide (body - i < 8) then body - i else (8 : UInt32)) = (partial32 r).toUInt32 :=
            UInt32.toNat.inj (by rw [htake', toUInt32_toNat_of_lt _ (by omega)])
          rw [this]; exact base32_partial_bytes_eq r hr1 hr5 fuel
        rw [hne8]
        simp only [Bool.false_eq_true, ↓reduceIte, hpb, Option.bind_some]
        have hr32 : (r.toUInt32).toNat = r := toUInt32_toNat_of_lt _ (by omega)
        obtain ⟨dst1, hloop3, hsize1, hget1⟩ := dec_loop3_spec out (w40 src g) r.toUInt32 fuel dst 0 (by omega) (by omega) hout5
          (by rw [hr32]; omega) (by omega)
        rw [show (0 : UInt32) = (0 : Nat).toUInt32 from rfl, hloop3]
        simp only [Option.bind_some]
        have hi' : (i + (if decide (body - i < 8) then body - i else (8 : UInt32))).toNat = symCount32 src.size := by
          rw [uadd i _ (partial32 r) htake' (by omega), hi]; omega
        obtain ⟨m', hm'⟩ : ∃ m', fuel = m' + 1 := ⟨fuel - 1, by omega⟩
        rw [hm']
        unfold base32_decode.loop1
        have hc' : decide (i + (if decide (body - i < 8) then body - i else (8 : UInt32)) < body) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hi', hbody]; omega
        rw [if_neg (by simpa using hc')]
        refine ⟨dst1, _, _, rfl, hsize1, ?_⟩
        intro k
        rw [hget1 k, hout, hr32]
        by_cases hin : 5 * g ≤ k ∧ k < src.size
        · rw [if_pos ⟨by omega, by omega⟩, if_pos hin, byteAt_w40 src g (k - 5 * g) (by omega),
            show 5 * g + (k - 5 * g) = k by omega]
        · rw [if_neg hin, if_neg]
          intro ⟨h1, h2⟩; apply hin; exact ⟨by omega, by omega⟩
      · -- a full group: five bytes, then the rest
        have htake' : (if decide (body - i < 8) then body - i else (8 : UInt32)).toNat = 8 := by rw [htake]; omega
        have heq8 : ((if decide (body - i < 8) then body - i else (8 : UInt32)) == 8) = true := by
          rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [htake']; rfl
        rw [heq8]
        simp only [↓reduceIte, Option.bind_some]
        have hg1 : 5 * (g + 1) ≤ src.size := by
          rw [symCount32_eq] at hfull; split at hfull <;> omega
        obtain ⟨dst1, hloop3, hsize1, hget1⟩ := dec_loop3_spec out (w40 src g) 5 fuel dst 0 (by decide) (by decide) hout5
          (by show out.toNat + 5 ≤ dst.size; omega) (by show 5 - 0 < fuel; omega)
        rw [show (0 : UInt32) = (0 : Nat).toUInt32 from rfl, hloop3]
        simp only [Option.bind_some]
        have hi' : (i + (if decide (body - i < 8) then body - i else (8 : UInt32))).toNat = 8 * (g + 1) := by
          rw [uadd i _ 8 htake' (by omega), hi]; omega
        have hout' : (out + 5).toNat = 5 * (g + 1) := by rw [uadd out 5 5 (by decide) (by omega), hout]; omega
        obtain ⟨dst', i', out', hrest, hsize', hget'⟩ := ih dst1 _ (out + 5) (g + 1) hi' hout' (by omega)
          (by rw [hsize1]; exact hroom) (by rw [hsize1]; exact hdst) (by omega)
        rw [hrest]
        refine ⟨dst', i', out', rfl, by rw [hsize', hsize1], ?_⟩
        intro k
        rw [hget' k, hget1 k, hout]
        simp only [Nat.add_zero]
        by_cases hin : 5 * (g + 1) ≤ k ∧ k < src.size
        · rw [if_pos hin, if_pos ⟨by omega, hin.2⟩]
        · rw [if_neg hin]
          by_cases hk : 5 * g ≤ k ∧ k < 5 * g + (5 : UInt32).toNat
          · have hk2 : k < 5 * g + 5 := hk.2
            rw [if_pos hk, if_pos ⟨hk.1, by omega⟩, byteAt_w40 src g (k - 5 * g) (by omega),
              show 5 * g + (k - 5 * g) = k by omega]
          · rw [if_neg hk, if_neg]
            intro ⟨h1, h2⟩; apply hk; refine ⟨h1, ?_⟩; show k < 5 * g + 5; omega
    · -- nothing remains
      have hc : decide (i < body) = false := by apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, hbody, hi]; omega
      rw [if_neg (by simpa using hc)]
      refine ⟨dst, i, out, rfl, rfl, ?_⟩
      intro k
      have hn5 : src.size ≤ 5 * g := by
        rw [symCount32_eq] at hge; split at hge <;> omega
      rw [if_neg (by omega)]

/-- The decoder on an encoding: for every source of at most `2684354555`
bytes, either alphabet, padded or not, and a decode destination that holds
the source, `base32_decode` of the encoding reports the source length and
writes the source back. -/
theorem base32_decode_encoded (src enc dst : Array UInt8) (hex pad : Bool) (fuel : Nat) (he : Encoded32V src enc hex pad)
    (hsrc : src.size ≤ 2684354555) (hdst : src.size ≤ dst.size) (hdst_small : dst.size < 2 ^ 32) (hf : 2 * src.size + 16 < fuel) :
    ∃ dst', base32_decode dst enc hex fuel = some (.Ok src.size.toUInt32, dst') ∧ dst'.size = dst.size ∧
      ∀ k, k < src.size → dst'.getD k 0 = src.getD k 0 := by
  have hsc_le := symCount32_le' src.size
  have hsc2 := symCount32_le2 src.size
  have hp8 := partial32_lt (src.size % 5)
  have hsc32 : symCount32 src.size < 2 ^ 32 := by omega
  have hn : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ (by omega)
  have hfits : decide (src.size.toUInt32 > dst.size.toUInt32) = false := by
    apply decide_eq_false; intro h
    have := UInt32.lt_iff_toNat_lt.mp h; rw [hn, toUInt32_toNat_of_lt _ hdst_small] at this; omega
  have hmod : (src.size.toUInt32 % 5).toNat = src.size % 5 := by
    rw [UInt32.toNat_mod, hn, show (5 : UInt32).toNat = 5 by decide]
  have hdiv : (src.size.toUInt32 / 5).toNat = src.size / 5 := by
    rw [UInt32.toNat_div, hn, show (5 : UInt32).toNat = 5 by decide]
  have hmul : (src.size.toUInt32 / 5 * 8).toNat = 8 * (src.size / 5) := by
    rw [UInt32.toNat_mul, hdiv, show (8 : UInt32).toNat = 8 by decide, Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨P32, hP32⟩ : ∃ P32 : UInt32, P32 = (if src.size % 5 = 0 then 0 else partial32 (src.size % 5)).toUInt32 := ⟨_, rfl⟩
  have hsum : 8 * (src.size / 5) + (if src.size % 5 = 0 then 0 else partial32 (src.size % 5)) < 2 ^ 32 := by
    rw [← symCount32_eq]; exact hsc32
  have hr4 : (if (src.size.toUInt32 % 5 == 0) then some (0 : UInt32) else base32_partial (src.size.toUInt32 % 5) fuel) = some P32 := by
    by_cases h0 : src.size % 5 = 0
    · have hb : (src.size.toUInt32 % 5 == 0) = true := by
        rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [hmod, h0]; rfl
      rw [if_pos hb, hP32, if_pos h0]; rfl
    · have hb : (src.size.toUInt32 % 5 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h' := congrArg UInt32.toNat h; rw [hmod] at h'; simp at h'; exact h0 h'
      rw [if_neg (by simpa using hb), base32_partial_eq _ (by rw [hmod]; omega) (by rw [hmod]; omega), hmod, hP32, if_neg h0]
  have hbodyN : (src.size.toUInt32 / 5 * 8 + P32).toNat = symCount32 src.size := by
    rw [UInt32.toNat_add, hmul, hP32, toUInt32_toNat_of_lt _ (by split <;> omega), Nat.mod_eq_of_lt hsum, symCount32_eq]
  unfold base32_decode
  rw [decoded_size_spec32 src enc hex pad he hsrc fuel hf]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hfits, Bool.false_eq_true, ↓reduceIte]
  rw [hr4]
  simp only [Option.bind_some]
  obtain ⟨dst', i', out', hloop, hsize', hget⟩ := dec_loop1_spec src enc hex pad he hsrc _ hbodyN fuel dst 0 0 0 (by simp) (by simp)
    (Nat.zero_le _) hdst hdst_small (by simp only [Nat.mul_zero, Nat.sub_zero]; omega)
  rw [hloop]
  simp only [Option.bind_some]
  exact ⟨dst', rfl, hsize', fun k hk => by rw [hget k, if_pos ⟨by omega, hk⟩]⟩

/-- The base32 round trip, for every source of at most `2684354555` bytes,
both alphabets, padded or not, a destination that holds exactly the encoding,
and a decode destination that holds the source. -/
theorem base32_round_trip (src enc dst : Array UInt8) (hex pad : Bool) (fuel : Nat)
    (hsrc : src.size ≤ 2684354555) (henc : enc.size = encSize32 src.size pad) (hdst : src.size ≤ dst.size)
    (hdst_small : dst.size < 2 ^ 32) (hf : 2 * src.size + 16 < fuel) :
    ∃ enc' dst', base32_encode enc src hex pad fuel = some (.Ok enc.size.toUInt32, enc') ∧
      base32_decode dst enc' hex fuel = some (.Ok src.size.toUInt32, dst') ∧ dst'.size = dst.size ∧
      ∀ k, k < src.size → dst'.getD k 0 = src.getD k 0 := by
  have hsize := encSize32_lt src.size pad hsrc
  obtain ⟨enc', hencode, hencsize, hsyms, hpads, -⟩ :=
    b32_encode_spec src enc hex pad fuel hsrc (by omega) (by rw [henc]; exact hsize) (by omega)
  have he : Encoded32 src enc' hex pad := ⟨by rw [hencsize, henc], hsyms, hpads⟩
  obtain ⟨dst', hdec, hsize', hget⟩ := base32_decode_encoded src enc' dst hex pad fuel he.toV hsrc hdst hdst_small hf
  rw [henc]
  exact ⟨enc', dst', hencode, hdec, hsize', hget⟩

end Oak.Stdlib.Encoding
