import Oak.WasmAssemblerLaws
import Oak.WasmEncoding

/-! Exact byte refinement of the mechanically extracted Oak LEB writers.
The mathematical byte sequence uses integers, not machine arithmetic or the
extracted loops. Its length is structural, not execution fuel. -/
namespace Oak.WasmAssembler

/-- Exactly `n` seven-bit groups, with continuation on all but the final byte. -/
def lebBytes : Nat → Int → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofNat ((v % 128).toNat + if n = 0 then 0 else 128) ::
      lebBytes n (v / 128)

@[simp] theorem lebBytes_length (n : Nat) (v : Int) : (lebBytes n v).length = n := by
  induction n generalizing v <;> simp [lebBytes, *]

private theorem encode_length_pos (w : Nat) (s : Bool) (v : Int) :
    0 < (WasmEncoding.encode w s v).length := by
  rw [WasmEncoding.encode]
  split <;> simp

/-- The fixed-count byte sequence equals the independent canonical encoder
when its count is the encoder's length. This does not assume a runtime loop. -/
theorem lebBytes_encode (w : Nat) (s : Bool) (v : Int) :
    lebBytes (WasmEncoding.encode w s v).length v = WasmEncoding.encode w s v := by
  induction w using Nat.strongRecOn generalizing v with
  | ind w ih =>
    rw [WasmEncoding.encode]
    split
    · simp [lebBytes]
    · rename_i h
      have hw : w - 7 < w := by omega
      have hn := encode_length_pos (w - 7) s (v / 128)
      simp only [List.length_cons, lebBytes, if_neg (by omega :
        (WasmEncoding.encode (w - 7) s (v / 128)).length ≠ 0), ih _ hw]

/-- Write a mathematical list at a natural-number offset. Public correctness
requires its complete footprint to fit, so no dropped store can justify it. -/
def writeBytes (dst : Array UInt8) (offset : Nat) : List UInt8 → Array UInt8
  | [] => dst
  | b :: bs => writeBytes (dst.setIfInBounds offset b) (offset + 1) bs

@[simp] theorem writeBytes_size (dst : Array UInt8) (offset : Nat) (bs : List UInt8) :
    (writeBytes dst offset bs).size = dst.size := by
  induction bs generalizing dst offset <;> simp [writeBytes, *]

private theorem or128 : ∀ b : Fin 128, b.val ||| 128 = b.val + 128 := by decide +kernel

private theorem word_byte (v : UInt64) (more : Bool) :
    (if more then ((v &&& 127).toUInt32 ||| 128) else (v &&& 127).toUInt32).toUInt8 =
      UInt8.ofNat (v.toNat % 128 + if more then 128 else 0) := by
  have hm := Nat.mod_lt v.toNat (by decide : 0 < 128)
  have ha : (v &&& 127).toNat = v.toNat % 128 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 7
  apply UInt8.toNat.inj
  cases more <;> simp only [Bool.false_eq_true, ↓reduceIte, UInt32.toNat_toUInt8,
    UInt64.toNat_toUInt32, UInt32.toNat_or, ha, UInt8.toNat_ofNat']
  · omega
  · rw [Nat.mod_eq_of_lt (by omega : v.toNat % 128 < 2^32)]
    rw [show (128 : UInt32).toNat = 128 by decide, or128 ⟨_, hm⟩]

private theorem shift7 (v : UInt64) : (v >>> 7).toNat = v.toNat / 128 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl

private def signedNext (v : Int64) : Int64 := (wasm_signed_next v 0).getD 0

private theorem signedNext_eq (v : Int64) (fuel : Nat) :
    wasm_signed_next v fuel = some (signedNext v) := by rfl

private theorem signedNext_int (v : Int64) : (signedNext v).toInt = v.toInt / 128 := by
  have h := signed_next_floor v 0
  rw [signedNext_eq] at h
  exact Option.some.inj h

private theorem signed_payload (v : Int64) : v.toUInt64.toNat % 128 = (v.toInt % 128).toNat := by
  have h : v.toInt = (v.toUInt64.toNat : Int).bmod (2^64) := by
    exact v.toBitVec.toInt_eq_toNat_bmod
  rw [h, Int.bmod]
  split <;> omega

/-- The actual unsigned loop terminates within its remaining byte count plus
one guard evaluation, and writes precisely the mathematical byte sequence. -/
theorem uleb_loop_bytes (offset size : UInt32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (v : UInt64) (i : UInt32),
      offset.toNat + size.toNat < 2^32 → i.toNat ≤ size.toNat →
      size.toNat - i.toNat < fuel →
      (wasm_write_uleb.loop1 dst offset size v i fuel).map Prod.fst =
        some (writeBytes dst (offset.toNat + i.toNat)
          (lebBytes (size.toNat - i.toNat) v.toNat)) := by
  induction fuel with
  | zero => intro dst v i hb hi hf; omega
  | succ fuel ih =>
    intro dst v i hb hi hf
    by_cases hlt : i < size
    · have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]; change (i.toNat + 1) % 2^32 = _; omega
      have hoff : (offset + i).toNat = offset.toNat + i.toNat := by
        rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hn : size.toNat - i.toNat = (size.toNat - (i + 1).toNat) + 1 := by omega
      let b := (if decide (i + 1 < size) then ((v &&& 127).toUInt32 ||| 128)
        else (v &&& 127).toUInt32).toUInt8
      have hstep : wasm_write_uleb.loop1 dst offset size v i (fuel + 1) =
          wasm_write_uleb.loop1 (dst.setIfInBounds (offset + i).toNat b)
            offset size (v >>> 7) (i + 1) fuel := by
        simp only [wasm_write_uleb.loop1, decide_eq_true hlt, ↓reduceIte]
        unfold b
        split <;> rfl
      rw [hstep, ih _ _ _ hb (by omega) (by omega), hoff, hn]
      simp only [lebBytes, writeBytes, shift7, Int.natCast_ediv, hi1]
      have hmore : (decide (i + 1 < size)) =
          decide (size.toNat - (i.toNat + 1) ≠ 0) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt, hi1]
        omega
      simp only [b, word_byte, hmore, decide_eq_true_eq]
      have hpay : ((v.toNat : Int) % 128).toNat = v.toNat % 128 := rfl
      simp only [hpay]
      by_cases hz : size.toNat - (i.toNat + 1) = 0 <;> simp [hz, Nat.add_assoc]
    · have he : size.toNat - i.toNat = 0 := by
        have := UInt32.not_lt.mp hlt
        rw [UInt32.le_iff_toNat_le] at this
        omega
      simp [wasm_write_uleb.loop1, hlt, he, lebBytes, writeBytes]

/-- The actual signed loop terminates within its remaining byte count plus
one guard evaluation, and writes precisely the mathematical byte sequence. -/
theorem sleb_loop_bytes (offset size : UInt32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (v : Int64) (i : UInt32),
      offset.toNat + size.toNat < 2^32 → i.toNat ≤ size.toNat →
      size.toNat - i.toNat < fuel →
      (wasm_write_sleb.loop1 dst offset size v i fuel).map Prod.fst =
        some (writeBytes dst (offset.toNat + i.toNat)
          (lebBytes (size.toNat - i.toNat) v.toInt)) := by
  induction fuel with
  | zero => intro dst v i hb hi hf; omega
  | succ fuel ih =>
    intro dst v i hb hi hf
    by_cases hlt : i < size
    · have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]; change (i.toNat + 1) % 2^32 = _; omega
      have hoff : (offset + i).toNat = offset.toNat + i.toNat := by
        rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hn : size.toNat - i.toNat = (size.toNat - (i + 1).toNat) + 1 := by omega
      let b := (if decide (i + 1 < size) then ((v.toUInt64 &&& 127).toUInt32 ||| 128)
        else (v.toUInt64 &&& 127).toUInt32).toUInt8
      have hstep : wasm_write_sleb.loop1 dst offset size v i (fuel + 1) =
          wasm_write_sleb.loop1 (dst.setIfInBounds (offset + i).toNat b)
            offset size (signedNext v) (i + 1) fuel := by
        simp only [wasm_write_sleb.loop1, decide_eq_true hlt, ↓reduceIte, signedNext_eq]
        unfold b
        split <;> rfl
      rw [hstep, ih _ _ _ hb (by omega) (by omega), hoff, hn]
      simp only [lebBytes, writeBytes, signedNext_int, hi1]
      have hmore : (decide (i + 1 < size)) =
          decide (size.toNat - (i.toNat + 1) ≠ 0) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt, hi1]
        omega
      simp only [b, word_byte, signed_payload, hmore, decide_eq_true_eq]
      by_cases hz : size.toNat - (i.toNat + 1) = 0 <;> simp [hz, Nat.add_assoc]
    · have he : size.toNat - i.toNat = 0 := by
        have := UInt32.not_lt.mp hlt
        rw [UInt32.le_iff_toNat_le] at this
        omega
      simp [wasm_write_sleb.loop1, hlt, he, lebBytes, writeBytes]

private theorem count_succ (count : UInt32) (n : Nat) (hn : 0 < n) :
    (count + 1) + UInt32.ofNat (n - 1) = count + UInt32.ofNat n := by
  rw [UInt32.add_assoc]
  have h : (1 : UInt32) + UInt32.ofNat (n - 1) = UInt32.ofNat n := by
    rw [show (1 : UInt32) = UInt32.ofNat 1 by rfl, ← UInt32.ofNat_add]
    congr 1; omega
  rw [h]

/-- The extracted unsigned size loop computes the canonical encoder's length,
including its termination bound. The accumulator arithmetic is explicit u32. -/
theorem uleb_size_loop (fuel : Nat) :
    ∀ (w : Nat) (v : UInt64) (count : UInt32), 0 < w →
      WasmLEB.inRange w false v.toNat → (WasmEncoding.encode w false v.toNat).length ≤ fuel →
      (wasm_uleb_size.loop1 v count fuel).map Prod.snd =
        some (count + UInt32.ofNat ((WasmEncoding.encode w false v.toNat).length - 1)) := by
  induction fuel with
  | zero => intro w v count hp hr hf; have := encode_length_pos w false v.toNat; omega
  | succ fuel ih =>
    intro w v count hp hr hf
    have he := WasmEncoding.encode_step hp hr
    by_cases ht : WasmEncoding.terminal false v.toNat
    · have hg : ¬v ≥ 128 := by
        simp only [WasmEncoding.terminal, Bool.false_eq_true, ↓reduceIte] at ht
        change ¬(128 : UInt64) ≤ v
        rw [UInt64.le_iff_toNat_le]; change ¬128 ≤ v.toNat; omega
      simp [wasm_uleb_size.loop1, hg, he, ht]
    · have hg : v ≥ 128 := by
        simp only [WasmEncoding.terminal, Bool.false_eq_true, ↓reduceIte] at ht
        change (128 : UInt64) ≤ v
        rw [UInt64.le_iff_toNat_le]; change 128 ≤ v.toNat; omega
      have hw := WasmEncoding.continuation_width hp hr ht
      have hr' : WasmLEB.inRange (w - 7) false (v >>> 7).toNat := by
        rw [shift7, Int.natCast_ediv]
        exact WasmEncoding.quotient_range hw hr
      have hn : (WasmEncoding.encode w false v.toNat).length =
          (WasmEncoding.encode (w - 7) false (v >>> 7).toNat).length + 1 := by
        rw [he, if_neg ht, shift7, Int.natCast_ediv]
        rfl
      have hn' := encode_length_pos (w - 7) false (v >>> 7).toNat
      simp only [wasm_uleb_size.loop1, decide_eq_true hg, ↓reduceIte]
      rw [ih _ _ _ (by omega) hr' (by omega), hn]
      simp only [Nat.add_sub_cancel]
      rw [count_succ _ _ hn']

private theorem unsigned_range (v : UInt64) : WasmLEB.inRange 64 false v.toNat := by
  have h := v.toNat_lt
  simp only [WasmLEB.inRange, Bool.false_eq_true, ↓reduceIte]
  constructor <;> omega

private theorem signed_range (v : Int64) : WasmLEB.inRange 64 true v.toInt := by
  exact ⟨v.le_toInt, v.toInt_lt⟩

/-- All uint64 sizes are canonical and complete in at most ten guard steps. -/
theorem uleb_size_exact (v : UInt64) (fuel : Nat) (hf : 10 ≤ fuel) :
    wasm_uleb_size v fuel = some (UInt32.ofNat (WasmEncoding.encode 64 false v.toNat).length) := by
  have hb := WasmEncoding.encode_byte_budget (by decide : 0 < 64) (unsigned_range v)
  have hn := encode_length_pos 64 false v.toNat
  have h := uleb_size_loop fuel 64 v 1 (by decide) (unsigned_range v) (by omega)
  have hc : (1 : UInt32) + UInt32.ofNat ((WasmEncoding.encode 64 false v.toNat).length - 1) =
      UInt32.ofNat (WasmEncoding.encode 64 false v.toNat).length := by
    rw [show (1 : UInt32) = UInt32.ofNat 1 by rfl, ← UInt32.ofNat_add]
    congr 1; omega
  rw [hc] at h
  cases hs : wasm_uleb_size.loop1 v 1 fuel with
  | none => simp [hs] at h
  | some state =>
    rcases state with ⟨v', n⟩
    simpa [wasm_uleb_size, hs] using h

private theorem signed_guard (v : Int64) :
    ((decide (v < (0 - (64 : Int64)))) || decide (v ≥ (64 : Int64))) =
      decide (¬WasmEncoding.terminal true v.toInt) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, WasmEncoding.terminal, ↓reduceIte]
  change (v < (0 - (64 : Int64)) ∨ (64 : Int64) ≤ v) ↔ _
  rw [Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le]
  change (v.toInt < -64 ∨ 64 ≤ v.toInt) ↔ ¬(-64 ≤ v.toInt ∧ v.toInt < 64)
  omega

/-- The extracted signed size loop computes the canonical encoder's length
for every in-range signed value, including negative nonmultiples of 128. -/
theorem sleb_size_loop (fuel : Nat) :
    ∀ (w : Nat) (v : Int64) (count : UInt32), 0 < w →
      WasmLEB.inRange w true v.toInt → (WasmEncoding.encode w true v.toInt).length ≤ fuel →
      (wasm_sleb_size.loop1 v count fuel).map Prod.snd =
        some (count + UInt32.ofNat ((WasmEncoding.encode w true v.toInt).length - 1)) := by
  induction fuel with
  | zero => intro w v count hp hr hf; have := encode_length_pos w true v.toInt; omega
  | succ fuel ih =>
    intro w v count hp hr hf
    have he := WasmEncoding.encode_step hp hr
    by_cases ht : WasmEncoding.terminal true v.toInt
    · simp only [wasm_sleb_size.loop1, signed_guard, ht, not_true_eq_false, decide_false]
      simp [he, ht]
    · have hw := WasmEncoding.continuation_width hp hr ht
      have hr' : WasmLEB.inRange (w - 7) true (signedNext v).toInt := by
        rw [signedNext_int]
        exact WasmEncoding.quotient_range hw hr
      have hn : (WasmEncoding.encode w true v.toInt).length =
          (WasmEncoding.encode (w - 7) true (signedNext v).toInt).length + 1 := by
        rw [he, if_neg ht, signedNext_int]; rfl
      have hn' := encode_length_pos (w - 7) true (signedNext v).toInt
      simp only [wasm_sleb_size.loop1, signed_guard, ht, not_false_eq_true,
        decide_true, ↓reduceIte, signedNext_eq, bind, Option.bind]
      rw [ih _ _ _ (by omega) hr' (by omega), hn]
      simp only [Nat.add_sub_cancel]
      rw [count_succ _ _ hn']
/-- All int64 sizes are canonical and complete in at most ten guard steps. -/
theorem sleb_size_exact (v : Int64) (fuel : Nat) (hf : 10 ≤ fuel) :
    wasm_sleb_size v fuel = some (UInt32.ofNat (WasmEncoding.encode 64 true v.toInt).length) := by
  have hb := WasmEncoding.encode_byte_budget (by decide : 0 < 64) (signed_range v)
  have hn := encode_length_pos 64 true v.toInt
  have h := sleb_size_loop fuel 64 v 1 (by decide) (signed_range v) (by omega)
  have hc : (1 : UInt32) + UInt32.ofNat ((WasmEncoding.encode 64 true v.toInt).length - 1) =
      UInt32.ofNat (WasmEncoding.encode 64 true v.toInt).length := by
    rw [show (1 : UInt32) = UInt32.ofNat 1 by rfl, ← UInt32.ofNat_add]
    congr 1; omega
  rw [hc] at h
  cases hs : wasm_sleb_size.loop1 v 1 fuel with
  | none => simp [hs] at h
  | some state =>
    rcases state with ⟨v', n⟩
    simpa [wasm_sleb_size, hs] using h

/-- Complete ULEB writer contract for every UInt64: termination, exact
canonical bytes and count on success, and complete storage preservation on
refusal. Eleven guard steps suffice, including the final writer guard. -/
theorem write_uleb_exact (dst : Array UInt8) (offset : UInt32) (v : UInt64)
    (fuel : Nat) (hf : 11 ≤ fuel) (hsmall : dst.size < 2^32) :
    wasm_write_uleb dst offset v fuel =
      some (if offset.toNat + (WasmEncoding.encode 64 false v.toNat).length ≤ dst.size
        then (UInt32.ofNat (WasmEncoding.encode 64 false v.toNat).length,
          writeBytes dst offset.toNat (WasmEncoding.encode 64 false v.toNat))
        else (0, dst)) := by
  let bs := WasmEncoding.encode 64 false v.toNat
  have hlen : bs.length ≤ 10 := by
    have := WasmEncoding.encode_byte_budget (by decide : 0 < 64) (unsigned_range v)
    dsimp [bs]; omega
  have hn : (UInt32.ofNat bs.length).toNat = bs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hd : dst.size.toUInt32.toNat = dst.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hsmall]
  have hs := uleb_size_exact v fuel (by omega)
  change wasm_write_uleb dst offset v fuel = some (if offset.toNat + bs.length ≤ dst.size
    then (UInt32.ofNat bs.length, writeBytes dst offset.toNat bs) else (0, dst))
  by_cases hb : offset.toNat + bs.length ≤ dst.size
  · have hg : offset ≤ dst.size.toUInt32 ∧ UInt32.ofNat bs.length ≤ dst.size.toUInt32 - offset := by
      apply (range_guard_iff _ _ _).mpr
      rwa [hn, hd]
    have hw := uleb_loop_bytes offset (UInt32.ofNat bs.length) fuel dst v 0
      (by rw [hn]; omega) (by simp) (by rw [hn]; change bs.length - 0 < fuel; omega)
    simp only [UInt32.toNat_zero, Nat.add_zero, Nat.sub_zero, hn] at hw
    cases hl : wasm_write_uleb.loop1 dst offset (UInt32.ofNat bs.length) v 0 fuel with
    | none => simp [hl] at hw
    | some state =>
      rcases state with ⟨out, v', i'⟩
      have he : out = writeBytes dst offset.toNat bs := by simpa [hl, bs, lebBytes_encode] using hw
      simp [wasm_write_uleb, hs, hg, hl, hb, he, bs]
  · have hg : ¬(offset ≤ dst.size.toUInt32 ∧ UInt32.ofNat bs.length ≤ dst.size.toUInt32 - offset) := by
      intro hg
      have := (range_guard_iff _ _ _).mp hg
      rw [hn, hd] at this
      exact hb this
    rw [if_neg hb]
    exact write_uleb_refuses dst offset v fuel _ hs hg


/-- Complete SLEB writer contract for every Int64: termination, exact
canonical bytes and count on success, and complete storage preservation on
refusal. Eleven guard steps suffice, including the final writer guard. -/
theorem write_sleb_exact (dst : Array UInt8) (offset : UInt32) (v : Int64)
    (fuel : Nat) (hf : 11 ≤ fuel) (hsmall : dst.size < 2^32) :
    wasm_write_sleb dst offset v fuel =
      some (if offset.toNat + (WasmEncoding.encode 64 true v.toInt).length ≤ dst.size
        then (UInt32.ofNat (WasmEncoding.encode 64 true v.toInt).length,
          writeBytes dst offset.toNat (WasmEncoding.encode 64 true v.toInt))
        else (0, dst)) := by
  let bs := WasmEncoding.encode 64 true v.toInt
  have hlen : bs.length ≤ 10 := by
    have := WasmEncoding.encode_byte_budget (by decide : 0 < 64) (signed_range v)
    dsimp [bs]; omega
  have hn : (UInt32.ofNat bs.length).toNat = bs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hd : dst.size.toUInt32.toNat = dst.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hsmall]
  have hs := sleb_size_exact v fuel (by omega)
  change wasm_write_sleb dst offset v fuel = some (if offset.toNat + bs.length ≤ dst.size
    then (UInt32.ofNat bs.length, writeBytes dst offset.toNat bs) else (0, dst))
  by_cases hb : offset.toNat + bs.length ≤ dst.size
  · have hg : offset ≤ dst.size.toUInt32 ∧ UInt32.ofNat bs.length ≤ dst.size.toUInt32 - offset := by
      apply (range_guard_iff _ _ _).mpr
      rwa [hn, hd]
    have hw := sleb_loop_bytes offset (UInt32.ofNat bs.length) fuel dst v 0
      (by rw [hn]; omega) (by simp) (by rw [hn]; change bs.length - 0 < fuel; omega)
    simp only [UInt32.toNat_zero, Nat.add_zero, Nat.sub_zero, hn] at hw
    cases hl : wasm_write_sleb.loop1 dst offset (UInt32.ofNat bs.length) v 0 fuel with
    | none => simp [hl] at hw
    | some state =>
      rcases state with ⟨out, v', i'⟩
      have he : out = writeBytes dst offset.toNat bs := by simpa [hl, bs, lebBytes_encode] using hw
      simp [wasm_write_sleb, hs, hg, hl, hb, he, bs]
  · have hg : ¬(offset ≤ dst.size.toUInt32 ∧ UInt32.ofNat bs.length ≤ dst.size.toUInt32 - offset) := by
      intro hg
      have := (range_guard_iff _ _ _).mp hg
      rw [hn, hd] at this
      exact hb this
    rw [if_neg hb]
    exact write_sleb_refuses dst offset v fuel _ hs hg

/-- Every byte in the mathematical write window is the requested byte, and
all other bytes retain their original value. The footprint hypothesis rules
out the extraction's dropped-store behavior. -/
theorem writeBytes_get (dst : Array UInt8) (offset : Nat) (bs : List UInt8)
    (hfit : offset + bs.length ≤ dst.size) (j : Nat) :
    (writeBytes dst offset bs)[j]? =
      if offset ≤ j ∧ j < offset + bs.length then bs[j - offset]? else dst[j]? := by
  induction bs generalizing dst offset with
  | nil => simp only [writeBytes, List.length_nil, Nat.add_zero, if_neg (by omega : ¬(offset ≤ j ∧ j < offset))]
  | cons b bs ih =>
    rw [writeBytes, ih _ _ (by simp only [Array.size_setIfInBounds]; simp only [List.length_cons] at hfit; omega)]
    by_cases he : j = offset
    · subst j
      have ho : offset < dst.size := by simp only [List.length_cons] at hfit; omega
      rw [if_neg (by omega : ¬(offset + 1 ≤ offset ∧ offset < offset + 1 + bs.length)),
        if_pos (by simp only [List.length_cons]; omega : offset ≤ offset ∧ offset < offset + (b :: bs).length)]
      simp [ho]
    · by_cases hj : offset + 1 ≤ j ∧ j < offset + 1 + bs.length
      · have hg : offset ≤ j ∧ j < offset + (b :: bs).length := by simp only [List.length_cons]; omega
        have hn : j - offset = (j - (offset + 1)) + 1 := by omega
        rw [if_pos hj, if_pos hg, hn]
        rfl
      · have hg : ¬(offset ≤ j ∧ j < offset + (b :: bs).length) := by simp only [List.length_cons]; omega
        rw [if_neg hj, if_neg hg, Array.getElem?_setIfInBounds_ne (Ne.symm he)]

/-- Reading from the write offset yields exactly the emitted bytes followed
by the untouched original suffix. -/
theorem writeBytes_suffix (dst : Array UInt8) (offset : Nat) (bs : List UInt8)
    (hfit : offset + bs.length ≤ dst.size) :
    (writeBytes dst offset bs).toList.drop offset = bs ++ dst.toList.drop (offset + bs.length) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_drop, Array.getElem?_toList, List.getElem?_append]
  rw [writeBytes_get _ _ _ hfit]
  by_cases hj : j < bs.length
  · simp [hj, show offset ≤ offset + j ∧ offset + j < offset + bs.length by omega]
  · simp [hj, show offset + bs.length + (j - bs.length) = offset + j by omega]

/-- The independent decoder recovers every uint64 from the actual written
buffer and returns the original suffix beyond the exact encoded footprint. -/
theorem write_uleb_decode (dst out : Array UInt8) (offset written : UInt32) (v : UInt64)
    (fuel : Nat) (hf : 11 ≤ fuel) (hsmall : dst.size < 2^32)
    (hfit : offset.toNat + (WasmEncoding.encode 64 false v.toNat).length ≤ dst.size)
    (h : wasm_write_uleb dst offset v fuel = some (written, out)) :
    WasmLEB.decode 64 false (out.toList.drop offset.toNat) =
      some ((v.toNat : Int), dst.toList.drop (offset.toNat + (WasmEncoding.encode 64 false v.toNat).length)) := by
  rw [write_uleb_exact dst offset v fuel hf hsmall, if_pos hfit] at h
  cases h
  rw [writeBytes_suffix _ _ _ hfit]
  exact WasmEncoding.decode_encode (by decide) (unsigned_range v) _

/-- Signed decoding of the actual written buffer recovers every int64 and
leaves the original suffix intact, including at both signed endpoints. -/
theorem write_sleb_decode (dst out : Array UInt8) (offset written : UInt32) (v : Int64)
    (fuel : Nat) (hf : 11 ≤ fuel) (hsmall : dst.size < 2^32)
    (hfit : offset.toNat + (WasmEncoding.encode 64 true v.toInt).length ≤ dst.size)
    (h : wasm_write_sleb dst offset v fuel = some (written, out)) :
    WasmLEB.decode 64 true (out.toList.drop offset.toNat) =
      some (v.toInt, dst.toList.drop (offset.toNat + (WasmEncoding.encode 64 true v.toInt).length)) := by
  rw [write_sleb_exact dst offset v fuel hf hsmall, if_pos hfit] at h
  cases h
  rw [writeBytes_suffix _ _ _ hfit]
  exact WasmEncoding.decode_encode (by decide) (signed_range v) _

end Oak.WasmAssembler
