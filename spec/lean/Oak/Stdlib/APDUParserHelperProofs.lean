import Oak.Stdlib.APDUParserRefinement

/-!
Source-only bottom-up helper proof candidate. UNCOMPILED.
The generated APDU terms, reader bridge and unchanged length model are imports.
No imported bytes, proof budgets, parser branches or model declarations change.
All helper equations quantify over arbitrary fuel. Size is bounded only by 2^32.
-/
set_option autoImplicit false

namespace Oak.Stdlib.APDUParserHelperProofs
open APDUExtracted APDUParserRefinement

/-- Add only the four retained header observations to an existing model result. -/
def attachHeader (h : HeaderObs) (r : Except APDUModel.Error APDUModel.Lengths) :
    Except APDUModel.Error CommandObs :=
  match r with
  | .error e => .error e
  | .ok lengths => .ok ⟨h, lengths⟩

def sourceInput (src : Array UInt8) : APDUModel.Input :=
  APDUModel.observe (sourceBytes src)

def sourceWindow (src : Array UInt8) (k : Nat) : encoding_sreader__Window :=
  { next := k.toUInt32, end_ := src.size.toUInt32 }

/-- This is only the extended branch of the unchanged model, including its order. -/
def extendedSpec (x : APDUModel.Input) : Except APDUModel.Error APDUModel.Lengths :=
  if x.n < 7 then .error .truncatedLength
  else if x.n = 7 then .ok (APDUModel.layout x .case2Extended)
  else if x.word.val = 0 then .error .zeroDataLength
  else APDUModel.extendedData x

/-- Reuse the accepted reader's exact emitted BE16 value expression. -/
abbrev wordAt (src : Array UInt8) (k : Nat) : UInt16 :=
  BoundedReaderRefinement.be16ValueExpr (src.getD k 0) (src.getD (k + 1) 0)

@[simp] theorem sourceBytes_length (src : Array UInt8) :
    (sourceBytes src).length = src.size := by
  simp [sourceBytes]

/-- Total default-preserving observation, including indices outside the array. -/
@[simp] theorem source_byteAt (src : Array UInt8) (k : Nat) :
    APDUModel.byteAt (sourceBytes src) k = liftByte (src.getD k 0) := by
  simp only [APDUModel.byteAt, sourceBytes, List.getD_eq_getElem?_getD,
    List.getElem?_map, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  cases src[k]? <;> rfl

@[simp] theorem sourceInput_n (src : Array UInt8) :
    (sourceInput src).n = src.size := by
  simp [sourceInput, APDUModel.observe]

@[simp] theorem sourceInput_first (src : Array UInt8) :
    (sourceInput src).first = liftByte (src.getD 4 0) := by
  simp [sourceInput, APDUModel.observe]

@[simp] theorem sourceInput_shortLe (src : Array UInt8) :
    (sourceInput src).shortLe = liftByte (src.getD (src.size - 1) 0) := by
  simp [sourceInput, APDUModel.observe]

theorem wordAt_toNat (src : Array UInt8) (k : Nat) :
    (wordAt src k).toNat =
      256 * (src.getD k 0).toNat + (src.getD (k + 1) 0).toNat := by
  exact BoundedReaderRefinement.be16ValueExpr_toNat _ _

@[simp] theorem sourceInput_word (src : Array UInt8) :
    (sourceInput src).word = liftWord (wordAt src 5) := by
  apply Fin.ext
  change 256 * (APDUModel.byteAt (sourceBytes src) 5).val +
    (APDUModel.byteAt (sourceBytes src) 6).val = (wordAt src 5).toNat
  rw [wordAt_toNat, source_byteAt, source_byteAt]
  rfl

theorem sourceInput_extendedLe (src : Array UInt8) (h : 2 ≤ src.size) :
    (sourceInput src).extendedLe = liftWord (wordAt src (src.size - 2)) := by
  have hi : src.size - 2 + 1 = src.size - 1 := by omega
  simp only [sourceInput, APDUModel.observe, sourceBytes_length]
  apply Fin.ext
  change 256 * (APDUModel.byteAt (sourceBytes src) (src.size - 2)).val +
    (APDUModel.byteAt (sourceBytes src) (src.size - 1)).val =
      (wordAt src (src.size - 2)).toNat
  simpa only [source_byteAt, liftByte, hi] using
    (wordAt_toNat src (src.size - 2)).symm

theorem nat32_toNat (n : Nat) (hn : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  change (UInt32.ofNat n).toNat = n
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

theorem u8_zero_iff (u : UInt8) : u = 0 ↔ u.toNat = 0 := by
  constructor
  · intro h; cases h; rfl
  · intro h
    exact BoundedReaderRefinement.u8_toNat_injective h

theorem u16_zero_iff (u : UInt16) : u = 0 ↔ u.toNat = 0 := by
  constructor
  · intro h; cases h; rfl
  · intro h
    exact BoundedReaderRefinement.u16_toNat_injective h

theorem u32_eq_iff (a b : UInt32) : a = b ↔ a.toNat = b.toNat := by
  constructor
  · exact congrArg UInt32.toNat
  · intro h
    exact BoundedReaderRefinement.u32_toNat_injective h

theorem u32_beq_nat (a b : UInt32) :
    (a == b) = decide (a.toNat = b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [u32_eq_iff]

theorem u16_beq_zero (u : UInt16) :
    (u == (0 : UInt16)) = decide (u.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp [u16_zero_iff]

theorem short_response_raw (u : UInt8) (fuel : Nat) :
    smartcard_sapdu__short_uresponse u fuel =
      some (APDUModel.shortResponse (liftByte u)).toUInt32 := by
  by_cases h : u = 0
  · subst u; rfl
  · have hn : u.toNat ≠ 0 := by simpa [u8_zero_iff] using h
    have hc : u.toUInt32 = u.toNat.toUInt32 := by
      apply BoundedReaderRefinement.u32_toNat_injective
      rw [UInt8.toNat_toUInt32, nat32_toNat]
      have hu := u.toNat_lt
      omega
    have hb : (u == (0 : UInt8)) = false := by simp [h]
    change some (if u == 0 then (256 : UInt32) else u.toUInt32) =
      some ((if u.toNat = 0 then 256 else u.toNat).toUInt32)
    rw [hb]
    change some u.toUInt32 = some ((if u.toNat = 0 then 256 else u.toNat).toUInt32)
    rw [if_neg hn]
    exact congrArg some hc

theorem extended_response_raw (u : UInt16) (fuel : Nat) :
    smartcard_sapdu__extended_uresponse u fuel =
      some (APDUModel.extendedResponse (liftWord u)).toUInt32 := by
  by_cases h : u = 0
  · subst u; rfl
  · have hn : u.toNat ≠ 0 := by simpa [u16_zero_iff] using h
    have hc : u.toUInt32 = u.toNat.toUInt32 := by
      apply BoundedReaderRefinement.u32_toNat_injective
      rw [UInt16.toNat_toUInt32, nat32_toNat]
      have hu := u.toNat_lt
      omega
    have hb : (u == (0 : UInt16)) = false := by simp [h]
    change some (if u == 0 then (65536 : UInt32) else u.toUInt32) =
      some ((if u.toNat = 0 then 65536 else u.toNat).toUInt32)
    rw [hb]
    change some u.toUInt32 = some ((if u.toNat = 0 then 65536 else u.toNat).toUInt32)
    rw [if_neg hn]
    exact congrArg some hc

@[simp] theorem short_response_toNat (u : UInt8) :
    (APDUModel.shortResponse (liftByte u)).toUInt32.toNat =
      APDUModel.shortResponse (liftByte u) := by
  apply nat32_toNat
  have hb := APDUModel.short_response_bounds (liftByte u)
  omega

@[simp] theorem extended_response_toNat (u : UInt16) :
    (APDUModel.extendedResponse (liftWord u)).toUInt32.toNat =
      APDUModel.extendedResponse (liftWord u) := by
  apply nat32_toNat
  have hb := APDUModel.extended_response_bounds (liftWord u)
  omega

theorem short_response_eq (u : UInt8) (fuel : Nat) :
    Option.map UInt32.toNat (smartcard_sapdu__short_uresponse u fuel) =
      some (APDUModel.shortResponse (liftByte u)) := by
  rw [short_response_raw]
  change some ((APDUModel.shortResponse (liftByte u)).toUInt32.toNat) =
    some (APDUModel.shortResponse (liftByte u))
  exact congrArg some (short_response_toNat u)

theorem extended_response_eq (u : UInt16) (fuel : Nat) :
    Option.map UInt32.toNat (smartcard_sapdu__extended_uresponse u fuel) =
      some (APDUModel.extendedResponse (liftWord u)) := by
  rw [extended_response_raw]
  change some ((APDUModel.extendedResponse (liftWord u)).toUInt32.toNat) =
    some (APDUModel.extendedResponse (liftWord u))
  apply congrArg some
  apply nat32_toNat
  have hb := APDUModel.extended_response_bounds (liftWord u)
  omega

theorem short_response_sentinel (fuel : Nat) :
    smartcard_sapdu__short_uresponse 0 fuel = some 256 := by rfl

theorem extended_response_sentinel (fuel : Nat) :
    smartcard_sapdu__extended_uresponse 0 fuel = some 65536 := by rfl

theorem short_response_bounds (u : UInt8) (fuel : Nat) (r : UInt32)
    (hr : smartcard_sapdu__short_uresponse u fuel = some r) :
    1 ≤ r.toNat ∧ r.toNat ≤ 256 := by
  have h := short_response_eq u fuel
  rw [hr] at h
  have hv : r.toNat = APDUModel.shortResponse (liftByte u) := Option.some.inj h
  rw [hv]
  exact APDUModel.short_response_bounds _

theorem extended_response_bounds (u : UInt16) (fuel : Nat) (r : UInt32)
    (hr : smartcard_sapdu__extended_uresponse u fuel = some r) :
    1 ≤ r.toNat ∧ r.toNat ≤ 65536 := by
  have h := extended_response_eq u fuel
  rw [hr] at h
  have hv : r.toNat = APDUModel.extendedResponse (liftWord u) := Option.some.inj h
  rw [hv]
  exact APDUModel.extended_response_bounds _

theorem sourceWindow_lift (src : Array UInt8) (k : Nat)
    (hSize : src.size < 2 ^ 32) (hk : k ≤ src.size) :
    BoundedReaderRefinement.liftWindow
      (APDUReaderBridge.toReaderWindow (sourceWindow src k)) = ⟨k, src.size⟩ := by
  have hk32 : k < 2 ^ 32 := by omega
  simp [BoundedReaderRefinement.liftWindow, APDUReaderBridge.toReaderWindow,
    sourceWindow, nat32_toNat k hk32, nat32_toNat src.size hSize]

theorem sourceWindow_valid (src : Array UInt8) (k : Nat)
    (hSize : src.size < 2 ^ 32) (hk : k ≤ src.size) :
    ReaderModel.Valid src.size (BoundedReaderRefinement.liftWindow
      (APDUReaderBridge.toReaderWindow (sourceWindow src k))) := by
  rw [sourceWindow_lift src k hSize hk]
  exact ⟨hk, Nat.le_refl _⟩

theorem sourceWindow_remaining_nat (src : Array UInt8) (k : Nat)
    (hSize : src.size < 2 ^ 32) (hk : k ≤ src.size) :
    (src.size.toUInt32 - k.toUInt32).toNat = src.size - k := by
  have hk32 : k < 2 ^ 32 := by omega
  rw [BoundedReaderRefinement.u32_sub_toNat]
  · rw [nat32_toNat src.size hSize, nat32_toNat k hk32]
  · simpa [nat32_toNat src.size hSize, nat32_toNat k hk32] using hk

theorem sourceWindow_advance (src : Array UInt8) (k : Nat) (count : UInt32)
    (hSize : src.size < 2 ^ 32) (hk : k ≤ src.size)
    (hc : count.toNat ≤ src.size - k) :
    k.toUInt32 + count = (k + count.toNat).toUInt32 := by
  have hk32 : k < 2 ^ 32 := by omega
  have hs32 : k + count.toNat < 2 ^ 32 := by omega
  apply BoundedReaderRefinement.u32_toNat_injective
  rw [BoundedReaderRefinement.u32_add_toNat]
  · rw [nat32_toNat k hk32, nat32_toNat _ hs32]
  · simpa [nat32_toNat k hk32] using hs32

theorem take_source_short (src : Array UInt8) (k : Nat) (count : UInt32)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) (hk : k ≤ src.size)
    (hc : src.size - k < count.toNat) :
    encoding_sreader__take (sourceWindow src k) src count fuel =
      some (.Err .InsufficientData) := by
  apply APDUReaderBridge.take_short_raw src _ count fuel hSize
    (sourceWindow_valid src k hSize hk)
  have hk32 : k < 2 ^ 32 := by omega
  simpa [sourceWindow, nat32_toNat k hk32, nat32_toNat src.size hSize] using hc

theorem take_source_good (src : Array UInt8) (k : Nat) (count : UInt32)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) (hk : k ≤ src.size)
    (hc : count.toNat ≤ src.size - k) :
    encoding_sreader__take (sourceWindow src k) src count fuel =
      some (.Ok { offset := k.toUInt32, length := count, rest := sourceWindow src (k + count.toNat) }) := by
  have hk32 : k < 2 ^ 32 := by omega
  have ht := APDUReaderBridge.take_good_raw src (sourceWindow src k) count fuel hSize
    (sourceWindow_valid src k hSize hk)
    (by simpa [sourceWindow, nat32_toNat k hk32, nat32_toNat src.size hSize] using hc)
  simpa only [sourceWindow, sourceWindow_advance src k count hSize hk hc] using ht

theorem read_u8_source_good (src : Array UInt8) (k : Nat) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hk : k < src.size) :
    encoding_sreader__read_uu8 (sourceWindow src k) src fuel =
      some (.Ok { value := src.getD k 0, rest := sourceWindow src (k + 1) }) := by
  have ht := take_source_good src k 1 fuel hSize (by omega) (by change 1 ≤ src.size - k; omega)
  have hr := APDUReaderBridge.read_u8_from_take (sourceWindow src k) src fuel _ ht
  have hk32 : k < 2 ^ 32 := by omega
  simpa [nat32_toNat k hk32] using hr

theorem read_be16_source_short (src : Array UInt8) (k : Nat) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hk : k ≤ src.size) (hs : src.size - k < 2) :
    encoding_sreader__read_uu16_ube (sourceWindow src k) src fuel =
      some (.Err .InsufficientData) := by
  apply APDUReaderBridge.read_be16_short_raw src _ fuel hSize
    (sourceWindow_valid src k hSize hk)
  have hk32 : k < 2 ^ 32 := by omega
  simpa [sourceWindow, nat32_toNat k hk32, nat32_toNat src.size hSize] using hs

theorem read_be16_source_good (src : Array UInt8) (k : Nat) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hk : k + 2 ≤ src.size) :
    encoding_sreader__read_uu16_ube (sourceWindow src k) src fuel =
      some (.Ok { value := wordAt src k, rest := sourceWindow src (k + 2) }) := by
  have hkn : k ≤ src.size := by omega
  have hlift := sourceWindow_lift src k hSize hkn
  have hg : BoundedReaderRefinement.Good src
      (BoundedReaderRefinement.liftWindow
        (APDUReaderBridge.toReaderWindow (sourceWindow src k))) := by
    rw [hlift]
    change (k ≤ src.size ∧ src.size ≤ src.size) ∧ 2 ≤ src.size - k
    exact ⟨⟨hkn, Nat.le_refl _⟩, by omega⟩
  have hr := APDUReaderBridge.read_be16_good_raw src (sourceWindow src k) fuel hSize hg
  have hi : k < src.size := by omega
  have hj : k + 1 < src.size := by omega
  have hv0 : BoundedReaderRefinement.checkedHi src
      (BoundedReaderRefinement.liftWindow
        (APDUReaderBridge.toReaderWindow (sourceWindow src k))) hg = src.getD k 0 := by
    simp only [BoundedReaderRefinement.checkedHi, hlift]
    exact (BoundedReaderRefinement.getD_checked src k 0 hi).symm
  have hv1 : BoundedReaderRefinement.checkedLo src
      (BoundedReaderRefinement.liftWindow
        (APDUReaderBridge.toReaderWindow (sourceWindow src k))) hg = src.getD (k + 1) 0 := by
    simp only [BoundedReaderRefinement.checkedLo, hlift]
    exact (BoundedReaderRefinement.getD_checked src (k + 1) 0 hj).symm
  have ha : k.toUInt32 + (2 : UInt32) = (k + 2).toUInt32 :=
    sourceWindow_advance src k 2 hSize hkn (by change 2 ≤ src.size - k; omega)
  rw [hv0, hv1] at hr
  simpa only [sourceWindow, ha] using hr

@[simp] theorem sourceInput_first_value (src : Array UInt8) :
    (sourceInput src).first.val = (src.getD 4 0).toNat := by
  rw [sourceInput_first]
  rfl

theorem read_first_byte (src : Array UInt8) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hEntry : 5 ≤ src.size) :
    encoding_sreader__read_uu8 (sourceWindow src 4) src fuel =
      some (.Ok { value := src.getD 4 0, rest := sourceWindow src 5 }) := by
  exact read_u8_source_good src 4 fuel hSize (by omega)

/-- Count zero is allowed: positivity belongs to the caller's marker branch. -/
theorem short_data_eq (src : Array UInt8) (header : smartcard_sapdu__Header)
    (count : UInt32) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hEntry : 5 ≤ src.size) (hCount : count.toNat = (sourceInput src).first.val) :
    Option.map liftResult
      (smartcard_sapdu__short_udata header (sourceWindow src 5) src count fuel) =
      some (attachHeader (liftHeader header) (APDUModel.shortData (sourceInput src))) := by
  have hn : (UInt32.ofNat src.size).toNat = src.size := nat32_toNat src.size hSize
  have hm : (sourceInput src).n = src.size := sourceInput_n src
  by_cases hc : count.toNat > src.size - 5
  · have ht := take_source_short src 5 count fuel hSize hEntry hc
    simp only [APDUModel.shortData, hm, ← hCount, if_pos hc, attachHeader]
    simp [smartcard_sapdu__short_udata, ht, liftResult, liftError]
  · have hFits : count.toNat ≤ src.size - 5 := by omega
    have ht := take_source_good src 5 count fuel hSize hEntry hFits
    have hRest : 5 + count.toNat ≤ src.size := by omega
    have hTrailing : (UInt32.ofNat src.size - ((5 : UInt32) + count)).toNat =
        src.size - (5 + count.toNat) := by
      simpa using sourceWindow_remaining_nat src (5 + count.toNat) hSize hRest
    have hNext : (sourceWindow src (5 + count.toNat)).next =
      (5 + count.toNat).toUInt32 := rfl
    by_cases h0 : src.size - (5 + count.toNat) = 0
    · simp only [APDUModel.shortData, hm, ← hCount, if_neg hc, if_pos h0,
        attachHeader, APDUModel.layout]
      rw [smartcard_sapdu__short_udata, ht]
      simp [u32_beq_nat, hNext,
        hTrailing, h0, smartcard_sapdu__command, liftResult, liftCommand,
        liftHeader, liftCase, liftResponse, hn]
    · by_cases h1 : src.size - (5 + count.toNat) = 1
      · have hIndex : 5 + count.toNat = src.size - 1 := by omega
        have hIn : 5 + count.toNat < src.size := by omega
        have hr := read_u8_source_good src (5 + count.toNat) fuel hSize hIn
        simp only [APDUModel.shortData, hm, ← hCount, if_neg hc, if_neg h0,
          if_pos h1, attachHeader, APDUModel.layout]
        rw [smartcard_sapdu__short_udata, ht]
        simp [u32_beq_nat, hNext, hTrailing, h1, hr, short_response_raw,
          smartcard_sapdu__command, liftResult, liftCommand, liftHeader,
          liftCase, liftResponse, hn]
        rw [hIndex]
        have hb := APDUModel.short_response_bounds (liftByte (src.getD (src.size - 1) 0))
        simp only [Array.getD_eq_getD_getElem?] at hb
        simp <;> omega
      · simp only [APDUModel.shortData, hm, ← hCount, if_neg hc, if_neg h0,
          if_neg h1, attachHeader]
        rw [smartcard_sapdu__short_udata, ht]
        simp [u32_beq_nat, hNext, hTrailing, h0, h1, liftResult, liftError]

/-- Count zero is allowed, as in the source helper. Only its dispatcher rejects zero Lc. -/
theorem extended_data_eq (src : Array UInt8) (header : smartcard_sapdu__Header)
    (count : UInt32) (fuel : Nat) (hSize : src.size < 2 ^ 32)
    (hEntry : 7 ≤ src.size) (hCount : count.toNat = (sourceInput src).word.val) :
    Option.map liftResult
      (smartcard_sapdu__extended_udata header (sourceWindow src 7) src count fuel) =
      some (attachHeader (liftHeader header) (APDUModel.extendedData (sourceInput src))) := by
  have hn : (UInt32.ofNat src.size).toNat = src.size := nat32_toNat src.size hSize
  have hm : (sourceInput src).n = src.size := sourceInput_n src
  by_cases hc : count.toNat > src.size - 7
  · have ht := take_source_short src 7 count fuel hSize hEntry hc
    simp only [APDUModel.extendedData, hm, ← hCount, if_pos hc, attachHeader]
    simp [smartcard_sapdu__extended_udata, ht, liftResult, liftError]
  · have hFits : count.toNat ≤ src.size - 7 := by omega
    have ht := take_source_good src 7 count fuel hSize hEntry hFits
    have hRest : 7 + count.toNat ≤ src.size := by omega
    have hTrailing : (UInt32.ofNat src.size - ((7 : UInt32) + count)).toNat =
        src.size - (7 + count.toNat) := by
      simpa using sourceWindow_remaining_nat src (7 + count.toNat) hSize hRest
    have hNext : (sourceWindow src (7 + count.toNat)).next =
      (7 + count.toNat).toUInt32 := rfl
    by_cases h0 : src.size - (7 + count.toNat) = 0
    · simp only [APDUModel.extendedData, hm, ← hCount, if_neg hc, if_pos h0,
        attachHeader, APDUModel.layout]
      rw [smartcard_sapdu__extended_udata, ht]
      simp [u32_beq_nat, hNext,
        hTrailing, h0, smartcard_sapdu__command, liftResult, liftCommand,
        liftHeader, liftCase, liftResponse, hn]
    · by_cases h1 : src.size - (7 + count.toNat) = 1
      · simp only [APDUModel.extendedData, hm, ← hCount, if_neg hc, if_neg h0,
          if_pos h1, attachHeader]
        rw [smartcard_sapdu__extended_udata, ht]
        simp [u32_beq_nat, hNext, hTrailing, h1, liftResult, liftError]
      · by_cases h2 : src.size - (7 + count.toNat) = 2
        · have hIndex : 7 + count.toNat = src.size - 2 := by omega
          have hIn : 7 + count.toNat + 2 ≤ src.size := by omega
          have hr := read_be16_source_good src (7 + count.toNat) fuel hSize hIn
          have hLe := sourceInput_extendedLe src (by omega)
          simp only [APDUModel.extendedData, hm, ← hCount, if_neg hc, if_neg h0,
            if_neg h1, if_pos h2, attachHeader, APDUModel.layout]
          rw [smartcard_sapdu__extended_udata, ht]
          simp [u32_beq_nat, hNext, hTrailing, h2, hr, extended_response_raw,
            smartcard_sapdu__command, liftResult, liftCommand, liftHeader,
            liftCase, liftResponse, hn]
          rw [hLe, hIndex]
          have hb := APDUModel.extended_response_bounds (liftWord (wordAt src (src.size - 2)))
          simp <;> omega
        · simp only [APDUModel.extendedData, hm, ← hCount, if_neg hc, if_neg h0,
            if_neg h1, if_neg h2, attachHeader]
          rw [smartcard_sapdu__extended_udata, ht]
          simp [u32_beq_nat, hNext, hTrailing, h0, h1, h2, liftResult, liftError]

/-- The helper never tests byte 4; no zero-marker premise is imposed here. -/
theorem extended_eq (src : Array UInt8) (header : smartcard_sapdu__Header)
    (fuel : Nat) (hSize : src.size < 2 ^ 32) (hEntry : 5 ≤ src.size) :
    Option.map liftResult
      (smartcard_sapdu__extended header (sourceWindow src 5) src fuel) =
      some (attachHeader (liftHeader header) (extendedSpec (sourceInput src))) := by
  have hn : (UInt32.ofNat src.size).toNat = src.size := nat32_toNat src.size hSize
  have hm : (sourceInput src).n = src.size := sourceInput_n src
  by_cases hShort : src.size < 7
  · have hr := read_be16_source_short src 5 fuel hSize hEntry (by omega)
    rw [smartcard_sapdu__extended, hr]
    simp [liftResult, liftError, extendedSpec, attachHeader, hShort]
  · have h7 : 7 ≤ src.size := by omega
    have hr := read_be16_source_good src 5 fuel hSize (by omega)
    have hw : (sourceInput src).word.val = (wordAt src 5).toNat := by
      rw [sourceInput_word]
      rfl
    by_cases hSeven : src.size = 7
    · rw [smartcard_sapdu__extended, hr]
      simp only [u32_beq_nat, hn]
      have hb := APDUModel.extended_response_bounds (liftWord (wordAt src 5))
      simp [hSeven, extended_response_raw, smartcard_sapdu__command,
        liftResult, liftCommand, liftHeader, liftCase, liftResponse,
        extendedSpec, attachHeader, APDUModel.layout] <;> omega
    · by_cases hZero : (wordAt src 5).toNat = 0
      · have hZero' := hZero
        simp at hZero'
        rw [smartcard_sapdu__extended, hr]
        simp only [u32_beq_nat, u16_beq_zero, hn]
        simp only [extendedSpec, hm, hw, if_neg hShort, if_neg hSeven, if_pos hZero]
        simp [hSeven, hZero', attachHeader, liftResult, liftError]
      · have hCount : (wordAt src 5).toUInt32.toNat = (sourceInput src).word.val := by
          rw [UInt16.toNat_toUInt32, hw]
        have hd := extended_data_eq src header (wordAt src 5).toUInt32 fuel hSize h7 hCount
        have hZero' := hZero
        simp at hZero'
        rw [smartcard_sapdu__extended, hr]
        simp only [u32_beq_nat, u16_beq_zero, hn]
        simp only [extendedSpec, hm, hw, if_neg hShort, if_neg hSeven, if_neg hZero]
        simp at hd
        simp [hSeven]
        split <;> simp_all

end Oak.Stdlib.APDUParserHelperProofs
