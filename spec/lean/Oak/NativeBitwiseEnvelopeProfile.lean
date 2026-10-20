import Oak.NativeBitwiseEnvelopeSpec

/-!
# Universal recognition of the independent envelope

Field decoding uses a natural-number little-endian roundtrip theorem and
in-bounds slices of the concatenated specification. Names are checked by a
universal terminating-NUL argument. Body bytes are arbitrary at the admitted
architecture-specific extent; this proves serialization and strict recognition,
not source provenance, body execution, host ELF loading, or a broader ABI.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine readLE)
open Oak.NativeBitwiseObject (fromUInt8 toUInt8)

def decode (bs : Bytes) : Nat := bs.foldr (fun b n => b.toNat + 256*n) 0

theorem decode_wordBytes (n width : Nat) (h : n < 256^width) :
    decode (wordBytes n width) = n := by
  induction width generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn, decode, wordBytes]
  | succ k ih =>
    have hd : n / 256 < 256^k := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa [Nat.pow_succ] using h
    change (UInt8.ofNat (n % 256)).toNat + 256 * decode (wordBytes (n / 256) k) = n
    rw [ih _ hd]
    simp only [UInt8.toNat_ofNat', Nat.mod_mod]
    exact Nat.mod_add_div n 256

theorem decode_word32Bytes (n : Nat) (h : n < 2^32) : decode (word32Bytes n) = n := by
  apply decode_wordBytes
  exact h

theorem decode_dwordBytes (n : Nat) (h : n < 2^32) : decode (dwordBytes n) = n := by
  have hd : decode (dwordBytes n) = decode (word32Bytes n) := by
    simp only [dwordBytes, decode, List.foldr_append]
    rfl
  rw [hd, decode_word32Bytes n h]

theorem readLE_slice (bs : Bytes) (off count : Nat) :
    readLE (fromUInt8 bs) off count = decode (slice bs off count) := by
  rw [readLE, ← fromUInt8_slice]
  simp [fromUInt8, decode, List.foldr_map]

theorem slice_slice (bs : Bytes) (start width off count : Nat) (h : off+count ≤ width) :
    slice (slice bs start width) off count = slice bs (start+off) count := by
  simp [slice, List.drop_take, List.drop_drop, List.take_take,
    Nat.min_eq_left (show count ≤ width-off by omega)]

theorem readLE_in_slice (bs chunk : Bytes) (start width off count : Nat)
    (he : slice bs start width = chunk) (h : off+count ≤ width) :
    readLE (fromUInt8 bs) (start+off) count = readLE (fromUInt8 chunk) off count := by
  simp only [readLE_slice]
  rw [← slice_slice bs start width off count h, he]


theorem header_fields (m : Machine) (name : Bytes)
    (hs : Oak.NativeBitwiseImage.shOffset m (fromUInt8 name) < 2^32) :
    slice (header m name) 0 16 = [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0] ∧
    readLE (fromUInt8 (header m name)) 16 2 = 2 ∧
    readLE (fromUInt8 (header m name)) 18 2 = m.number ∧
    readLE (fromUInt8 (header m name)) 20 4 = 1 ∧
    readLE (fromUInt8 (header m name)) 24 8 = Oak.NativeBitwiseImage.base ∧
    readLE (fromUInt8 (header m name)) 32 8 = 64 ∧
    readLE (fromUInt8 (header m name)) 40 8 = Oak.NativeBitwiseImage.shOffset m (fromUInt8 name) ∧
    readLE (fromUInt8 (header m name)) 48 4 = m.abiFlags ∧
    readLE (fromUInt8 (header m name)) 52 2 = 64 ∧
    readLE (fromUInt8 (header m name)) 54 2 = 56 ∧
    readLE (fromUInt8 (header m name)) 56 2 = 1 ∧
    readLE (fromUInt8 (header m name)) 58 2 = 64 ∧
    readLE (fromUInt8 (header m name)) 60 2 = 6 ∧
    readLE (fromUInt8 (header m name)) 62 2 = 5 := by
  cases m <;>
    simp (disch := (try (first | omega | (simp only [word32Bytes_length,
      dwordBytes_length, List.length_replicate, List.length_append] <;> omega)))) only
      [readLE_slice, List.length_append, header, Oak.NativeBitwiseImage.base, Machine.number, Machine.abiFlags,
       slice_append_left, slice_append_right, slice_all, word32Bytes_length, dwordBytes_length,
       List.length_replicate, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
       decode_word32Bytes, decode_dwordBytes] <;>
    simp [slice, word32Bytes, wordBytes, decode]


theorem section_fields (s : Oak.NativeBitwiseObject.Section)
    (h : ∀ v ∈ [s.name,s.kind,s.flags,s.address,s.offset,s.size,s.link,s.info,s.alignment,s.entrySize], v < 2^32) :
    readLE (fromUInt8 (sectionBytes s)) 0 4 = s.name ∧
    readLE (fromUInt8 (sectionBytes s)) 4 4 = s.kind ∧
    readLE (fromUInt8 (sectionBytes s)) 8 8 = s.flags ∧
    readLE (fromUInt8 (sectionBytes s)) 16 8 = s.address ∧
    readLE (fromUInt8 (sectionBytes s)) 24 8 = s.offset ∧
    readLE (fromUInt8 (sectionBytes s)) 32 8 = s.size ∧
    readLE (fromUInt8 (sectionBytes s)) 40 4 = s.link ∧
    readLE (fromUInt8 (sectionBytes s)) 44 4 = s.info ∧
    readLE (fromUInt8 (sectionBytes s)) 48 8 = s.alignment ∧
    readLE (fromUInt8 (sectionBytes s)) 56 8 = s.entrySize := by
  simp only [List.mem_cons, forall_eq_or_imp] at h
  simp (disch := (try (first | omega | (simp only [word32Bytes_length,
    dwordBytes_length, List.length_append] <;> omega)))) only
    [readLE_slice, sectionBytes, List.length_append, word32Bytes_length, dwordBytes_length,
     Nat.reduceAdd, Nat.reduceSub, slice_append_left, slice_append_right, slice_all,
     decode_word32Bytes, decode_dwordBytes, and_self]

theorem program_fields (m : Machine) :
    readLE (fromUInt8 (programBytes m)) 0 4 = 1 ∧
    readLE (fromUInt8 (programBytes m)) 4 4 = 5 ∧
    readLE (fromUInt8 (programBytes m)) 8 8 = 4096 ∧
    readLE (fromUInt8 (programBytes m)) 16 8 = 65536 ∧
    readLE (fromUInt8 (programBytes m)) 24 8 = 65536 ∧
    readLE (fromUInt8 (programBytes m)) 32 8 = Oak.NativeBitwiseImage.loadSize m ∧
    readLE (fromUInt8 (programBytes m)) 40 8 = Oak.NativeBitwiseImage.loadSize m ∧
    readLE (fromUInt8 (programBytes m)) 48 8 = 4096 := by
  cases m <;> simp [programBytes, readLE_slice, slice, decode, dwordBytes,
    word32Bytes, wordBytes, Oak.NativeBitwiseImage.base,
    Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.loadSize]

theorem readSection_of_slice (bs : Bytes) (s : Oak.NativeBitwiseObject.Section)
    (table index : Nat)
    (ht : readLE (fromUInt8 bs) 40 8 = table)
    (he : readLE (fromUInt8 bs) 58 2 = 64)
    (hi : index < readLE (fromUInt8 bs) 60 2)
    (hb : table + index*64 + 64 ≤ bs.length)
    (hx : slice bs (table + index*64) 64 = sectionBytes s)
    (hv : ∀ v ∈ [s.name,s.kind,s.flags,s.address,s.offset,s.size,s.link,s.info,s.alignment,s.entrySize], v < 2^32) :
    Oak.NativeBitwiseObject.readSection (fromUInt8 bs) index = some s := by
  have hr := readLE_in_slice bs (sectionBytes s) (table+index*64) 64
  have h0 := hr 0 4 hx (by omega)
  have h4 := hr 4 4 hx (by omega)
  have h8 := hr 8 8 hx (by omega)
  have h16 := hr 16 8 hx (by omega)
  have h24 := hr 24 8 hx (by omega)
  have h32 := hr 32 8 hx (by omega)
  have h40 := hr 40 4 hx (by omega)
  have h44 := hr 44 4 hx (by omega)
  have h48 := hr 48 8 hx (by omega)
  have h56 := hr 56 8 hx (by omega)
  simp only [Nat.add_zero] at h0
  have hf := section_fields s hv
  rcases hf with ⟨f0,f4,f8,f16,f24,f32,f40,f44,f48,f56⟩
  have hlen : 64 ≤ bs.length := by omega
  simp only [Oak.NativeBitwiseObject.readSection, ht, he, hi, Oak.NativeBitwiseObject.fromUInt8_length,
    hlen, hb, and_self, ↓reduceIte, h0,h4,h8,h16,h24,h32,h40,h44,h48,h56,
    f0,f4,f8,f16,f24,f32,f40,f44,f48,f56]


theorem readLE_in_window (bs chunk : Bytes) (start width off count : Nat)
    (he : slice bs start width = chunk) (hlo : start ≤ off) (hhi : off+count ≤ start+width) :
    readLE (fromUInt8 bs) off count = readLE (fromUInt8 chunk) (off-start) count := by
  have hr := readLE_in_slice bs chunk start width (off-start) count he (by omega)
  simpa [Nat.add_sub_of_le hlo] using hr

theorem E_header_program (m : Machine) (name body : Bytes)
    (hn : name.length ≤ 256) (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    Oak.NativeBitwiseImage.Header m (fromUInt8 name) (fromUInt8 (E m name body)) ∧
    Oak.NativeBitwiseImage.Program m (fromUInt8 (E m name body)) := by
  have hlen := E_length m name body hb
  have hsz := E_size_bound m name body hn hb
  have hs := (shOffset_bounds m name).1
  have hsh : Oak.NativeBitwiseImage.shOffset m (fromUInt8 name) < 2^32 := by omega
  have hbnd : 120 ≤ (E m name body).length := by
    cases m <;> simp_all [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset,
      Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.textOffset,
      Oak.NativeBitwiseImage.loadSize] <;> omega
  obtain ⟨hh,hp,_⟩ := E_slices m name body hb
  have rh := readLE_in_window (E m name body) (header m name) 0 64
  have rp := readLE_in_window (E m name body) (programBytes m) 64 56
  obtain ⟨hm,h16,h18,h20,h24,h32,h40,h48,h52,h54,h56,h58,h60,h62⟩ := header_fields m name hsh
  obtain ⟨p0,p4,p8,p16,p24,p32,p40,p48⟩ := program_fields m
  have hmagic : Oak.MinimalELF.slice (fromUInt8 (E m name body)) 0 16 =
      [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0] := by
    have hx : slice (E m name body) 0 16 = slice (header m name) 0 16 := by
      rw [← hh, slice_slice _ 0 64 0 16 (by omega), Nat.add_zero]
    rw [← fromUInt8_slice, hx, hm]
    rfl
  unfold Oak.NativeBitwiseImage.Header Oak.MinimalELF.Header Oak.NativeBitwiseImage.Program
    Oak.MinimalELF.segment Oak.NativeBitwiseImage.program
  simp (disch := (try omega)) only [rh _ _ hh, rp _ _ hp, Nat.sub_zero,
    Nat.reduceSub, h16,h18,h20,h24,h32,h40,h48,h52,h54,h56,h58,h60,h62,
    p0,p4,p8,p16,p24,p32,p40,p48, hmagic, Oak.NativeBitwiseObject.fromUInt8_length,
    hbnd, Oak.NativeBitwiseImage.base, Oak.NativeBitwiseImage.textOffset,
    and_self]


theorem sections_slices (m : Machine) (name : Bytes) :
    slice (sections m name) 0 64 = sectionBytes Oak.NativeBitwiseImage.nullSection ∧
    slice (sections m name) 64 64 = sectionBytes (Oak.NativeBitwiseImage.textSection m) ∧
    slice (sections m name) 128 64 = sectionBytes (Oak.NativeBitwiseImage.dataSection m) ∧
    slice (sections m name) 192 64 = sectionBytes (Oak.NativeBitwiseImage.symSection m) ∧
    slice (sections m name) 256 64 = sectionBytes (Oak.NativeBitwiseImage.strSection m (fromUInt8 name)) ∧
    slice (sections m name) 320 64 = sectionBytes (Oak.NativeBitwiseImage.shstrSection m (fromUInt8 name)) := by
  simp (disch := (try (first | omega | (simp only [sectionBytes_length,
    List.length_append] <;> omega)))) [sections, slice_append_left, slice_append_right, slice_all]

theorem E_sections (m : Machine) (name body : Bytes)
    (hn : name.length ≤ 256) (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    Oak.NativeBitwiseImage.Sections m (fromUInt8 name) (fromUInt8 (E m name body)) := by
  have hh := (E_header_program m name body hn hb).1
  obtain ⟨_,_,ht,he,hi,_⟩ := hh
  have hx := (E_slices m name body hb).2.2.2.2.2.2.2.2.2
  have hlen := E_length m name body hb
  have go : ∀ (s : Oak.NativeBitwiseObject.Section) (index : Nat), index < 6 →
      slice (sections m name) (index*64) 64 = sectionBytes s →
      (∀ v ∈ [s.name,s.kind,s.flags,s.address,s.offset,s.size,s.link,s.info,s.alignment,s.entrySize], v < 2^32) →
      Oak.NativeBitwiseObject.readSection (fromUInt8 (E m name body)) index = some s := by
    intro s index hib hsec hv
    apply readSection_of_slice _ s (Oak.NativeBitwiseImage.shOffset m (fromUInt8 name)) index ht he
    · simpa only [hi] using hib
    · omega
    · rw [← slice_slice _ _ 384 (index*64) 64 (by omega), hx, hsec]
    · exact hv
  obtain ⟨s0,s1,s2,s3,s4,s5⟩ := sections_slices m name
  unfold Oak.NativeBitwiseImage.Sections
  refine ⟨go _ 0 (by decide) s0 ?_,go _ 1 (by decide) s1 ?_,
    go _ 2 (by decide) s2 ?_,go _ 3 (by decide) s3 ?_,
    go _ 4 (by decide) s4 ?_,go _ 5 (by decide) s5 ?_⟩
  all_goals
    cases m <;> simp_all [Oak.NativeBitwiseImage.nullSection, Oak.NativeBitwiseImage.textSection,
      Oak.NativeBitwiseImage.dataSection, Oak.NativeBitwiseImage.symSection,
      Oak.NativeBitwiseImage.strSection, Oak.NativeBitwiseImage.shstrSection,
      Oak.NativeBitwiseImage.base, Oak.NativeBitwiseImage.textOffset,
      Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize,
      Oak.NativeBitwiseImage.bodySize, Oak.NativeBitwiseImage.loadSize,
      Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.strOffset,
      Oak.NativeBitwiseImage.shstrOffset] <;> omega


theorem symbol_fields (m : Machine) (s : Oak.NativeBitwiseObject.Symbol)
    (hs : s ∈ [Oak.NativeBitwiseImage.nullSymbol,Oak.NativeBitwiseImage.startSymbol m,
      Oak.NativeBitwiseImage.functionSymbol m]) :
    readLE (fromUInt8 (symbolBytes s)) 0 4 = s.name ∧
    readLE (fromUInt8 (symbolBytes s)) 4 1 = s.info ∧
    readLE (fromUInt8 (symbolBytes s)) 5 1 = s.other ∧
    readLE (fromUInt8 (symbolBytes s)) 6 2 = s.shndx ∧
    readLE (fromUInt8 (symbolBytes s)) 8 8 = s.value ∧
    readLE (fromUInt8 (symbolBytes s)) 16 8 = s.size := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> cases m <;>
    simp [symbolBytes, readLE_slice, slice, decode, dwordBytes, word32Bytes, wordBytes,
      Oak.NativeBitwiseImage.nullSymbol, Oak.NativeBitwiseImage.startSymbol,
      Oak.NativeBitwiseImage.functionSymbol, Oak.NativeBitwiseImage.base,
      Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize,
      Oak.NativeBitwiseImage.bodyAddress]

theorem symbols_slices (m : Machine) :
    slice (symbols m) 0 24 = symbolBytes Oak.NativeBitwiseImage.nullSymbol ∧
    slice (symbols m) 24 24 = symbolBytes (Oak.NativeBitwiseImage.startSymbol m) ∧
    slice (symbols m) 48 24 = symbolBytes (Oak.NativeBitwiseImage.functionSymbol m) := by
  simp (disch := (try (first | omega | (simp only [symbolBytes_length,
    List.length_append] <;> omega)))) [symbols, slice_append_left, slice_append_right, slice_all]

theorem E_symbol_records (m : Machine) (name body : Bytes)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    Oak.NativeBitwiseObject.readSymbol (fromUInt8 (E m name body)) (Oak.NativeBitwiseImage.symSection m) 0 =
      some Oak.NativeBitwiseImage.nullSymbol ∧
    Oak.NativeBitwiseObject.readSymbol (fromUInt8 (E m name body)) (Oak.NativeBitwiseImage.symSection m) 1 =
      some (Oak.NativeBitwiseImage.startSymbol m) ∧
    Oak.NativeBitwiseObject.readSymbol (fromUInt8 (E m name body)) (Oak.NativeBitwiseImage.symSection m) 2 =
      some (Oak.NativeBitwiseImage.functionSymbol m) := by
  have hx := (E_slices m name body hb).2.2.2.2.2.1
  have hlen := E_length m name body hb
  have hs := (shOffset_bounds m name).1
  have hend : Oak.NativeBitwiseImage.symOffset m + 72 ≤ (E m name body).length := by
    simp only [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset,
      Oak.NativeBitwiseObject.fromUInt8_length] at hs
    omega
  have go : ∀ (s : Oak.NativeBitwiseObject.Symbol) (index : Nat), index < 3 →
      slice (symbols m) (index*24) 24 = symbolBytes s →
      s ∈ [Oak.NativeBitwiseImage.nullSymbol,Oak.NativeBitwiseImage.startSymbol m,
        Oak.NativeBitwiseImage.functionSymbol m] →
      Oak.NativeBitwiseObject.readSymbol (fromUInt8 (E m name body)) (Oak.NativeBitwiseImage.symSection m) index = some s := by
    intro s index hib hsym hm
    have hx' : slice (E m name body) (Oak.NativeBitwiseImage.symOffset m + index*24) 24 = symbolBytes s := by
      rw [← slice_slice _ _ 72 (index*24) 24 (by omega), hx, hsym]
    have hr := readLE_in_slice (E m name body) (symbolBytes s)
      (Oak.NativeBitwiseImage.symOffset m + index*24) 24
    have h0 := hr 0 4 hx' (by omega)
    have h4 := hr 4 1 hx' (by omega)
    have h5 := hr 5 1 hx' (by omega)
    have h6 := hr 6 2 hx' (by omega)
    have h8 := hr 8 8 hx' (by omega)
    have h16 := hr 16 8 hx' (by omega)
    simp only [Nat.add_zero] at h0
    obtain ⟨f0,f4,f5,f6,f8,f16⟩ := symbol_fields m s hm
    have hib' : (index+1)*24 ≤ 72 := by omega
    simp only [Oak.NativeBitwiseObject.readSymbol, Oak.NativeBitwiseImage.symSection,
      Nat.reduceMod, Oak.NativeBitwiseObject.fromUInt8_length, hend, hib', and_self,
      ↓reduceIte,h0,h4,h5,h6,h8,h16,f0,f4,f5,f6,f8,f16]
  obtain ⟨s0,s1,s2⟩ := symbols_slices m
  exact ⟨go _ 0 (by decide) s0 (by simp),go _ 1 (by decide) s1 (by simp),
    go _ 2 (by decide) s2 (by simp)⟩


theorem terminatedName_zero (name rest : Oak.MinimalELF.Bytes)
    (hn : ∀ b ∈ name, b ≠ 0) :
    Oak.NativeBitwiseObject.terminatedName (name ++ 0 :: rest) = some name := by
  have ht : (name ++ 0 :: rest).takeWhile (fun b => b != 0) = name := by
    induction name with
    | nil => simp
    | cons b bs ih =>
      have hb := hn b (by simp)
      have hrs : ∀ c ∈ bs, c ≠ 0 := by intro c hc; exact hn c (by simp [hc])
      rw [List.cons_append, List.takeWhile_cons_of_pos (p := fun x : BitVec 8 => x != 0) (a := b) (bne_iff_ne.mpr hb), ih hrs]
  unfold Oak.NativeBitwiseObject.terminatedName
  rw [ht]
  simp

theorem E_symbol_names (m : Machine) (name body : Bytes)
    (hn : name.length ≤ 256) (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (hv : (fromUInt8 name).all (fun b => decide (0 < b.toNat ∧ b.toNat < 128)) = true) :
    Oak.NativeBitwiseObject.symbolName (fromUInt8 (E m name body))
      (Oak.NativeBitwiseImage.symSection m) (Oak.NativeBitwiseImage.startSymbol m) =
      some Oak.NativeBitwiseImage.startName ∧
    Oak.NativeBitwiseObject.symbolName (fromUInt8 (E m name body))
      (Oak.NativeBitwiseImage.symSection m) (Oak.NativeBitwiseImage.functionSymbol m) =
      some (Oak.NativeBitwiseObject.oakPrefix ++ fromUInt8 name) ∧
    Oak.NativeBitwiseObject.symbolName (fromUInt8 (E m name body))
      (Oak.NativeBitwiseImage.symSection m) Oak.NativeBitwiseImage.nullSymbol = some [] := by
  have hs := E_sections m name body hn hb
  have hx := (E_slices m name body hb).2.2.2.2.2.2.1
  have hlen := E_length m name body hb
  have hbound := (shOffset_bounds m name).1
  have he : Oak.NativeBitwiseImage.strOffset m + (name.length + 13) ≤ (E m name body).length := by
    simp only [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseObject.fromUInt8_length] at hbound
    omega
  have hx0 : slice (E m name body) (Oak.NativeBitwiseImage.strOffset m) (name.length+13) = stringTable name := hx
  have hx1 : slice (E m name body) (Oak.NativeBitwiseImage.strOffset m+1) (name.length+12) =
      [95,115,116,97,114,116,0,111,97,107,95] ++ name ++ [0] := by
    rw [← slice_slice _ _ (name.length+13) 1 (name.length+12) (by omega), hx]
    simp [stringTable, slice, List.take_append, List.take_of_length_le (show name.length ≤ name.length+1 by omega)]
  have hx8 : slice (E m name body) (Oak.NativeBitwiseImage.strOffset m+8) (name.length+5) =
      [111,97,107,95] ++ name ++ [0] := by
    rw [← slice_slice _ _ (name.length+13) 8 (name.length+5) (by omega), hx]
    simp [stringTable, slice, List.take_append, List.take_of_length_le (show name.length ≤ name.length+1 by omega)]
  have hnonzero : ∀ b ∈ fromUInt8 name, b ≠ 0 := by
    intro b hmem
    have hh := (List.all_eq_true.mp hv) b hmem
    simp only [decide_eq_true_eq] at hh
    intro hz
    simpa [hz] using hh.1
  have htstart := terminatedName_zero Oak.NativeBitwiseImage.startName
    (Oak.NativeBitwiseObject.oakPrefix ++ fromUInt8 name ++ [0]) (by decide)
  have htfun := terminatedName_zero (Oak.NativeBitwiseObject.oakPrefix ++ fromUInt8 name) []
    (by simp only [List.mem_append]; intro b hmem; rcases hmem with hp | hn
        · simp [Oak.NativeBitwiseObject.oakPrefix] at hp; rcases hp with rfl | rfl | rfl | rfl <;> decide
        · exact hnonzero b hn)
  unfold Oak.NativeBitwiseObject.symbolName
  simp only [Oak.NativeBitwiseImage.symSection, hs.2.2.2.2.1, Bind.bind, Option.bind,
    Oak.NativeBitwiseImage.strSection, Oak.NativeBitwiseImage.startSymbol,
    Oak.NativeBitwiseImage.functionSymbol, Oak.NativeBitwiseImage.nullSymbol,
    Oak.NativeBitwiseObject.fromUInt8_length, he]
  simp only [show name.length+13-1 = name.length+12 by omega,
    show name.length+13-8 = name.length+5 by omega, Nat.sub_zero, Nat.add_zero]
  simp only [show 1 < name.length+13 by omega, show 8 < name.length+13 by omega,
    show 0 < name.length+13 by omega, and_self, ↓reduceIte,
    ← fromUInt8_slice, hx0,hx1,hx8]
  simpa [fromUInt8, stringTable, Oak.NativeBitwiseImage.startName,
    Oak.NativeBitwiseObject.oakPrefix, List.map_append, List.append_assoc] using And.intro htstart (And.intro htfun (show
      Oak.NativeBitwiseObject.terminatedName (fromUInt8 (stringTable name)) = some [] by rfl))


theorem E_layout (m : Machine) (name body : Bytes)
    (hp : 0 < name.length) (hn : name.length ≤ 256)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (hv : (fromUInt8 name).all (fun b => decide (0 < b.toNat ∧ b.toNat < 128)) = true) :
    Oak.NativeBitwiseImage.Layout m (fromUInt8 name) (fromUInt8 (E m name body)) := by
  obtain ⟨_,_,hgap,hstartup,hpad,_,hstr,hshstr,halign,_⟩ := E_slices m name body hb
  have hlen := E_length m name body hb
  have hsz := E_size_bound m name body hn hb
  have hs := (shOffset_bounds m name).1
  have hbnd : Oak.NativeBitwiseImage.textOffset + Oak.NativeBitwiseImage.loadSize m ≤ (E m name body).length := by
    simp only [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset,
      Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseObject.fromUInt8_length] at hs
    omega
  unfold Oak.NativeBitwiseImage.Layout
  simp only [Oak.NativeBitwiseObject.fromUInt8_length]
  refine ⟨hp,hv,hlen,by omega,hbnd,?_,?_,?_,?_,?_,?_,hn⟩
  · have hh := congrArg fromUInt8 hgap
    rw [fromUInt8_slice] at hh
    simpa [Oak.NativeBitwiseImage.textOffset, fromUInt8, -List.reduceReplicate] using hh
  · have hh := congrArg fromUInt8 hstartup
    rw [fromUInt8_slice, Oak.NativeBitwiseObject.from_toUInt8] at hh
    exact hh
  · have hh := congrArg fromUInt8 hpad
    rw [fromUInt8_slice] at hh
    simpa [Oak.NativeBitwiseImage.textOffset, fromUInt8, -List.reduceReplicate] using hh
  · have hh := congrArg fromUInt8 hstr
    rw [fromUInt8_slice] at hh
    simpa [stringTable, fromUInt8, Oak.NativeBitwiseImage.startName, Oak.NativeBitwiseObject.oakPrefix,
      List.append_assoc] using hh
  · have hh := congrArg fromUInt8 hshstr
    rw [fromUInt8_slice, Oak.NativeBitwiseObject.from_toUInt8] at hh
    exact hh
  · have hh := congrArg fromUInt8 halign
    rw [fromUInt8_slice] at hh
    simpa [fromUInt8, -List.reduceReplicate] using hh

/-- Every byte in the independent envelope satisfies the complete strict image profile. -/
theorem E_strictProfile (m : Machine) (name body : Bytes)
    (hp : 0 < name.length) (hn : name.length ≤ 256)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (hv : (fromUInt8 name).all (fun b => decide (0 < b.toNat ∧ b.toNat < 128)) = true) :
    Oak.NativeBitwiseImage.StrictProfile m (fromUInt8 name) (fromUInt8 (E m name body)) := by
  obtain ⟨hh,hpgr⟩ := E_header_program m name body hn hb
  obtain ⟨s0,s1,s2⟩ := E_symbol_records m name body hb
  obtain ⟨ns,nf,nn⟩ := E_symbol_names m name body hn hb hv
  exact ⟨hh,hpgr,E_sections m name body hn hb,⟨s0,s1,s2,ns,nf,nn⟩,
    E_layout m name body hp hn hb hv⟩

/-- Acceptance is universal over the name bytes and every body of the fixed extent. -/
theorem E_accepts (m : Machine) (name body : Bytes)
    (hp : 0 < name.length) (hn : name.length ≤ 256)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (hv : (fromUInt8 name).all (fun b => decide (0 < b.toNat ∧ b.toNat < 128)) = true) :
    Oak.NativeBitwiseImage.accepts m (fromUInt8 name) (fromUInt8 (E m name body))
      (fromUInt8 body) = true := by
  have profile := E_strictProfile m name body hp hn hb hv
  have hbody := congrArg fromUInt8 (E_body_slice m name body hb)
  rw [fromUInt8_slice] at hbody
  simp only [Oak.NativeBitwiseImage.accepts, Oak.NativeBitwiseImage.extract, profile,
    ↓reduceIte, Oak.NativeBitwiseImage.profile_decodes profile,
    Oak.NativeBitwiseImage.candidate, hbody, decide_true]

/-- The writer's native byte inequalities imply the recognizer's ASCII predicate. -/
theorem valid_name_bridge (name : Bytes) (hv : ∀ b ∈ name, 0 < b ∧ b < 128) :
    (fromUInt8 name).all (fun b => decide (0 < b.toNat ∧ b.toNat < 128)) = true := by
  simp only [fromUInt8, List.all_map, Function.comp_def, List.all_eq_true]
  intro b hmem
  have hh := hv b hmem
  simpa [UInt8.lt_iff_toNat_lt, UInt8.toNat_toBitVec] using hh

end Oak.NativeBitwiseEnvelope
