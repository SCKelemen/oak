import Oak.NativeBitwiseImage

/-!
# Independent complete native ELF envelope specification

The specification is a concatenation of ELF fields and payloads, not a memory
update program. All arithmetic is over naturals. The only variable bytes are
the explicitly supplied profile-name proposal and fixed-extent function-body bytes.
Profile names may include bytes that are not valid source identifiers; source
parsing and source/body binding remain separate obligations.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine)
abbrev Bytes := List UInt8

def wordBytes (n : Nat) : Nat → Bytes
  | 0 => []
  | k+1 => UInt8.ofNat (n % 256) :: wordBytes (n / 256) k

def word32Bytes (n : Nat) : Bytes := wordBytes n 4
/-- ELF64 values in this bounded profile have a zero high 32-bit half. -/
def dwordBytes (n : Nat) : Bytes := word32Bytes n ++ word32Bytes 0

def header (m : Machine) (name : Bytes) : Bytes :=
  word32Bytes 0x464c457f ++ word32Bytes 0x00010102 ++ List.replicate 8 0 ++
  word32Bytes (2 + 65536 * m.number) ++ word32Bytes 1 ++
  dwordBytes Oak.NativeBitwiseImage.base ++ dwordBytes 64 ++
  dwordBytes (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name)) ++
  word32Bytes m.abiFlags ++ word32Bytes 0x00380040 ++
  word32Bytes 0x00400001 ++ word32Bytes 0x00050006

def programBytes (m : Machine) : Bytes :=
  word32Bytes 1 ++ word32Bytes 5 ++ dwordBytes Oak.NativeBitwiseImage.textOffset ++
  dwordBytes Oak.NativeBitwiseImage.base ++ dwordBytes Oak.NativeBitwiseImage.base ++
  dwordBytes (Oak.NativeBitwiseImage.loadSize m) ++ dwordBytes (Oak.NativeBitwiseImage.loadSize m) ++ dwordBytes 4096

def symbolBytes (s : Oak.NativeBitwiseObject.Symbol) : Bytes :=
  word32Bytes s.name ++ word32Bytes (s.info + 256 * s.other + 65536 * s.shndx) ++
  dwordBytes s.value ++ dwordBytes s.size

def symbols (m : Machine) : Bytes :=
  symbolBytes Oak.NativeBitwiseImage.nullSymbol ++ symbolBytes (Oak.NativeBitwiseImage.startSymbol m) ++
  symbolBytes (Oak.NativeBitwiseImage.functionSymbol m)

def stringTable (name : Bytes) : Bytes :=
  [0,95,115,116,97,114,116,0,111,97,107,95] ++ name ++ [0]

def sectionBytes (s : Oak.NativeBitwiseObject.Section) : Bytes :=
  word32Bytes s.name ++ word32Bytes s.kind ++ dwordBytes s.flags ++
  dwordBytes s.address ++ dwordBytes s.offset ++ dwordBytes s.size ++
  word32Bytes s.link ++ word32Bytes s.info ++ dwordBytes s.alignment ++
  dwordBytes s.entrySize

def sections (m : Machine) (name : Bytes) : Bytes :=
  sectionBytes Oak.NativeBitwiseImage.nullSection ++ sectionBytes (Oak.NativeBitwiseImage.textSection m) ++
  sectionBytes (Oak.NativeBitwiseImage.dataSection m) ++ sectionBytes (Oak.NativeBitwiseImage.symSection m) ++
  sectionBytes (Oak.NativeBitwiseImage.strSection m (Oak.NativeBitwiseObject.fromUInt8 name)) ++
  sectionBytes (Oak.NativeBitwiseImage.shstrSection m (Oak.NativeBitwiseObject.fromUInt8 name))

/-- The entire strict one-function ELF64 executable, independently serialized. -/
def E (m : Machine) (name body : Bytes) : Bytes :=
  header m name ++ programBytes m ++ List.replicate (Oak.NativeBitwiseImage.textOffset - 120) 0 ++
  Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++ body ++
  List.replicate (Oak.NativeBitwiseImage.loadSize m - Oak.NativeBitwiseImage.textSize m) 0 ++ symbols m ++
  stringTable name ++ Oak.NativeBitwiseObject.toUInt8 Oak.NativeBitwiseImage.sectionNames ++
  List.replicate (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) -
    (Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name) + 41)) 0 ++ sections m name

@[simp] theorem wordBytes_length (n width : Nat) : (wordBytes n width).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ k ih => simp [wordBytes, ih]
@[simp] theorem word32Bytes_length (n : Nat) : (word32Bytes n).length = 4 := wordBytes_length n 4
@[simp] theorem dwordBytes_length (n : Nat) : (dwordBytes n).length = 8 := by simp [dwordBytes]
@[simp] theorem header_length (m : Machine) (name : Bytes) : (header m name).length = 64 := by simp [header]
@[simp] theorem programBytes_length (m : Machine) : (programBytes m).length = 56 := by simp [programBytes]
@[simp] theorem symbolBytes_length (s : Oak.NativeBitwiseObject.Symbol) : (symbolBytes s).length = 24 := by simp [symbolBytes]
@[simp] theorem symbols_length (m : Machine) : (symbols m).length = 72 := by simp [symbols]
@[simp] theorem stringTable_length (name : Bytes) : (stringTable name).length = name.length + 13 := by simp [stringTable]
@[simp] theorem sectionBytes_length (s : Oak.NativeBitwiseObject.Section) : (sectionBytes s).length = 64 := by simp [sectionBytes]
@[simp] theorem sections_length (m : Machine) (name : Bytes) : (sections m name).length = 384 := by simp [sections]

@[simp] theorem startup_length (m : Machine) : (Oak.NativeBitwiseImage.startup m).length = Oak.NativeBitwiseImage.stubSize m := by cases m <;> rfl
@[simp] theorem sectionNames_length : Oak.NativeBitwiseImage.sectionNames.length = 41 := rfl

theorem align8_bounds (n : Nat) : n ≤ Oak.NativeBitwiseObject.align8 n ∧ Oak.NativeBitwiseObject.align8 n < n + 8 := by
  unfold Oak.NativeBitwiseObject.align8
  omega

theorem shOffset_bounds (m : Machine) (name : Bytes) :
    Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name) + 41 ≤ Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) ∧
    Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) < Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name) + 49 := by
  exact align8_bounds _

theorem E_length (m : Machine) (name body : Bytes) (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    (E m name body).length = Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) + 384 := by
  have hs := (shOffset_bounds m name).1
  simp only [E, List.length_append, header_length, programBytes_length, List.length_replicate,
    Oak.NativeBitwiseObject.toUInt8_length, startup_length, hb, symbols_length, stringTable_length,
    sectionNames_length, sections_length]
  cases m <;> simp_all [Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize, Oak.NativeBitwiseImage.loadSize,
    Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset, Oak.NativeBitwiseImage.symOffset] <;> omega

theorem E_size_bound (m : Machine) (name body : Bytes)
    (hn : name.length ≤ 256) (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    (E m name body).length ≤ 4928 := by
  rw [E_length m name body hb]
  have hs := (shOffset_bounds m name).2
  cases m <;> simp_all [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset, Oak.NativeBitwiseImage.symOffset,
    Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseImage.shOffset, Oak.NativeBitwiseObject.align8] <;> omega


def slice (bs : Bytes) (off count : Nat) : Bytes := (bs.drop off).take count

@[simp] theorem slice_empty (off count : Nat) : slice [] off count = [] := by simp [slice]
@[simp] theorem slice_zero (bs : Bytes) (off : Nat) : slice bs off 0 = [] := by simp [slice]
@[simp] theorem slice_self (bs : Bytes) : slice bs 0 bs.length = bs := by simp [slice]
theorem slice_all (bs : Bytes) (count : Nat) (h : bs.length ≤ count) : slice bs 0 count = bs := by
  simp [slice, List.take_of_length_le h]
theorem slice_append_left (a b : Bytes) (off count : Nat) (h : off + count ≤ a.length) :
    slice (a ++ b) off count = slice a off count := by
  simp only [slice, List.drop_append, List.take_append, List.length_drop]
  have : count - (a.length - off) = 0 := by omega
  simp [this]
theorem slice_append_right (a b : Bytes) (off count : Nat) (h : a.length ≤ off) :
    slice (a ++ b) off count = slice b (off - a.length) count := by
  simp [slice, List.drop_append, List.drop_eq_nil_of_le h]
@[simp] theorem slice_replicate (n off count : Nat) (x : UInt8) :
    slice (List.replicate n x) off count = List.replicate (min count (n-off)) x := by
  simp [slice, List.drop_replicate, List.take_replicate]
@[simp] theorem fromUInt8_slice (bs : Bytes) (off count : Nat) :
    Oak.NativeBitwiseObject.fromUInt8 (slice bs off count) =
    Oak.MinimalELF.slice (Oak.NativeBitwiseObject.fromUInt8 bs) off count := by
  simp [slice, Oak.NativeBitwiseObject.fromUInt8, Oak.MinimalELF.slice, List.map_drop, List.map_take]

theorem E_body_slice (m : Machine) (name body : Bytes)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    slice (E m name body) (Oak.NativeBitwiseImage.bodyOffset m)
      (Oak.NativeBitwiseImage.bodySize m) = body := by
  cases m <;> simp only [Oak.NativeBitwiseImage.bodySize] at hb <;>
    simp (disch := (try (first | omega | (simp only [header_length, programBytes_length, List.length_replicate, Oak.NativeBitwiseObject.toUInt8_length, startup_length, Oak.NativeBitwiseImage.stubSize] <;> omega)))) [E, Oak.NativeBitwiseImage.bodyOffset,
      Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.stubSize,
      Oak.NativeBitwiseImage.bodySize, slice_append_left, slice_append_right, slice_all,
      -List.reduceReplicate]


theorem E_slices (m : Machine) (name body : Bytes)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    slice (E m name body) 0 64 = header m name ∧
    slice (E m name body) 64 56 = programBytes m ∧
    slice (E m name body) 120 3976 = List.replicate 3976 0 ∧
    slice (E m name body) 4096 (Oak.NativeBitwiseImage.stubSize m) =
      Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ∧
    slice (E m name body) (4096 + Oak.NativeBitwiseImage.textSize m)
      (Oak.NativeBitwiseImage.loadSize m - Oak.NativeBitwiseImage.textSize m) =
      List.replicate (Oak.NativeBitwiseImage.loadSize m - Oak.NativeBitwiseImage.textSize m) 0 ∧
    slice (E m name body) (Oak.NativeBitwiseImage.symOffset m) 72 = symbols m ∧
    slice (E m name body) (Oak.NativeBitwiseImage.strOffset m) (name.length+13) = stringTable name ∧
    slice (E m name body) (Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name)) 41 =
      Oak.NativeBitwiseObject.toUInt8 Oak.NativeBitwiseImage.sectionNames ∧
    slice (E m name body) (Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name)+41)
      (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) -
       (Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name)+41)) =
      List.replicate (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) -
       (Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name)+41)) 0 ∧
    slice (E m name body) (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name)) 384 =
      sections m name := by
  have hs := (shOffset_bounds m name).1
  cases m <;> simp only [Oak.NativeBitwiseImage.bodySize] at hb <;>
    simp (disch := (try (first | omega | (simp only [List.length_append,
      header_length, programBytes_length, List.length_replicate,
      Oak.NativeBitwiseObject.toUInt8_length, startup_length, sectionNames_length,
      symbols_length, stringTable_length, sections_length, Oak.NativeBitwiseObject.fromUInt8_length,
      Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.bodySize,
      Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseImage.shstrOffset,
      Oak.NativeBitwiseImage.strOffset, Oak.NativeBitwiseImage.symOffset,
      Oak.NativeBitwiseImage.textOffset] at * <;> omega))))
      [E, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.textOffset,
       Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.bodySize, Oak.NativeBitwiseImage.loadSize,
       Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.strOffset,
       Oak.NativeBitwiseImage.shstrOffset, slice_append_left, slice_append_right, slice_all,
       -List.reduceReplicate]


/-- The alignment calculation yields the sharper architecture-specific bound. -/
theorem E_arm64_size_bound (name body : Bytes)
    (hn : name.length ≤ 256) (hb : body.length = Oak.NativeBitwiseImage.bodySize .arm64) :
    (E .arm64 name body).length ≤ 4896 := by
  rw [E_length .arm64 name body hb]
  have hs := (shOffset_bounds .arm64 name).2
  simp only [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset,
    Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.textOffset,
    Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseObject.fromUInt8_length] at hs
  unfold Oak.NativeBitwiseImage.shOffset Oak.NativeBitwiseObject.align8
  simp only [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset,
    Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.textOffset,
    Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseObject.fromUInt8_length]
  omega

theorem E_rv64_size_bound (name body : Bytes)
    (hn : name.length ≤ 256) (hb : body.length = Oak.NativeBitwiseImage.bodySize .rv64) :
    (E .rv64 name body).length ≤ 4928 := E_size_bound .rv64 name body hn hb

/-- Four-byte chunks covering exactly the fixed target startup prefix. -/
def startupReadOffsets : Machine → List Nat
  | .arm64 => [0,4,8]
  | .rv64 => [0,4,8,12]

/-- Every startup comparison has its entire four-byte read inside the prefix. -/
theorem startup_read_footprint (m : Machine) (offset : Nat)
    (ho : offset ∈ startupReadOffsets m) :
    offset + 4 ≤ Oak.NativeBitwiseImage.stubSize m ∧
    ∀ k < 4, offset + k < Oak.NativeBitwiseImage.stubSize m ∧ offset + k < 2^32 := by
  cases m <;> simp only [startupReadOffsets, List.mem_cons, List.not_mem_nil, or_false] at ho <;>
    simp only [Oak.NativeBitwiseImage.stubSize]
  all_goals constructor <;> (try intro k hk) <;> omega

/-- The source's u32 index additions are exact, and each defaulting read is in bounds. -/
theorem startup_read_index (m : Machine) (offset k : Nat)
    (ho : offset ∈ startupReadOffsets m) (hk : k < 4) :
    (UInt32.ofNat offset + UInt32.ofNat k).toNat = offset+k ∧
    offset+k < (Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m)).length := by
  obtain ⟨hfoot,hindices⟩ := startup_read_footprint m offset ho
  have hi := hindices k hk
  have ho32 : offset < 2^32 := by omega
  have hk32 : k < 2^32 := by omega
  constructor
  · rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt ho32, Nat.mod_eq_of_lt hk32]
    exact Nat.mod_eq_of_lt hi.2
  · simpa only [Oak.NativeBitwiseObject.toUInt8_length, startup_length] using hi.1

/-- Every byte-packing shift is below the source u32 word width. -/
theorem startup_read_shift_counts : ∀ shift ∈ [0,8,16,24], shift < 32 := by
  simp

end Oak.NativeBitwiseEnvelope
