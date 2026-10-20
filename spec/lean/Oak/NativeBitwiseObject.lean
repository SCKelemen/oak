import Oak.MinimalELF
import Oak.AArch64BitwiseFunction
import Oak.RiscVFramedBitwise

/-!
# Strict production-shaped ELF64 relocatable bitwise objects

This recognizer consumes the complete object, follows the header's section-table
pointer and the symbol table's string-table link, and binds exactly one named
GLOBAL/FUNC symbol to the whole text section. The canonical profile is the
one-function, no-data, no-relocation shape of `asm/object.go:writeELF`.

The flat section loader below is an explicit model. No OS loader, system linker,
executable entry, fetched ISA execution, arbitrary compiler correctness, or
production verification authority is asserted. ET_REL's zero e_entry is not the
function entry. A source name here is an explicit byte argument; original-source
parsing and source semantics are separate obligations.
-/
set_option autoImplicit false
namespace Oak.NativeBitwiseObject
open Oak.MinimalELF (Bytes Machine slice readLE)

/-- Exact, elementwise bridge to the source/ARM byte representation. -/
def fromUInt8 (bytes : List UInt8) : Bytes := bytes.map UInt8.toBitVec
def toUInt8 (bytes : Bytes) : List UInt8 := bytes.map UInt8.ofBitVec

@[simp] theorem fromUInt8_length (bytes : List UInt8) :
    (fromUInt8 bytes).length = bytes.length := by simp [fromUInt8]
@[simp] theorem toUInt8_length (bytes : Bytes) :
    (toUInt8 bytes).length = bytes.length := by simp [toUInt8]
@[simp] theorem to_fromUInt8 (bytes : List UInt8) :
    toUInt8 (fromUInt8 bytes) = bytes := by simp [toUInt8, fromUInt8, List.map_map, Function.comp_def]
@[simp] theorem from_toUInt8 (bytes : Bytes) :
    fromUInt8 (toUInt8 bytes) = bytes := by simp [toUInt8, fromUInt8, List.map_map, Function.comp_def]
theorem fromUInt8_injective {a b : List UInt8} (h : fromUInt8 a = fromUInt8 b) : a = b := by
  have := congrArg toUInt8 h
  simpa using this

structure Section where
  name : Nat
  kind : Nat
  flags : Nat
  address : Nat
  offset : Nat
  size : Nat
  link : Nat
  info : Nat
  alignment : Nat
  entrySize : Nat
  deriving DecidableEq, Repr

structure Symbol where
  name : Nat
  info : Nat
  other : Nat
  shndx : Nat
  value : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- Bounded section decoder. No missing bytes are treated as zero. -/
def readSection (image : Bytes) (index : Nat) : Option Section :=
  let table := readLE image 40 8
  let pos := table + index * 64
  if 64 ≤ image.length ∧ readLE image 58 2 = 64 ∧
      index < readLE image 60 2 ∧ pos + 64 ≤ image.length then
    some ⟨readLE image pos 4, readLE image (pos+4) 4,
      readLE image (pos+8) 8, readLE image (pos+16) 8,
      readLE image (pos+24) 8, readLE image (pos+32) 8,
      readLE image (pos+40) 4, readLE image (pos+44) 4,
      readLE image (pos+48) 8, readLE image (pos+56) 8⟩
  else none

/-- Bounded ELF64 symbol decoder for the supplied decoded symbol-table section. -/
def readSymbol (image : Bytes) (table : Section) (index : Nat) : Option Symbol :=
  let pos := table.offset + index * 24
  if table.kind = 2 ∧ table.entrySize = 24 ∧ table.size % 24 = 0 ∧
      (index+1) * 24 ≤ table.size ∧ table.offset + table.size ≤ image.length then
    some ⟨readLE image pos 4, readLE image (pos+4) 1, readLE image (pos+5) 1,
      readLE image (pos+6) 2, readLE image (pos+8) 8, readLE image (pos+16) 8⟩
  else none

/-- Require an actual terminating NUL within the linked string table. -/
def terminatedName (bytes : Bytes) : Option Bytes :=
  let name := bytes.takeWhile (fun b => b != 0)
  if name.length < bytes.length then some name else none

def symbolName (image : Bytes) (table : Section) (symbol : Symbol) : Option Bytes := do
  let strings ← readSection image table.link
  if strings.kind = 3 ∧ strings.offset + strings.size ≤ image.length ∧
      symbol.name < strings.size then
    terminatedName (slice image (strings.offset + symbol.name) (strings.size - symbol.name))
  else none

def oakPrefix : Bytes := [111, 97, 107, 95]
def sectionNames : Bytes :=
  [0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,
   46,114,101,108,97,46,116,101,120,116,0,
   46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,
   46,115,104,115,116,114,116,97,98,0]
def bodySize : Machine → Nat | .arm64 => 8 | .rv64 => 36
def align8 (n : Nat) : Nat := ((n + 7) / 8) * 8
def dataOffset (machine : Machine) : Nat := align8 (64 + bodySize machine)
def strOffset (machine : Machine) : Nat := dataOffset machine + 96
def shstrOffset (machine : Machine) (name : Bytes) : Nat := strOffset machine + name.length + 6
def shOffset (machine : Machine) (name : Bytes) : Nat := align8 (shstrOffset machine name + 52)

def nullSection : Section := ⟨0,0,0,0,0,0,0,0,0,0⟩
def textSection (machine : Machine) : Section := ⟨1,1,6,0,64,bodySize machine,0,0,4,0⟩
def dataSection (machine : Machine) : Section := ⟨7,1,2,0,dataOffset machine,0,0,0,1,0⟩
def relaSection (machine : Machine) : Section := ⟨15,4,64,0,dataOffset machine,0,4,1,8,24⟩
def symSection (machine : Machine) : Section := ⟨26,2,0,0,dataOffset machine,96,5,3,8,24⟩
def strSection (machine : Machine) (name : Bytes) : Section :=
  ⟨34,3,0,0,strOffset machine,name.length+6,0,0,1,0⟩
def shstrSection (machine : Machine) (name : Bytes) : Section :=
  ⟨42,3,0,0,shstrOffset machine name,52,0,0,1,0⟩
def nullSymbol : Symbol := ⟨0,0,0,0,0,0⟩
def textSymbol : Symbol := ⟨0,3,0,1,0,0⟩
def dataSymbol : Symbol := ⟨0,3,0,2,0,0⟩
def functionSymbol (machine : Machine) : Symbol := ⟨1,18,0,1,0,bodySize machine⟩

/-- This is an ET_REL header, deliberately separate from MinimalELF.Header. -/
def Header (machine : Machine) (name image : Bytes) : Prop :=
  64 ≤ image.length ∧
  slice image 0 16 = [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0] ∧
  readLE image 16 2 = 1 ∧ readLE image 18 2 = machine.number ∧
  readLE image 20 4 = 1 ∧ readLE image 24 8 = 0 ∧ readLE image 32 8 = 0 ∧
  readLE image 40 8 = shOffset machine name ∧
  readLE image 48 4 = machine.abiFlags ∧ readLE image 52 2 = 64 ∧
  readLE image 54 2 = 0 ∧ readLE image 56 2 = 0 ∧
  readLE image 58 2 = 64 ∧ readLE image 60 2 = 7 ∧ readLE image 62 2 = 6
instance (m : Machine) (n b : Bytes) : Decidable (Header m n b) := inferInstanceAs (Decidable (_ ∧ _))

def Sections (machine : Machine) (name image : Bytes) : Prop :=
  readSection image 0 = some nullSection ∧
  readSection image 1 = some (textSection machine) ∧
  readSection image 2 = some (dataSection machine) ∧
  readSection image 3 = some (relaSection machine) ∧
  readSection image 4 = some (symSection machine) ∧
  readSection image 5 = some (strSection machine name) ∧
  readSection image 6 = some (shstrSection machine name)
instance (m : Machine) (n b : Bytes) : Decidable (Sections m n b) := inferInstanceAs (Decidable (_ ∧ _))

def Symbols (machine : Machine) (name image : Bytes) : Prop :=
  readSymbol image (symSection machine) 0 = some nullSymbol ∧
  readSymbol image (symSection machine) 1 = some textSymbol ∧
  readSymbol image (symSection machine) 2 = some dataSymbol ∧
  readSymbol image (symSection machine) 3 = some (functionSymbol machine) ∧
  symbolName image (symSection machine) (functionSymbol machine) = some (oakPrefix ++ name)
instance (m : Machine) (n b : Bytes) : Decidable (Symbols m n b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Exact payloads/padding and exhaustion exclude hidden extra data or code.
Offsets are naturals; the checked full-file bound excludes u64 wrapping. -/
def Layout (machine : Machine) (name image : Bytes) : Prop :=
  0 < name.length ∧ name.all (fun b => decide (0 < b.toNat ∧ b.toNat < 128)) = true ∧
  image.length = shOffset machine name + 448 ∧ image.length < 2^64 ∧
  64 + bodySize machine ≤ image.length ∧
  slice image (64 + bodySize machine) (dataOffset machine - (64 + bodySize machine)) =
    List.replicate (dataOffset machine - (64 + bodySize machine)) 0 ∧
  slice image (strOffset machine) (name.length+6) = [0] ++ oakPrefix ++ name ++ [0] ∧
  slice image (shstrOffset machine name) 52 = sectionNames ∧
  slice image (shstrOffset machine name + 52) (shOffset machine name - (shstrOffset machine name + 52)) =
    List.replicate (shOffset machine name - (shstrOffset machine name + 52)) 0
instance (m : Machine) (n b : Bytes) : Decidable (Layout m n b) := inferInstanceAs (Decidable (_ ∧ _))

def StrictProfile (machine : Machine) (name image : Bytes) : Prop :=
  Header machine name image ∧ Sections machine name image ∧
  Symbols machine name image ∧ Layout machine name image
instance (m : Machine) (n b : Bytes) : Decidable (StrictProfile m n b) := inferInstanceAs (Decidable (_ ∧ _))

structure Loaded where
  body : Bytes
  symbolIndex : Nat
  sectionIndex : Nat
  entry : Nat
  fileOffset : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- A declarative relation through actual decoded records, independent of extract.
The complete section is the function extent. The entry is section-relative. -/
def NamedFunction (image name : Bytes) (loaded : Loaded) : Prop :=
  ∃ table symbol sec,
    readSection image 4 = some table ∧
    readSymbol image table loaded.symbolIndex = some symbol ∧
    symbolName image table symbol = some name ∧
    readSection image symbol.shndx = some sec ∧
    symbol.info = 18 ∧ symbol.other = 0 ∧
    loaded.sectionIndex = symbol.shndx ∧ loaded.entry = symbol.value ∧
    symbol.value = 0 ∧ symbol.size = sec.size ∧
    sec.kind = 1 ∧ sec.flags = 6 ∧ sec.alignment = 4 ∧
    loaded.fileOffset = sec.offset ∧ loaded.size = symbol.size ∧
    loaded.body = slice image loaded.fileOffset loaded.size ∧
    loaded.fileOffset + loaded.size ≤ image.length

/-- Uniqueness ranges over every decoded symbol, not a trusted external index. -/
def UniqueFunction (image : Bytes) (table : Section) (index : Nat) : Prop :=
  ∀ i symbol, readSymbol image table i = some symbol → symbol.info = 18 → i = index

def candidate (machine : Machine) (image : Bytes) : Loaded :=
  ⟨slice image 64 (bodySize machine), 3, 1, 0, 64, bodySize machine⟩

/-- Only the complete checked image supplies the returned body. -/
def extract (machine : Machine) (name image : Bytes) : Option Loaded :=
  if StrictProfile machine name image then some (candidate machine image) else none

def accepts (machine : Machine) (name image expectedBody : Bytes) : Bool :=
  match extract machine name image with
  | some loaded => decide (loaded.body = expectedBody)
  | none => false

private theorem symbol_index_bound {image : Bytes} {table : Section} {i : Nat} {s : Symbol}
    (h : readSymbol image table i = some s) : (i+1)*24 ≤ table.size := by
  unfold readSymbol at h
  split at h
  · rename_i guard
    exact guard.2.2.2.1
  · simp at h

theorem profile_unique {m : Machine} {name image : Bytes}
    (h : Symbols m name image) : UniqueFunction image (symSection m) 3 := by
  intro i symbol hs hi
  have bound := symbol_index_bound hs
  change (i+1)*24 ≤ 96 at bound
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with ⟨h0,h1,h2,h3,_⟩
  rcases cases with h | h | h | h
  · subst i
    rw [h0] at hs
    cases hs
    change 0 = 18 at hi
    omega
  · subst i
    rw [h1] at hs
    cases hs
    change 3 = 18 at hi
    omega
  · subst i
    rw [h2] at hs
    cases hs
    change 3 = 18 at hi
    omega
  · exact h

theorem profile_named {m : Machine} {name image : Bytes}
    (h : StrictProfile m name image) : NamedFunction image (oakPrefix ++ name) (candidate m image) := by
  rcases h with ⟨_, hsections, hsymbols, hlayout⟩
  refine ⟨symSection m, functionSymbol m, textSection m, hsections.2.2.2.2.1,
    hsymbols.2.2.2.1, hsymbols.2.2.2.2, hsections.2.1, ?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hlayout.2.2.2.2.1⟩

theorem extract_sound {m : Machine} {name image : Bytes} {loaded : Loaded}
    (h : extract m name image = some loaded) :
    StrictProfile m name image ∧ NamedFunction image (oakPrefix ++ name) loaded ∧
    UniqueFunction image (symSection m) loaded.symbolIndex ∧
    loaded = candidate m image := by
  unfold extract at h
  split at h
  · rename_i profile
    cases h
    exact ⟨profile, profile_named profile, profile_unique profile.2.2.1, rfl⟩
  · simp at h

/-- The central container/name/whole-body binding theorem. No separately supplied
body, name, section index or entry is trusted without checking the full object. -/
theorem accepted_named_body {m : Machine} {name image expectedBody : Bytes}
    (h : accepts m name image expectedBody = true) :
    ∃ loaded, extract m name image = some loaded ∧
      StrictProfile m name image ∧ NamedFunction image (oakPrefix ++ name) loaded ∧
      UniqueFunction image (symSection m) loaded.symbolIndex ∧
      loaded.body = expectedBody ∧ loaded.entry = 0 ∧ loaded.sectionIndex = 1 ∧
      loaded.fileOffset = 64 ∧ loaded.size = bodySize m ∧
      expectedBody = slice image loaded.fileOffset loaded.size ∧
      loaded.fileOffset + loaded.size ≤ image.length ∧ expectedBody.length = loaded.size ∧
      0 < loaded.size := by
  unfold accepts at h
  split at h
  · rename_i loaded hextract
    have heq : loaded.body = expectedBody := by simpa using h
    obtain ⟨profile,named,unique,hloaded⟩ := extract_sound hextract
    refine ⟨loaded,hextract,profile,named,unique,heq,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals subst loaded
    · rfl
    · rfl
    · rfl
    · rfl
    · exact heq.symm
    · exact profile.2.2.2.2.2.2.2.1
    · rw [← heq]
      simp only [candidate, slice, List.length_take, List.length_drop]
      have hb := profile.2.2.2.2.2.2.2.1
      omega
    · cases m <;> exact Nat.zero_lt_succ _
  · simp at h

/-- The canonical nonempty payloads are ordered and disjoint. Empty data and
relocation sections deliberately share the symbol-table start, as the writer does. -/
theorem accepted_layout_bounds {m : Machine} {name image body : Bytes}
    (h : accepts m name image body = true) :
    64 + bodySize m ≤ dataOffset m ∧
    dataOffset m + 96 = strOffset m ∧
    strOffset m + (name.length + 6) = shstrOffset m name ∧
    shstrOffset m name + 52 ≤ shOffset m name ∧
    shOffset m name + 448 = image.length ∧ image.length < 2^64 := by
  obtain ⟨_,_,profile,_⟩ := accepted_named_body h
  have layout := profile.2.2.2
  refine ⟨?_,rfl,?_,?_,layout.2.2.1.symm,layout.2.2.2.1⟩
  · cases m <;> decide
  · simp [shstrOffset, Nat.add_assoc]
  · unfold shOffset align8
    omega

/-- Architecture, ABI and the empty relocation section come from the full object,
not from an external target label or a separately extracted body. -/
theorem accepted_architecture_no_relocations {m : Machine} {name image body : Bytes}
    (h : accepts m name image body = true) :
    readLE image 16 2 = 1 ∧ readLE image 18 2 = m.number ∧
    readLE image 48 4 = m.abiFlags ∧
    readSection image 3 = some (relaSection m) ∧ (relaSection m).size = 0 := by
  obtain ⟨_,_,profile,_⟩ := accepted_named_body h
  exact ⟨profile.1.2.2.1,profile.1.2.2.2.1,profile.1.2.2.2.2.2.2.2.2.1,
    profile.2.1.2.2.2.1,rfl⟩

/-- Relocatable-section loading model, with no wrapping or out-of-file reads. -/
def loadBytes (image : Bytes) (loaded : Loaded) (base address count : Nat) : Option Bytes :=
  if base % 4 = 0 ∧ base + loaded.size < 2^64 ∧
      loaded.fileOffset + loaded.size ≤ image.length ∧
      base ≤ address ∧ address + count ≤ base + loaded.size then
    some (slice image (loaded.fileOffset + (address - base)) count)
  else none

def resolvedEntry (loaded : Loaded) (base : Nat) : Nat := base + loaded.entry

theorem named_load {m : Machine} {name image body : Bytes}
    (h : accepts m name image body = true) (base : Nat)
    (aligned : base % 4 = 0) (bounded : base + bodySize m < 2^64) :
    ∃ loaded, extract m name image = some loaded ∧
      NamedFunction image (oakPrefix ++ name) loaded ∧ resolvedEntry loaded base = base ∧
      loadBytes image loaded base (resolvedEntry loaded base) loaded.size = some body := by
  obtain ⟨l,hex,_,hn,_,_,he,_,_,hs,hbody,hbounds,_,_⟩ := accepted_named_body h
  refine ⟨l,hex,hn,?_,?_⟩
  · simp [resolvedEntry, he]
  · have bound : base + l.size < 2^64 := by simpa [hs] using bounded
    simp only [loadBytes, resolvedEntry, he, Nat.add_zero, aligned, bound, hbounds,
      Nat.le_refl, and_self, if_true, Nat.sub_self, ← hbody]

/-- Every byte at the modeled named entry is the checked body byte. -/
theorem named_fetch_byte {m : Machine} {name image body : Bytes}
    (h : accepts m name image body = true) (base i : Nat)
    (aligned : base % 4 = 0) (bounded : base + bodySize m < 2^64)
    (hi : i < body.length) :
    ∃ loaded, extract m name image = some loaded ∧
      resolvedEntry loaded base = base ∧
      loadBytes image loaded base (base+i) 1 = some (slice body i 1) ∧
      image[loaded.fileOffset+i]? = body[i]? := by
  obtain ⟨l,hex,_,_,_,_,he,_,_,hs,hbody,hbounds,hlen,_⟩ := accepted_named_body h
  have hic : i < l.size := by omega
  have hbyte : image[l.fileOffset+i]? = body[i]? := by
    rw [hbody]
    simp [slice, hic, List.getElem?_drop]
  refine ⟨l,hex,by simp [resolvedEntry,he],?_,hbyte⟩
  have sliceEq : slice image (l.fileOffset+i) 1 = slice body i 1 := by
    rw [hbody]
    simp only [slice, List.drop_take, List.drop_drop]
    rw [List.take_take]
    congr 1
    omega
  have bound : base + l.size < 2^64 := by simpa [hs] using bounded
  have low : base ≤ base+i := by omega
  have high : base+i+1 ≤ base+l.size := by omega
  simp only [loadBytes, aligned, bound, hbounds, low, high, and_self, if_true,
    Nat.add_sub_cancel_left, sliceEq]

/-- ARM execution in the existing no-fault scalar projection, at the resolved
entry of the modeled section loader. High input halves remain unrestricted. -/
theorem accepted_arm_execution {name image : Bytes} (op : Oak.BitwiseFunction.Op)
    (h : accepts .arm64 name image (fromUInt8 (Oak.AArch64BitwiseFunction.functionBytes op)) = true)
    (base : Nat) (aligned : base % 4 = 0) (bounded : base + 8 < 2^64)
    (s : Oak.AArch64BitwiseFunction.State) :
    ∃ loaded, extract .arm64 name image = some loaded ∧
      NamedFunction image (oakPrefix ++ name) loaded ∧ resolvedEntry loaded base = base ∧
      (loadBytes image loaded base (resolvedEntry loaded base) loaded.size).bind
        (fun bytes => Oak.AArch64BitwiseFunction.invoke (toUInt8 bytes)
          { s with pc := BitVec.ofNat 64 base }) =
      some (Oak.AArch64BitwiseFunction.returned op { s with pc := BitVec.ofNat 64 base }) := by
  obtain ⟨l,hex,hn,he,hl⟩ := named_load h base aligned bounded
  refine ⟨l,hex,hn,he,?_⟩
  rw [hl]
  simp only [Option.bind_some, to_fromUInt8]
  exact Oak.AArch64BitwiseFunction.function_success op _

/-- RV uses the actual 36-byte wrapper. frameSafe is still an external mapping,
stack alignment and noninterference requirement of the existing flat model. -/
theorem accepted_rv_execution {name image : Bytes} (op : Oak.BitwiseFunction.Op)
    (h : accepts .rv64 name image (Oak.RiscVFramedBitwise.functionBytes op) = true)
    (base : Nat) (aligned : base % 4 = 0) (bounded : base + 36 < 2^64)
    (s : Oak.RiscVFramedBitwise.State) (mappedRW : Nat → Nat → Bool)
    (safe : Oak.RiscVFramedBitwise.frameSafe mappedRW s = true) :
    ∃ loaded, extract .rv64 name image = some loaded ∧
      NamedFunction image (oakPrefix ++ name) loaded ∧ resolvedEntry loaded base = base ∧
      (loadBytes image loaded base (resolvedEntry loaded base) loaded.size).bind
        (fun bytes => Oak.RiscVFramedBitwise.invoke mappedRW bytes
          { s with core := { s.core with pc := BitVec.ofNat 64 base } }) =
      some (Oak.RiscVFramedBitwise.finalState op
        { s with core := { s.core with pc := BitVec.ofNat 64 base } }) := by
  obtain ⟨l,hex,hn,he,hl⟩ := named_load h base aligned bounded
  refine ⟨l,hex,hn,he,?_⟩
  rw [hl]
  apply Oak.RiscVFramedBitwise.function_success
  exact safe

example : extract .arm64 [102] [] = none := by decide +kernel
example : extract .rv64 [102] [] = none := by decide +kernel

end Oak.NativeBitwiseObject
