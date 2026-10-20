import Oak.NativeBitwiseObject

/-!
# Complete, strict production ELF64 executable image binding

This is the one-function Linux/default-base profile of `asm.WriteExecutable`:
exactly `_start` and one `oak_<name>` GLOBAL/FUNC symbol, six sections, one RX
PT_LOAD, no data/relocations/extra bytes, and the exact linked startup bytes.
ARM64 uses e_flags=0 and an eight-byte body; RV64 uses LP64D e_flags=4 and the
36-byte framed body extent. The expected body is only a comparison proposal.
The extractor reads symbol/section records and returns the file's bytes and
virtual address. It does not trust an external entry, offset, extent or symbol.

Only the bounded byte/record/name readers are reused from NativeBitwiseObject;
none of its ET_REL profile, section-relative entry or loader assumptions apply.
The load theorem uses MinimalELF's explicit flat loader. No `_start` execution,
OS loader, ISA execution, source provenance, compiler correctness, broad ABI or
production verification authority is asserted.
-/
set_option autoImplicit false
set_option maxRecDepth 1024
namespace Oak.NativeBitwiseImage
open Oak.MinimalELF (Bytes Machine slice readLE)
open Oak.NativeBitwiseObject (Section Symbol readSection readSymbol symbolName oakPrefix fromUInt8)

def base : Nat := 65536
def textOffset : Nat := 4096
def stubSize : Machine → Nat | .arm64 => 12 | .rv64 => 16
def bodySize : Machine → Nat | .arm64 => 8 | .rv64 => 36
def textSize (m : Machine) : Nat := stubSize m + bodySize m
def loadSize : Machine → Nat | .arm64 => 32 | .rv64 => 64
def bodyOffset (m : Machine) : Nat := textOffset + stubSize m
def bodyAddress (m : Machine) : Nat := base + stubSize m
def symOffset (m : Machine) : Nat := textOffset + loadSize m
def strOffset (m : Machine) : Nat := symOffset m + 72
def shstrOffset (m : Machine) (name : Bytes) : Nat := strOffset m + name.length + 13
def shOffset (m : Machine) (name : Bytes) : Nat :=
  Oak.NativeBitwiseObject.align8 (shstrOffset m name + 41)

def startName : Bytes := [95,115,116,97,114,116]
def startup : Machine → Bytes
  | .arm64 => [3,0,0,148,168,11,128,82,1,0,0,212]
  | .rv64 => [151,0,0,0,231,128,0,1,147,8,208,5,115,0,0,0]
def sectionNames : Bytes :=
  [0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,
   46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,
   46,115,104,115,116,114,116,97,98,0]

def nullSection : Section := ⟨0,0,0,0,0,0,0,0,0,0⟩
def textSection (m : Machine) : Section := ⟨1,1,6,base,textOffset,textSize m,0,0,4,0⟩
def dataSection (m : Machine) : Section := ⟨7,1,2,base+loadSize m,symOffset m,0,0,0,16,0⟩
def symSection (m : Machine) : Section := ⟨15,2,0,0,symOffset m,72,4,1,8,24⟩
def strSection (m : Machine) (name : Bytes) : Section :=
  ⟨23,3,0,0,strOffset m,name.length+13,0,0,1,0⟩
def shstrSection (m : Machine) (name : Bytes) : Section :=
  ⟨31,3,0,0,shstrOffset m name,41,0,0,1,0⟩
def nullSymbol : Symbol := ⟨0,0,0,0,0,0⟩
def startSymbol (m : Machine) : Symbol := ⟨1,18,0,1,base,stubSize m⟩
def functionSymbol (m : Machine) : Symbol := ⟨8,18,0,1,bodyAddress m,bodySize m⟩
def program (m : Machine) : Oak.MinimalELF.Segment :=
  ⟨base,textOffset,base,loadSize m,loadSize m,5,4096⟩

/-- All ELF header bytes, including the ET_EXEC-only program-header profile. -/
def Header (m : Machine) (name image : Bytes) : Prop :=
  Oak.MinimalELF.Header m image ∧
  readLE image 24 8 = base ∧ readLE image 40 8 = shOffset m name ∧
  readLE image 58 2 = 64 ∧ readLE image 60 2 = 6 ∧ readLE image 62 2 = 5
instance (m : Machine) (n b : Bytes) : Decidable (Header m n b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every program-header field is fixed, including p_paddr absent from Segment. -/
def Program (m : Machine) (image : Bytes) : Prop :=
  Oak.MinimalELF.segment image = program m ∧ readLE image 88 8 = base
instance (m : Machine) (b : Bytes) : Decidable (Program m b) := inferInstanceAs (Decidable (_ ∧ _))

def Sections (m : Machine) (name image : Bytes) : Prop :=
  readSection image 0 = some nullSection ∧
  readSection image 1 = some (textSection m) ∧
  readSection image 2 = some (dataSection m) ∧
  readSection image 3 = some (symSection m) ∧
  readSection image 4 = some (strSection m name) ∧
  readSection image 5 = some (shstrSection m name)
instance (m : Machine) (n b : Bytes) : Decidable (Sections m n b) := inferInstanceAs (Decidable (_ ∧ _))

def Symbols (m : Machine) (name image : Bytes) : Prop :=
  readSymbol image (symSection m) 0 = some nullSymbol ∧
  readSymbol image (symSection m) 1 = some (startSymbol m) ∧
  readSymbol image (symSection m) 2 = some (functionSymbol m) ∧
  symbolName image (symSection m) (startSymbol m) = some startName ∧
  symbolName image (symSection m) (functionSymbol m) = some (oakPrefix ++ name) ∧
  symbolName image (symSection m) nullSymbol = some []
instance (m : Machine) (n b : Bytes) : Decidable (Symbols m n b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Exhaust every payload and padding byte; the function body alone is variable. -/
def Layout (m : Machine) (name image : Bytes) : Prop :=
  0 < name.length ∧ name.all (fun b => decide (0 < b.toNat ∧ b.toNat < 128)) = true ∧
  image.length = shOffset m name + 384 ∧ image.length ≤ 5120 ∧
  textOffset + loadSize m ≤ image.length ∧
  slice image 120 (textOffset-120) = List.replicate (textOffset-120) 0 ∧
  slice image textOffset (stubSize m) = startup m ∧
  slice image (textOffset + textSize m) (loadSize m - textSize m) =
    List.replicate (loadSize m - textSize m) 0 ∧
  slice image (strOffset m) (name.length+13) = [0] ++ startName ++ [0] ++ oakPrefix ++ name ++ [0] ∧
  slice image (shstrOffset m name) 41 = sectionNames ∧
  slice image (shstrOffset m name+41) (shOffset m name - (shstrOffset m name+41)) =
    List.replicate (shOffset m name - (shstrOffset m name+41)) 0 ∧ name.length ≤ 256
instance (m : Machine) (n b : Bytes) : Decidable (Layout m n b) := inferInstanceAs (Decidable (_ ∧ _))

def StrictProfile (m : Machine) (name image : Bytes) : Prop :=
  Header m name image ∧ Program m image ∧ Sections m name image ∧
  Symbols m name image ∧ Layout m name image
instance (m : Machine) (n b : Bytes) : Decidable (StrictProfile m n b) := inferInstanceAs (Decidable (_ ∧ _))

structure Loaded where
  body : Bytes
  symbolIndex : Nat
  sectionIndex : Nat
  address : Nat
  fileOffset : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- Decode the owned address/extent through the actual symbol and section.
The candidate index is checked against the exact complete symbol inventory. -/
def decodeNamed (image name : Bytes) : Option Loaded := do
  let table ← readSection image 3
  let symbol ← readSymbol image table 2
  let actualName ← symbolName image table symbol
  if actualName = name then
    let sec ← readSection image symbol.shndx
    let offset := sec.offset + (symbol.value - sec.address)
    some ⟨slice image offset symbol.size,2,symbol.shndx,symbol.value,offset,symbol.size⟩
  else none

/-- Independently stated actual-record ownership, extent and load mapping. -/
def NamedFunction (image name : Bytes) (l : Loaded) : Prop :=
  ∃ table symbol sec,
    readSection image 3 = some table ∧
    readSymbol image table l.symbolIndex = some symbol ∧
    symbolName image table symbol = some name ∧
    readSection image symbol.shndx = some sec ∧
    symbol.info = 18 ∧ symbol.other = 0 ∧ l.sectionIndex = symbol.shndx ∧
    l.address = symbol.value ∧ l.size = symbol.size ∧
    sec.kind = 1 ∧ sec.flags = 6 ∧ sec.alignment = 4 ∧
    sec.address ≤ symbol.value ∧ symbol.value + symbol.size = sec.address + sec.size ∧
    l.fileOffset = sec.offset + (symbol.value - sec.address) ∧
    l.fileOffset = (Oak.MinimalELF.segment image).fileOffset +
      (l.address - (Oak.MinimalELF.segment image).vaddr) ∧
    l.body = slice image l.fileOffset l.size ∧ l.fileOffset + l.size ≤ image.length

def UniqueNamedFunction (image name : Bytes) (table : Section) (index : Nat) : Prop :=
  ∀ i symbol, readSymbol image table i = some symbol →
    symbolName image table symbol = some name → i = index

def candidate (m : Machine) (image : Bytes) : Loaded :=
  ⟨slice image (bodyOffset m) (bodySize m),2,1,bodyAddress m,bodyOffset m,bodySize m⟩

def extract (m : Machine) (name image : Bytes) : Option Loaded :=
  if StrictProfile m name image then decodeNamed image (oakPrefix ++ name) else none

def accepts (m : Machine) (name image expectedBody : Bytes) : Bool :=
  match extract m name image with
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
    (h : Symbols m name image) :
    UniqueNamedFunction image (oakPrefix ++ name) (symSection m) 2 := by
  intro i symbol hs hn
  have bound := symbol_index_bound hs
  change (i+1)*24 ≤ 72 at bound
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with ⟨h0,h1,_,hstart,_,hnul⟩
  rcases cases with h | h | h
  · subst i
    rw [h0] at hs
    cases hs
    rw [hnul] at hn
    simp [oakPrefix] at hn
  · subst i
    rw [h1] at hs
    cases hs
    rw [hstart] at hn
    simp [startName, oakPrefix] at hn
  · exact h

theorem profile_decodes {m : Machine} {name image : Bytes}
    (h : StrictProfile m name image) :
    decodeNamed image (oakPrefix ++ name) = some (candidate m image) := by
  rcases h with ⟨_,_,hsec,hsym,_⟩
  simp only [decodeNamed,Bind.bind,Option.bind,hsec.2.2.2.1,hsym.2.2.1,hsym.2.2.2.2.1]
  simp [functionSymbol,hsec.2.1,textSection,bodyAddress,bodyOffset,candidate]

theorem profile_named {m : Machine} {name image : Bytes}
    (h : StrictProfile m name image) :
    NamedFunction image (oakPrefix ++ name) (candidate m image) := by
  rcases h with ⟨_,hp,hsec,hsym,hl⟩
  refine ⟨symSection m,functionSymbol m,textSection m,hsec.2.2.2.1,
    hsym.2.2.1,hsym.2.2.2.2.1,hsec.2.1,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,rfl,?_⟩
  · simp [functionSymbol,textSection,bodyAddress]
  · simp [functionSymbol,textSection,bodyAddress,textSize,Nat.add_assoc]
  · simp [candidate,functionSymbol,textSection,bodyAddress,bodyOffset]
  · simp [candidate,hp.1,program,bodyAddress,bodyOffset]
  · have bound := hl.2.2.2.2.1
    cases m <;> simp_all [candidate,bodyOffset,textOffset,stubSize,bodySize,loadSize] <;> omega

theorem profile_admitted {m : Machine} {name image : Bytes}
    (h : StrictProfile m name image) : Oak.MinimalELF.admitted m image = true := by
  apply (Oak.MinimalELF.admitted_iff m image).mpr
  refine ⟨h.1.1,?_⟩
  rw [h.2.1.1]
  have bound := h.2.2.2.2.2.2.2.2.1
  cases m <;> simp_all [Oak.MinimalELF.Layout,program,base,textOffset,loadSize]

theorem profile_body {m : Machine} {name image : Bytes}
    (h : StrictProfile m name image) :
    Oak.MinimalELF.BodyAt image (bodyAddress m) (candidate m image).body := by
  have bound := h.2.2.2.2.2.2.2.2.1
  have length : (candidate m image).body.length = bodySize m := by
    simp only [candidate,slice,List.length_take,List.length_drop]
    cases m <;> simp_all [bodyOffset,textOffset,stubSize,bodySize,loadSize] <;> omega
  rw [Oak.MinimalELF.BodyAt,length,h.2.1.1]
  cases m <;> simp [program,candidate,bodyAddress,bodyOffset,base,textOffset,
    stubSize,bodySize,loadSize]

theorem extract_sound {m : Machine} {name image : Bytes} {loaded : Loaded}
    (h : extract m name image = some loaded) :
    StrictProfile m name image ∧ NamedFunction image (oakPrefix ++ name) loaded ∧
    UniqueNamedFunction image (oakPrefix ++ name) (symSection m) loaded.symbolIndex ∧
    loaded = candidate m image := by
  unfold extract at h
  split at h
  · rename_i profile
    rw [profile_decodes profile] at h
    cases h
    exact ⟨profile,profile_named profile,profile_unique profile.2.2.2.1,rfl⟩
  · simp at h

/-- Universal full-file/name/address/extent binding to the explicit flat loader.
No successful evaluator or independently supplied address/size is a premise. -/
theorem accepted_named_load {m : Machine} {name image expectedBody : Bytes}
    (h : accepts m name image expectedBody = true) :
    ∃ loaded, extract m name image = some loaded ∧
      StrictProfile m name image ∧ NamedFunction image (oakPrefix ++ name) loaded ∧
      UniqueNamedFunction image (oakPrefix ++ name) (symSection m) loaded.symbolIndex ∧
      loaded.body = expectedBody ∧ loaded.address = bodyAddress m ∧
      loaded.fileOffset = bodyOffset m ∧ loaded.size = bodySize m ∧
      expectedBody.length = loaded.size ∧
      expectedBody = slice image loaded.fileOffset loaded.size ∧
      Oak.MinimalELF.admittedBytes m image loaded.address expectedBody = true ∧
      Oak.MinimalELF.loadBytes image loaded.address loaded.size = some expectedBody ∧
      loaded.fileOffset + loaded.size ≤ image.length ∧ loaded.address + loaded.size < 2^64 := by
  unfold accepts at h
  split at h
  · rename_i loaded hextract
    have heq : loaded.body = expectedBody := by simpa using h
    obtain ⟨profile,named,unique,hloaded⟩ := extract_sound hextract
    have hb := profile_body profile
    have ha := profile_admitted profile
    have admitted : Oak.MinimalELF.admittedBytes m image loaded.address expectedBody = true := by
      simp only [Oak.MinimalELF.admittedBytes,ha,Bool.true_and,decide_eq_true_eq]
      rw [hloaded] at heq ⊢
      rw [← heq]
      exact hb
    have bounds := Oak.MinimalELF.admitted_bounds admitted
    have length : expectedBody.length = loaded.size := by
      rw [← heq,hloaded]
      simp only [candidate,slice,List.length_take,List.length_drop]
      have bound := profile.2.2.2.2.2.2.2.2.1
      cases m <;> simp_all [bodyOffset,textOffset,stubSize,bodySize,loadSize] <;> omega
    refine ⟨loaded,hextract,profile,named,unique,heq,?_,?_,?_,length,?_,admitted,?_,?_,?_⟩
    · rw [hloaded]; rfl
    · rw [hloaded]; rfl
    · rw [hloaded]; rfl
    · rw [← heq,hloaded]; rfl
    · rw [← length]; exact Oak.MinimalELF.admitted_load admitted
    · rw [length,hloaded,profile.2.1.1] at bounds
      simpa [hloaded,candidate,program,bodyAddress,bodyOffset] using bounds.1
    · simpa [length] using bounds.2
  · simp at h

example : extract .arm64 [102] [] = none := by decide +kernel
example : extract .rv64 [102] [] = none := by decide +kernel
end Oak.NativeBitwiseImage
