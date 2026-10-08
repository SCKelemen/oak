import Std

/-!
# Narrow ELF64 file-to-load admission

A checked profile of the production executable writer: ELF64 little endian,
ET_EXEC, one readable/executable PT_LOAD, 4 KiB alignment, no zero-fill tail,
entry at segment start, and bounded file/64-bit address extents. RV64 is the
uncompressed LP64D profile (e_flags=4); AArch64 has e_flags=0. Section and
symbol tables are not interpreted: PT_LOAD, not .text, defines loaded bytes.

`loadBytes` is an explicit flat loader specification. There is no theorem
about a host kernel/firmware's ELF loader, instruction-fetch permissions or
traps, startup execution, relocation implementation or source provenance.
An admitted body is tied to this exact file's bytes and address, not merely
its size or an independently supplied body. Production authority is unchanged.
-/
set_option autoImplicit false
namespace Oak.MinimalELF
abbrev Bytes := List (BitVec 8)
inductive Machine where
  | rv64 | arm64
  deriving DecidableEq, Repr

def Machine.number : Machine → Nat | .rv64 => 243 | .arm64 => 183
def Machine.abiFlags : Machine → Nat | .rv64 => 4 | .arm64 => 0

def slice (image : Bytes) (offset count : Nat) : Bytes := (image.drop offset).take count
/-- Total byte reader; header admission separately requires all 120 bytes. -/
def readLE (image : Bytes) (offset count : Nat) : Nat :=
  (slice image offset count).foldr (fun b n => b.toNat + 256 * n) 0

structure Segment where
  entry : Nat
  fileOffset : Nat
  vaddr : Nat
  fileSize : Nat
  memorySize : Nat
  flags : Nat
  alignment : Nat
  deriving DecidableEq, Repr

def segment (image : Bytes) : Segment :=
  ⟨readLE image 24 8, readLE image 72 8, readLE image 80 8,
   readLE image 96 8, readLE image 104 8, readLE image 68 4, readLE image 112 8⟩

def Header (machine : Machine) (image : Bytes) : Prop :=
  120 ≤ image.length ∧
  slice image 0 16 = [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
  readLE image 16 2 = 2 ∧ readLE image 18 2 = machine.number ∧
  readLE image 20 4 = 1 ∧ readLE image 32 8 = 64 ∧
  readLE image 48 4 = machine.abiFlags ∧ readLE image 52 2 = 64 ∧
  readLE image 54 2 = 56 ∧ readLE image 56 2 = 1 ∧ readLE image 64 4 = 1

instance (m : Machine) (b : Bytes) : Decidable (Header m b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Strict profile uses one fully file-backed, page-congruent RX segment. -/
def Layout (image : Bytes) (s : Segment) : Prop :=
  s.flags = 5 ∧ s.alignment = 4096 ∧ 120 ≤ s.fileOffset ∧
  s.fileOffset % 4096 = s.vaddr % 4096 ∧ s.vaddr % 4096 = 0 ∧
  0 < s.fileSize ∧ s.memorySize = s.fileSize ∧
  s.fileOffset + s.fileSize ≤ image.length ∧ s.vaddr + s.memorySize < 2^64 ∧
  s.entry = s.vaddr
instance (b : Bytes) (s : Segment) : Decidable (Layout b s) := inferInstanceAs (Decidable (_ ∧ _))

def admitted (machine : Machine) (image : Bytes) : Bool :=
  decide (Header machine image ∧ Layout image (segment image))

def BodyAt (image : Bytes) (address : Nat) (body : Bytes) : Prop :=
  0 < body.length ∧ address % 4 = 0 ∧ (segment image).vaddr ≤ address ∧
  address + body.length ≤ (segment image).vaddr + (segment image).fileSize ∧
  slice image ((segment image).fileOffset + (address - (segment image).vaddr)) body.length = body
instance (b : Bytes) (a : Nat) (code : Bytes) : Decidable (BodyAt b a code) := inferInstanceAs (Decidable (_ ∧ _))

def admittedBytes (machine : Machine) (image : Bytes) (address : Nat) (body : Bytes) : Bool :=
  admitted machine image && decide (BodyAt image address body)

theorem admitted_iff (machine : Machine) (image : Bytes) :
    admitted machine image = true ↔ Header machine image ∧ Layout image (segment image) := by
  simp [admitted]

theorem admitted_body (machine : Machine) (image : Bytes) (address : Nat) (body : Bytes) :
    admittedBytes machine image address body = true ↔
      Header machine image ∧ Layout image (segment image) ∧ BodyAt image address body := by
  simp [admittedBytes, admitted, and_assoc]

/-- Flat file-backed loading, with explicit bounds and no address wrapping. -/
def loadBytes (image : Bytes) (address count : Nat) : Option Bytes :=
  let s := segment image
  if s.vaddr ≤ address ∧ address + count ≤ s.vaddr + s.fileSize ∧
      s.fileOffset + s.fileSize ≤ image.length ∧ s.vaddr + s.fileSize < 2^64 then
    some (slice image (s.fileOffset + (address - s.vaddr)) count)
  else none

theorem admitted_load {machine : Machine} {image : Bytes} {address : Nat} {body : Bytes}
    (h : admittedBytes machine image address body = true) :
    loadBytes image address body.length = some body := by
  obtain ⟨_, hl, hb⟩ := (admitted_body machine image address body).mp h
  rcases hl with ⟨_, _, _, _, _, _, hm, hf, ha, _⟩
  rcases hb with ⟨_, _, hlow, hhigh, heq⟩
  simp only [hm] at ha
  simp [loadBytes, hlow, hhigh, hf, ha, heq]

/-- Body placement cannot underflow, overrun the file, or wrap a u64 PC. -/
theorem admitted_bounds {machine : Machine} {image : Bytes} {address : Nat} {body : Bytes}
    (h : admittedBytes machine image address body = true) :
    (segment image).fileOffset + (address - (segment image).vaddr) + body.length ≤ image.length ∧
      address + body.length < 2^64 := by
  obtain ⟨_, hl, hb⟩ := (admitted_body machine image address body).mp h
  rcases hl with ⟨_, _, _, _, _, _, hm, hf, ha, _⟩
  rcases hb with ⟨_, _, hlow, hhigh, _⟩
  omega

/-- Transport a successful byte evaluator through the admitted file slice.
The caller chooses the execution semantics, input and success value. -/
theorem admitted_execution {machine : Machine} {image : Bytes} {address : Nat} {body : Bytes}
    {α : Type} (execute : Bytes → Option α) (value : α)
    (h : admittedBytes machine image address body = true)
    (success : execute body = some value) :
    (loadBytes image address body.length).bind execute = some value := by
  rw [admitted_load h]
  exact success

example : admitted .rv64 [] = false := by decide +kernel
example : admitted .arm64 [] = false := by decide +kernel
example (m : Machine) (image : Bytes) (address : Nat) :
    admittedBytes m image address [] = false := by simp [admittedBytes, BodyAt]
end Oak.MinimalELF
