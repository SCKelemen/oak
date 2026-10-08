import Oak.AArch64BitwiseFunction
import Oak.MinimalELF

/-!
# Minimal Linux ARM64 startup request projection

The concrete Oak compiler output for `main: (): i32 { 42 }` is a 20-byte
text section: BL main; MOVZ W8,93; SVC0; MOVZ W0,42; RET X30. Five decoded
steps, in execution rather than file order, reach a syscall request with
X8=93 and X0=42. This theorem says nothing about Linux satisfying that
request, loading ELF segments, initial page mappings, or real Arm fetch,
PostDecode/BranchTo/exception behavior. It is a local no-fault CPU projection.
The source spelling is provenance recorded by a finite compiler test; there
is no source parser/lowering theorem in this module.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
namespace Oak.AArch64MinimalStartup

open Oak.AArch64BitwiseFunction (State Registers takeWord decodeRet readX writeW)

inductive Event where
  | next (state : State)
  | syscall (number argument : BitVec 64)

abbrev Bytes := List UInt8

def writeX (regs : Registers) (r : BitVec 5) (value : BitVec 64) : Registers :=
  fun q => if r != 31#5 && q == r then value else regs q

/-- Only BL, MOVZ Wd,#imm16 (LSL0), ordinary RET, and SVC0 are supported. -/
def step (word : BitVec 32) (s : State) : Option Event :=
  if word &&& 0xfc000000#32 == 0x94000000#32 then
    let offset := (word.extractLsb' 0 26 ++ 0#2).signExtend 64
    some (.next { s with regs := writeX s.regs 30#5 (s.pc + 4), pc := s.pc + offset })
  else if word &&& 0xffe00000#32 == 0x52800000#32 then
    let value := (word.extractLsb' 5 16).zeroExtend 32
    some (.next { s with regs := writeW s.regs (word.extractLsb' 0 5) value, pc := s.pc + 4 })
  else if word == 0xd4000001#32 then
    some (.syscall (s.regs 8#5) (s.regs 0#5))
  else do
    let rn ← decodeRet word
    some (.next { s with pc := readX s.regs rn })

/-- Fetch only aligned, complete instructions within supplied text bytes.
This reads a list provided by the caller, not mapped architectural memory. -/
def fetch (base : Nat) (text : Bytes) (pc : BitVec 64) : Option (BitVec 32) := do
  if pc.toNat < base || (pc.toNat - base) % 4 != 0 then none
  else
    let (word, _) ← takeWord (text.drop (pc.toNat - base))
    some word

/-- Fuel bounds a concrete finite trace, and running out is failure. -/
def run : Nat → Nat → Bytes → State → Option (BitVec 64 × BitVec 64)
  | 0, _, _, _ => none
  | fuel + 1, base, text, s => do
      let word ← fetch base text s.pc
      let event ← step word s
      match event with
      | .next next => run fuel base text next
      | .syscall number argument => some (number, argument)

def textBytes : Bytes :=
  [0x03,0x00,0x00,0x94, 0xa8,0x0b,0x80,0x52, 0x01,0x00,0x00,0xd4,
   0x40,0x05,0x80,0x52, 0xc0,0x03,0x5f,0xd6]

/-- BL saves the startup continuation, main writes 42, RET returns to it,
MOVZ selects syscall93, then SVC0 reports the request. All initial registers,
SP and flags are arbitrary; this is independent of caller X30. -/
theorem startup_request (regs : Registers) (sp : BitVec 64) (nzcv : BitVec 4) :
    run 5 0x10000 textBytes ⟨regs, 0x10000#64, sp, nzcv⟩ =
      some (93#64, 42#64) := by simp [run, fetch, step, textBytes, takeWord, writeX, writeW, decodeRet, readX]

/-- Four steps cannot reach the request: the instruction count is checked. -/
example (regs : Registers) (sp : BitVec 64) (nzcv : BitVec 4) :
    run 4 0x10000 textBytes ⟨regs, 0x10000#64, sp, nzcv⟩ = none := by simp [run, fetch, step, textBytes, takeWord, writeX, writeW, decodeRet, readX]

example : fetch 0x10000 textBytes 0x10001#64 = none := by decide +kernel
example : fetch 0x10000 textBytes 0xffff#64 = none := by decide +kernel
example : fetch 0x10000 textBytes 0x10014#64 = none := by decide +kernel

/-- Byte representation used by the target-independent ELF parser. -/
def fileText : Oak.MinimalELF.Bytes :=
  textBytes.map (fun b => BitVec.ofNat 8 b.toNat)

def executeLoaded (regs : Registers) (sp : BitVec 64) (nzcv : BitVec 4)
    (bytes : Oak.MinimalELF.Bytes) : Option (BitVec 64 × BitVec 64) :=
  run 5 0x10000 (bytes.map (fun b => UInt8.ofNat b.toNat))
    ⟨regs, 0x10000#64, sp, nzcv⟩

/-- Exact code placement alone does not say it is the entrypoint: bind both. -/
def acceptsImage (image : Oak.MinimalELF.Bytes) : Bool :=
  Oak.MinimalELF.admittedBytes .arm64 image 0x10000 fileText &&
    decide ((Oak.MinimalELF.segment image).entry = 0x10000)

theorem admitted_startup_request (image : Oak.MinimalELF.Bytes)
    (accepted : acceptsImage image = true)
    (regs : Registers) (sp : BitVec 64) (nzcv : BitVec 4) :
    (Oak.MinimalELF.segment image).entry = 0x10000 ∧
    (Oak.MinimalELF.loadBytes image 0x10000 fileText.length).bind
      (executeLoaded regs sp nzcv) = some (93#64, 42#64) := by
  have h : Oak.MinimalELF.admittedBytes .arm64 image 0x10000 fileText = true ∧
      (Oak.MinimalELF.segment image).entry = 0x10000 := by
    simpa [acceptsImage] using accepted
  refine ⟨h.2, Oak.MinimalELF.admitted_execution _ _ h.1 ?_⟩
  change run 5 0x10000 textBytes ⟨regs, 0x10000#64, sp, nzcv⟩ = _
  exact startup_request regs sp nzcv

end Oak.AArch64MinimalStartup
