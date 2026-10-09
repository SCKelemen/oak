import OakSailImageLoad
import OakSailClockedSource

/-! Original restricted source, complete admitted ET_EXEC, explicit loading and
RX/RW region installation, then nine bounded generated platform callbacks.
Invocation still starts at the separately checked function address, not ELF
entry. ABI registers and the Machine/Bare/PMP/CSR/clock profile are explicit;
startup/reset reachability and opaque platform-loop termination are not proved. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
noncomputable section
namespace OakSailImageSource
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode
open OakSailSteppedFrame OakSailClockTick OakSailPlatformCallback
open OakSailImageLoad Oak.MinimalELF

def accepts (source : List UInt8) (claim : Oak.BitwiseSource.Decl)
    (image : Bytes) (address sp : Nat) : Bool :=
  OakSailFramedComposition.acceptsFrame source claim
    (Oak.RiscVFramedBitwise.functionBytes claim.op) &&
  acceptsImage image address sp (Oak.RiscVFramedBitwise.functionBytes claim.op)

theorem accepts_iff (source : List UInt8) (claim : Oak.BitwiseSource.Decl)
    (image : Bytes) (address sp : Nat) :
    accepts source claim image address sp = true ↔
      OakSailFramedComposition.acceptsFrame source claim
        (Oak.RiscVFramedBitwise.functionBytes claim.op) = true ∧
      acceptsImage image address sp (Oak.RiscVFramedBitwise.functionBytes claim.op) = true := by
  simp [accepts]

/-- The source-bound image acceptance actually selects the explicit checked
load operation, rather than hypothesizing that RAM already contains the code. -/
theorem accepted_load {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {address sp : Nat} (s : State)
    (h : accepts source claim image address sp = true) :
    checkedLoad s image address sp (Oak.RiscVFramedBitwise.functionBytes claim.op) =
      some (installImage s image sp) :=
  checkedLoad_success s image address sp _ ((accepts_iff _ _ _ _ _).mp h).2

theorem loaded_stepProfile (s : State) (image : Bytes) (sp : Nat) (h : StepProfile s) :
    StepProfile (installImage s image sp) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  constructor <;> simpa using ‹_›

theorem loaded_clockProfile (s : State) (image : Bytes) (sp : Nat) (c t d : BitVec 64)
    (h : ClockProfile s c t d) : ClockProfile (installImage s image sp) c t d := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> simpa using ‹_›

/-- No code-byte, per-word permission, alignment, code/stack separation, or
fetch-success hypotheses remain: they are consequences of the file check and
explicit load. The caller supplies only invocation/platform initialization. -/
theorem accepted_typed_image_clocked_prefix
    {source : List UInt8} {claim : Oak.BitwiseSource.Decl} {image : Bytes} {address sp : Nat}
    (accepted : accepts source claim image address sp = true)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (saved1 saved2 ra : BitVec 64) (step : Nat) (c t d : BitVec 64)
    (previous : List PMA_Region)
    (hc : MemoryConfig s previous) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat + 4 < d.toNat)
    (hsp : s.regs.get? Register.x2 = some (BitVec.ofNat 64 sp))
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra) (halign : ReturnAligned ra)
    (hpc : s.regs.get? Register.PC = some (BitVec.ofNat 64 address))
    (hn : s.regs.get? Register.nextPC = some (BitVec.ofNat 64 address))
    (hi : s.regs.get? Register.minstret_increment = some false) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 9 (0,step)).run (installImage s image sp) = .ok (1,step)
      (clockState (finalSteppedState (installImage s image sp) (BitVec.ofNat 64 sp) saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) ra)
        (c+4#64) (t+4#64)) := by
  obtain ⟨hsource,himage⟩ := (accepts_iff _ _ _ _ _).mp accepted
  have hcode := frame_code s image address sp claim.op himage
  have hcfg : ConfigOK (installImage s image sp) := by
    exact ⟨by simpa using hp.privilege, by simpa using hc.masking, by simpa using hp.isa⟩
  apply OakSailClockedSource.accepted_typed_clocked_prefix hsource left right fuel
    (installImage s image sp) (BitVec.ofNat 64 sp) saved1 saved2 ra (BitVec.ofNat 64 address)
    step c t d (imageRegions image sp) (stackRegion sp) (stackRegion sp)
    (fun _ => imageRegion image)
    (loaded_memoryConfig s image sp previous hc) hcfg (loaded_stepProfile s image sp hp)
    (loaded_clockProfile s image sp c t d hclock) hdeadline
    (stack_access image sp ((acceptsImage_iff _ _ _ _).mp himage).2)
    (by simpa using hsp) (by simpa using h1) (by simpa using h2)
    (by simpa using hl) (by simpa using hr) (by simpa using hra) halign
    (by simpa using hpc) (by simpa using hn) (by simpa using hi)
    hcode.1 hcode.2.1 hcode.2.2 (code_stack_disjoint image address sp claim.op himage)
    (fun i => (executable_frame image address sp claim.op himage i).1)
    (fun i => (executable_frame image address sp claim.op himage i).2)

end OakSailImageSource
