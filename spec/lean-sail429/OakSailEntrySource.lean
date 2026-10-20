import OakSailEntryInstructions

/-! Checked original ELF entry through its actual two-instruction call into
the source-bound frame. Initial platform/ABI state is explicit. The eleven
callbacks stop on return, before the exit-number instruction and ECALL. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailEntrySource
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode
open OakSailSteppedState OakSailSteppedFetch OakSailSteppedFrame
open OakSailClockTick OakSailClockedState OakSailPlatformCallback OakSailClockedPrefix
open OakSailImageLoad OakSailImageSource OakSailEntryInstructions Oak.MinimalELF

/-- Body location is derived from this checked call pair, not an independent
PC supplied to the execution theorem. All bytes still bind to this exact file. -/
def acceptsEntry (source : List UInt8) (claim : Oak.BitwiseSource.Decl)
    (image : Bytes) (sp : Nat) : Bool :=
  accepts source claim image ((segment image).entry+16) sp &&
    admittedBytes .rv64 image (segment image).entry startupBytes

theorem acceptsEntry_iff (source : List UInt8) (claim : Oak.BitwiseSource.Decl)
    (image : Bytes) (sp : Nat) :
    acceptsEntry source claim image sp = true ↔
      accepts source claim image ((segment image).entry+16) sp = true ∧
      admittedBytes .rv64 image (segment image).entry startupBytes = true := by
  simp [acceptsEntry]

/-- The complete checked artifact selects the existing explicit load operation. -/
theorem accepted_load {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (s : State) (h : acceptsEntry source claim image sp = true) :
    checkedLoad s image ((segment image).entry+16) sp (Oak.RiscVFramedBitwise.functionBytes claim.op) =
      some (installImage s image sp) :=
  OakSailImageSource.accepted_load s ((acceptsEntry_iff _ _ _ _).mp h).1

def entryAddress (image : Bytes) : BitVec 64 := BitVec.ofNat 64 (segment image).entry

def entryState (s : State) (image : Bytes) (sp : Nat) : State :=
  controlState (installImage s image sp) (entryAddress image) (entryAddress image)

def returnAddress (image : Bytes) : BitVec 64 := entryAddress image + 8#64

def bodyEntryState (s : State) (image : Bytes) (sp : Nat) : State :=
  calledState (installImage s image sp) (entryAddress image)

theorem accepted_entry_code {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (s : State) (h : acceptsEntry source claim image sp = true) :
    EntryCodeAt (installImage s image sp) (entryAddress image) := by
  obtain ⟨hb,hp⟩ := (acceptsEntry_iff _ _ _ _).mp h
  have hb' := ((accepts_iff _ _ _ _ _).mp hb).2
  have ha := (acceptsImage_iff _ _ _ _).mp hb'
  have body := (admitted_body .rv64 _ _ _).mp ha.1
  have prefixFacts := (admitted_body .rv64 _ _ _).mp hp
  have hlen : (Oak.RiscVFramedBitwise.functionBytes claim.op).length = 36 := by cases claim.op <;> rfl
  have low := ha.2.1
  have hi := body.2.2.2.2.2.1
  rw [hlen] at hi
  have he : (segment image).entry < 2^64 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [entryAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he] using
      loaded_body s image (segment image).entry sp startupBytes hp
  · simpa only [entryAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he] using prefixFacts.2.2.2.1
  · simp only [entryAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]
    omega

theorem accepted_entry_permissions {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (h : acceptsEntry source claim image sp = true) (i : Fin 2) :
    ExecutableRegion (imageRegions image sp) (entryPC (entryAddress image) i) (imageRegion image) ∧
      LowCodeRAM (entryPC (entryAddress image) i) := by
  obtain ⟨hb,hp⟩ := (acceptsEntry_iff _ _ _ _).mp h
  have ha := (acceptsImage_iff _ _ _ _).mp ((accepts_iff _ _ _ _ _).mp hb).2
  obtain ⟨_,layout,body⟩ := (admitted_body .rv64 _ _ _).mp ha.1
  have hlen : (Oak.RiscVFramedBitwise.functionBytes claim.op).length = 36 := by cases claim.op <;> rfl
  have hhigh := body.2.2.2.1
  rw [hlen] at hhigh
  have hentry : (segment image).entry = (segment image).vaddr := layout.2.2.2.2.2.2.2.2.2
  have hi := i.isLt
  have hlow := ha.2.1
  have haddr : (segment image).entry+4 * i.val < 2^64 := by omega
  have hcode : entryPC (entryAddress image) i = BitVec.ofNat 64 ((segment image).entry+4 * i.val) := by
    simp only [entryPC, entryAddress, BitVec.ofNat_add]
  have halign := ((admitted_body .rv64 _ _ _).mp hp).2.2.2.1
  rw [hcode]
  constructor
  · refine ⟨image_region_matches image sp _ (by omega) (by omega) (by omega), rfl, ?_⟩
    apply aligned_paddr
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr]
    omega
  · unfold LowCodeRAM
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr]
    omega

/-- The original ELF entry executes its two fetched call instructions, then
nine source-bound body callbacks. No initial RA or function-entry PC premise
is supplied. The fifth tick remains strictly before the initialized deadline. -/
theorem accepted_typed_entry_clocked_prefix
    {source : List UInt8} {claim : Oak.BitwiseSource.Decl} {image : Bytes} {sp : Nat}
    (accepted : acceptsEntry source claim image sp = true)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (saved1 saved2 : BitVec 64) (step : Nat) (c t d : BitVec 64)
    (previous : List PMA_Region)
    (hc : MemoryConfig s previous) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat + 5 < d.toNat)
    (hsp : s.regs.get? Register.x2 = some (BitVec.ofNat 64 sp))
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right)) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 11 (0,step)).run (entryState s image sp) = .ok (1,step)
      (clockState (finalSteppedState (bodyEntryState s image sp) (BitVec.ofNat 64 sp) saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (returnAddress image))
        (c+5#64) (t+5#64)) := by
  obtain ⟨hb,_⟩ := (acceptsEntry_iff _ _ _ _).mp accepted
  obtain ⟨hsource,himage⟩ := (accepts_iff _ _ _ _ _).mp hb
  let loaded := installImage s image sp
  let body := bodyEntryState s image sp
  let ticking := clockState body (c+1#64) (t+1#64)
  have hm : MemoryConfig loaded (imageRegions image sp) := loaded_memoryConfig s image sp previous hc
  have hs : StepProfile loaded := loaded_stepProfile s image sp hp
  have hk : ClockProfile loaded c t d := loaded_clockProfile s image sp c t d hclock
  have hcfg : ConfigOK loaded := ⟨by simpa [loaded] using hp.privilege,
    by simpa [loaded] using hc.masking, by simpa [loaded] using hp.isa⟩
  have bm : MemoryConfig body (imageRegions image sp) :=
    control_memoryConfig _ _ _ _ (x1_memoryConfig _ _ _ hm)
  have bs : StepProfile body := control_stepProfile _ _ _ (x1_stepProfile _ _ hs)
  have bk : ClockProfile body c t d := control_clockProfile _ _ _ _ _ _ (x1_clockProfile _ _ _ _ _ hk)
  have bc : ConfigOK body := control_config _ _ _ (x1_config _ _ hcfg)
  have code := frame_code s image ((segment image).entry+16) sp claim.op himage
  have prefixCode := accepted_entry_code s accepted
  have bodyAddress : entryAddress image+16#64 = BitVec.ofNat 64 ((segment image).entry+16) := by
    simp only [entryAddress, BitVec.ofNat_add]
  have align : ReturnAligned (returnAddress image) := by
    have ha := entry_add_aligned (entryAddress image) 8 prefixCode.2.2 prefixCode.2.1 (by decide) (by decide)
    apply aligned4_bits
    rw [clear_aligned (returnAddress image) ha]
    exact ha
  have deadline : (t+1#64).toNat+4 < d.toNat := by
    rw [timer_add_toNat t d 1 (by omega)]
    omega
  have bodyRun := OakSailClockedSource.accepted_typed_clocked_prefix hsource left right fuel
    ticking (BitVec.ofNat 64 sp) saved1 saved2 (returnAddress image)
    (BitVec.ofNat 64 ((segment image).entry+16)) step (c+1#64) (t+1#64) d
    (imageRegions image sp) (stackRegion sp) (stackRegion sp) (fun _ => imageRegion image)
    (clockState_memoryConfig _ _ _ _ bm) (clockState_config _ _ _ bc)
    (clockState_stepProfile _ _ _ bs) (clockState_profile _ c t d _ _ bk) deadline
    (stack_access image sp ((acceptsImage_iff _ _ _ _).mp himage).2)
    (by simpa [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert] using hsp)
    (by simpa [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert] using h1)
    (by simpa [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert] using h2)
    (by simpa [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert] using hl)
    (by simpa [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert] using hr)
    (by simp [ticking, body, bodyEntryState, calledState, controlState, clockState,
      returnAddress, setRegister, Std.ExtDHashMap.get?_insert]) align
    (by simp [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert, bodyAddress])
    (by simp [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert, bodyAddress])
    (by simp [ticking, body, bodyEntryState, calledState, controlState, clockState,
      setRegister, Std.ExtDHashMap.get?_insert])
    code.1 code.2.1 code.2.2 (code_stack_disjoint image _ sp claim.op himage)
    (fun i => (executable_frame image _ sp claim.op himage i).1)
    (fun i => (executable_frame image _ sp claim.op himage i).2)
  refine ⟨bodyRun.1, bodyRun.2.1, ?_⟩
  apply startup_then loaded (entryAddress image) step c t d
    (imageRegions image sp) (imageRegion image) hm hcfg hs hk (by omega)
    prefixCode (fun i => (accepted_entry_permissions accepted i).1)
    (fun i => (accepted_entry_permissions accepted i).2) 9 (1,step) _
  simpa only [ticking, body, finalStepped_clockState, clockState_same,
    BitVec.add_assoc, BitVec.reduceAdd] using bodyRun.2.2

end OakSailEntrySource
