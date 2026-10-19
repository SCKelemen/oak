import OakSailExitInstructions
import OakSailBoundedAppend

/-! Stronger full-image admission binds the post-return ADDI and ECALL.
The result is Machine/Bare register/PC readiness, not syscall delivery. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailExitSource
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode OakSailFetchedFrame
open OakSailSteppedState OakSailSteppedFetch OakSailSteppedFrame
open OakSailClockTick OakSailClockedState OakSailClockedPrefix OakSailPlatformCallback
open OakSailImageLoad OakSailImageSource OakSailEntryInstructions OakSailEntrySource
open OakSailExitInstructions Oak.MinimalELF

def acceptsExit (source : List UInt8) (claim : Oak.BitwiseSource.Decl)
    (image : Bytes) (sp : Nat) : Bool :=
  acceptsEntry source claim image sp &&
    admittedBytes .rv64 image ((segment image).entry+8) exitBytes

theorem acceptsExit_iff (source : List UInt8) (claim : Oak.BitwiseSource.Decl)
    (image : Bytes) (sp : Nat) :
    acceptsExit source claim image sp = true ↔
      acceptsEntry source claim image sp = true ∧
      admittedBytes .rv64 image ((segment image).entry+8) exitBytes = true := by
  simp [acceptsExit]

theorem accepted_load {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (s : State) (h : acceptsExit source claim image sp = true) :
    checkedLoad s image ((segment image).entry+16) sp (Oak.RiscVFramedBitwise.functionBytes claim.op) =
      some (installImage s image sp) :=
  OakSailEntrySource.accepted_load s ((acceptsExit_iff _ _ _ _).mp h).1

def returnedState (s : State) (image : Bytes) (sp : Nat)
    (saved1 saved2 result : BitVec 64) : State :=
  finalSteppedState (bodyEntryState s image sp) (BitVec.ofNat 64 sp)
    saved1 saved2 result (returnAddress image)

def readyState (s : State) (image : Bytes) (sp : Nat)
    (saved1 saved2 result c t : BitVec 64) : State :=
  clockState (controlState (setRegister (returnedState s image sp saved1 saved2 result) .x17 (93#64))
    (entryAddress image+12#64) (entryAddress image+12#64)) c t

theorem returned_profiles (s : State) (image : Bytes) (sp : Nat)
    (saved1 saved2 result c t d : BitVec 64) (previous : List PMA_Region)
    (hm : MemoryConfig s previous) (hp : StepProfile s) (hk : ClockProfile s c t d) :
    MemoryConfig (returnedState s image sp saved1 saved2 result) (imageRegions image sp) ∧
    StepProfile (returnedState s image sp saved1 saved2 result) ∧
    ClockProfile (returnedState s image sp saved1 saved2 result) c t d := by
  have hmc := loaded_memoryConfig s image sp previous hm
  have hpc := loaded_stepProfile s image sp hp
  have hkc := loaded_clockProfile s image sp c t d hk
  rcases hmc with ⟨m1,m2,m3,m4,m5,m6,m7⟩
  rcases hpc with ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩
  rcases hkc with ⟨c1,c2,c3,c4,c5,c6⟩
  refine ⟨?_,?_,?_⟩ <;> constructor <;>
    simpa only [returnedState, bodyEntryState, calledState, finalSteppedState, finalFrameState,
      controlState, setRegister, Std.ExtDHashMap.get?_insert, frameSavedMemory_regs,
      reduceCtorEq, ↓reduceDIte] using ‹_›

theorem returned_segment_preserved (s : State) (image : Bytes) (sp : Nat)
    (saved1 saved2 result : BitVec 64) (h : ImageLayout image sp) (query : Nat)
    (hq : (segment image).vaddr ≤ query ∧ query < (segment image).vaddr+(segment image).fileSize) :
    (returnedState s image sp saved1 saved2 result).mem.get? query =
      (installImage s image sp).mem.get? query := by
  have heq := stack_bits image sp h
  have hs := h.2.1
  have he := h.2.2.1
  have hsep := h.2.2.2.2
  have hb : sp-96 < 2^64 := by omega
  have hn : sp-96+8 < 2^64 := by omega
  apply stepped_memory_other
  · rw [heq.1]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    omega
  · rw [heq.2]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    omega

/-- The two suffix words survive the body frame stores because the entire
loaded segment, not merely the body, is disjoint from the reserved stack. -/
theorem returned_exit_bytes {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (h : acceptsExit source claim image sp = true)
    (s : State) (saved1 saved2 result : BitVec 64) :
    BytesAt (returnedState s image sp saved1 saved2 result) ((segment image).entry+8) exitBytes := by
  obtain ⟨he,hx⟩ := (acceptsExit_iff _ _ _ _).mp h
  have ha := (acceptsImage_iff _ _ _ _).mp
    ((accepts_iff _ _ _ _ _).mp ((acceptsEntry_iff _ _ _ _).mp he).1).2
  have placed := loaded_body s image ((segment image).entry+8) sp exitBytes hx
  have body := ((admitted_body .rv64 _ _ _).mp hx).2.2
  intro i
  rw [returned_segment_preserved s image sp saved1 saved2 result ha.2 _ (by
    have hi := i.isLt
    change i.val < 8 at hi
    have lo := body.2.2.1
    have up := body.2.2.2.1
    change (segment image).entry+8+8 ≤ (segment image).vaddr+(segment image).fileSize at up
    omega)]
  exact placed i

theorem suffix_permissions {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (h : acceptsExit source claim image sp = true) (offset : Nat)
    (ho : offset = 8 ∨ offset = 12) :
    ExecutableRegion (imageRegions image sp) (entryAddress image+BitVec.ofNat 64 offset) (imageRegion image) ∧
      LowCodeRAM (entryAddress image+BitVec.ofNat 64 offset) := by
  obtain ⟨he,hx⟩ := (acceptsExit_iff _ _ _ _).mp h
  have ha := (acceptsImage_iff _ _ _ _).mp
    ((accepts_iff _ _ _ _ _).mp ((acceptsEntry_iff _ _ _ _).mp he).1).2
  obtain ⟨_,layout,body⟩ := (admitted_body .rv64 _ _ _).mp hx
  have hentry : (segment image).entry = (segment image).vaddr := layout.2.2.2.2.2.2.2.2.2
  have hi := body.2.2.2.1
  change (segment image).entry+8+8 ≤ (segment image).vaddr+(segment image).fileSize at hi
  have low := ha.2.1
  have haddr : (segment image).entry+offset < 2^64 := by omega
  have aligned := body.2.1
  have eq : entryAddress image+BitVec.ofNat 64 offset = BitVec.ofNat 64 ((segment image).entry+offset) := by
    simp only [entryAddress, BitVec.ofNat_add]
  rw [eq]
  constructor
  · refine ⟨image_region_matches image sp _ (by omega) (by omega) (by omega), rfl, ?_⟩
    apply aligned_paddr
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr]
    omega
  · unfold LowCodeRAM
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr]
    omega

def exitWord (i : Fin 2) : BitVec 32 := if i.val = 0 then 0x05d00893 else 0x00000073

theorem exit_word_bytes {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (h : acceptsExit source claim image sp = true)
    (s : State) (saved1 saved2 result : BitVec 64) (i : Fin 2) :
    ∀ j : Fin 4, (returnedState s image sp saved1 saved2 result).mem.get?
      ((entryAddress image+BitVec.ofNat 64 (8+4 * i.val)).toNat + j.val) =
      some ((exitWord i).extractLsb' (8 * j.val) 8) := by
  obtain ⟨he,hx⟩ := (acceptsExit_iff _ _ _ _).mp h
  have ha := (acceptsImage_iff _ _ _ _).mp
    ((accepts_iff _ _ _ _ _).mp ((acceptsEntry_iff _ _ _ _).mp he).1).2
  have body := ((admitted_body .rv64 _ _ _).mp hx).2.2
  have hi := i.isLt
  have upper := body.2.2.2.1
  change (segment image).entry+8+8 ≤ (segment image).vaddr+(segment image).fileSize at upper
  have low := ha.2.1
  have addr : (segment image).entry+(8+4 * i.val) < 2^64 := by omega
  intro j
  have hj := j.isLt
  have b := returned_exit_bytes h s saved1 saved2 result ⟨4 * i.val+j.val, by change 4 * i.val+j.val < 8; omega⟩
  have eq : entryAddress image+BitVec.ofNat 64 (8+4 * i.val) =
      BitVec.ofNat 64 ((segment image).entry+(8+4 * i.val)) := by
    simp only [entryAddress, BitVec.ofNat_add]
  rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt addr]
  have ci : i.val = 0 ∨ i.val = 1 := by omega
  have cj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases ci with hi|hi <;> rcases cj with hj|hj|hj|hj <;>
    simpa [exitWord, exitBytes, hi, hj, Nat.add_assoc] using b

/-- Exact machine-side readiness, including real fetch and decode. This does
not execute ECALL or assert any host interpretation of these ABI registers. -/
def ExitReady (s : State) (entry : BitVec 64) (result : BitVec 32) : Prop :=
  s.regs.get? Register.PC = some (entry+12#64) ∧
  s.regs.get? Register.nextPC = some (entry+12#64) ∧
  s.regs.get? Register.x17 = some (93#64) ∧
  s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false result) ∧
  (fetch ()).run s = .ok (.F_Base (0x00000073#32)) s ∧
  (ext_decode (0x00000073#32)).run s = .ok (.ECALL ()) s

/-- Original source and complete ELF through callback twelve. The sixth tick
is real, ECALL is only fetched/decoded, and the u32 result uses RV64's existing
sign-extended 32-bit ABI representation. No Linux delivery follows from this. -/
theorem accepted_typed_exit_ready
    {source : List UInt8} {claim : Oak.BitwiseSource.Decl} {image : Bytes} {sp : Nat}
    (accepted : acceptsExit source claim image sp = true)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (saved1 saved2 : BitVec 64) (step : Nat) (c t d : BitVec 64)
    (previous : List PMA_Region)
    (hc : MemoryConfig s previous) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat+6 < d.toNat)
    (hsp : s.regs.get? Register.x2 = some (BitVec.ofNat 64 sp))
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right)) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 12 (0,step)).run (entryState s image sp) = .ok (0,step)
      (readyState s image sp saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (c+6#64) (t+6#64)) ∧
    ExitReady (readyState s image sp saved1 saved2
      (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (c+6#64) (t+6#64))
      (entryAddress image) (Oak.BitwiseFunction.eval claim.op left right) := by
  have he := ((acceptsExit_iff _ _ _ _).mp accepted).1
  let result := Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)
  let returned := returnedState s image sp saved1 saved2 result
  let before := clockState returned (c+5#64) (t+5#64)
  let last := controlState (setRegister before .x17 (93#64))
    (entryAddress image+12#64) (entryAddress image+12#64)
  let final := readyState s image sp saved1 saved2 result (c+6#64) (t+6#64)
  have prefixRun := accepted_typed_entry_clocked_prefix he left right fuel s saved1 saved2
    step c t d previous hc hp hclock (by omega) hsp h1 h2 hl hr
  obtain ⟨rm,rp,rk⟩ := returned_profiles s image sp saved1 saved2 result c t d previous hc hp hclock
  have rc : ConfigOK returned := ⟨rp.privilege,rm.masking,rp.isa⟩
  have bm : MemoryConfig before (imageRegions image sp) := clockState_memoryConfig _ _ _ _ rm
  have bp : StepProfile before := clockState_stepProfile _ _ _ rp
  have bk : ClockProfile before (c+5#64) (t+5#64) d := clockState_profile _ c t d _ _ rk
  have bc : ConfigOK before := clockState_config _ _ _ rc
  have code := accepted_entry_code s he
  have ar := entry_add_aligned (entryAddress image) 8 code.2.2 code.2.1 (by decide) (by decide)
  have ae := entry_add_aligned (entryAddress image) 12 code.2.2 code.2.1 (by decide) (by decide)
  have pc := clocked_pc_and_next (bodyEntryState s image sp) (BitVec.ofNat 64 sp)
    saved1 saved2 result (returnAddress image) (c+5#64) (t+5#64)
  rw [clear_aligned (returnAddress image) ar] at pc
  have add : returnAddress image+4#64 = entryAddress image+12#64 := by
    simp only [returnAddress, BitVec.add_assoc, BitVec.reduceAdd]
  have stepping : (try_step step true).run before = .ok false last := by
    have h := exit_addi_step before (returnAddress image) step (imageRegions image sp)
      (imageRegion image) bm bc bp ar
      (by simpa only [exitWord, Nat.mul_zero, Nat.add_zero, if_pos rfl, returnAddress] using
        exit_word_bytes accepted s saved1 saved2 result ⟨0,by decide⟩)
      (suffix_permissions accepted 8 (Or.inl rfl)).1
      (suffix_permissions accepted 8 (Or.inl rfl)).2
    rw [control_self before (returnAddress image) pc.1 pc.2.1 pc.2.2, add] at h
    exact h
  have lp : StepProfile last := control_stepProfile _ _ _ (x17_stepProfile _ _ bp)
  have lk : ClockProfile last (c+5#64) (t+5#64) d :=
    control_clockProfile _ _ _ _ _ _ (x17_clockProfile _ _ _ _ _ bk)
  have tick : (tick_clock ()).run last = .ok () final := by
    have deadline : (t+5#64).toNat+1 < d.toNat := by
      rw [timer_add_toNat t d 5 (by omega)]
      omega
    have h := tick_clock_run last (c+5#64) (t+5#64) d lp lk deadline
    simpa only [final, readyState, last, before, returned,
      set_clockState _ _ _ Register.x17 _ (by decide) (by decide), control_clockState,
      clockState_same, BitVec.add_assoc, BitVec.reduceAdd] using h
  have callback := phase_one_callback before last final step bk.done lk.done stepping tick
  have one : (boundedPlatform 1 (1,step)).run before = .ok (0,step) final := by
    simp only [boundedPlatform]
    rw [bind_run_ok _ _ callback]
    rfl
  have twelve := OakSailBoundedAppend.bounded_append 11 1 (entryState s image sp) before final
    (0,step) (1,step) (0,step) prefixRun.2.2 one
  refine ⟨prefixRun.1, prefixRun.2.1, twelve, ?_⟩
  have fm : MemoryConfig final (imageRegions image sp) :=
    clockState_memoryConfig _ _ _ _ (control_memoryConfig _ _ _ _ (x17_memoryConfig _ _ _ rm))
  have fp : StepProfile final :=
    clockState_stepProfile _ _ _ (control_stepProfile _ _ _ (x17_stepProfile _ _ rp))
  have fc : ConfigOK final :=
    clockState_config _ _ _ (control_config _ _ _ (x17_config _ _ rc))
  have hpc : final.regs.get? Register.PC = some (entryAddress image+12#64) := by
    simp [final, readyState, clockState, controlState, setRegister, Std.ExtDHashMap.get?_insert]
  refine ⟨hpc, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, readyState, clockState, controlState, setRegister, Std.ExtDHashMap.get?_insert]
  · simp [final, readyState, clockState, controlState, setRegister, Std.ExtDHashMap.get?_insert]
  · simp [final, readyState, returnedState, finalSteppedState, finalFrameState, frameSavedMemory_regs,
      clockState, controlState, setRegister, Std.ExtDHashMap.get?_insert, result]
  · apply fetch_base_run final (entryAddress image+12#64) (0x00000073#32)
      (imageRegions image sp) (imageRegion image) fm fp.isa hpc ae
      (suffix_permissions accepted 12 (Or.inr rfl)).1
      (suffix_permissions accepted 12 (Or.inr rfl)).2
      (by simpa only [exitWord, Nat.reduceMul, Nat.reduceAdd, if_neg (by decide : ¬(1:Nat)=0)] using
        exit_word_bytes accepted s saved1 saved2 result ⟨1,by decide⟩) (by decide +kernel)
  · exact (congrArg (fun action : SailM instruction => action.run final) decode_exit_ecall).trans
      (decoderChecks_run final (.ECALL ()) fc)

end OakSailExitSource
