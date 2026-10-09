import OakSailImageSource

/-! Exact generated AUIPC/JALR startup call bodies. This is a bounded entry
prefix, not reset, the post-return syscall, or an opaque full-loop execution. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailEntryInstructions
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailFetchedFrame OakSailSteppedState OakSailSteppedFetch OakSailSteppedFrame
open OakSailClockTick OakSailClockedState OakSailPlatformCallback

def startupBytes : Oak.MinimalELF.Bytes := [0x97,0,0,0,0xe7,0x80,0,1]

theorem decode_start_auipc : encdec_backwards 0x00000097 =
    decoderChecks (.UTYPE (0, .Regidx 1, .AUIPC)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_uop_backwards, encdec_uop_backwards_matches, Sail.BitVec.extractLsb,
    Functions.base_E_enabled, Functions.regidx_bit_width, Functions.not]

theorem decode_start_call : encdec_backwards 0x010080e7 =
    decoderChecks (.JALR (16, .Regidx 1, .Regidx 1)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_uop_backwards_matches, Sail.BitVec.extractLsb, Functions.base_E_enabled,
    Functions.regidx_bit_width, Functions.not]

theorem write_x1 (v : BitVec 64) : wX_bits (.Regidx 1) v = writeReg Register.x1 v := by rfl

theorem execute_start_auipc_run (s : State) (pc : BitVec 64)
    (hpc : s.regs.get? Register.PC = some pc) :
    (execute_UTYPE 0 (.Regidx 1) .AUIPC).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x1 pc) := by
  simp only [execute_UTYPE, get_arch_pc, sign_extend, Sail.BitVec.signExtend,
    write_x1, pure_bind, bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.PC pc hpc)]
  change ((writeReg Register.x1 (pc + 0#64)) >>= fun _ => pure RETIRE_SUCCESS).run s = _
  rw [_root_.BitVec.add_zero]
  rfl

/-- JALR reads the old x1 before writing the sequential link address to x1. -/
theorem execute_start_call_run (s : State) (base next : BitVec 64)
    (hc : ConfigOK s) (hra : s.regs.get? Register.x1 = some base)
    (hn : s.regs.get? Register.nextPC = some next)
    (ha : ReturnAligned (base+16#64)) :
    (execute_JALR 16 (.Regidx 1) (.Regidx 1)).run s =
      .ok RETIRE_SUCCESS
        (setRegister (setRegister s Register.nextPC (Sail.BitVec.update (base+16#64) 0 0#1))
          Register.x1 next) := by
  unfold execute_JALR
  rw [bind_run_ok _ _ (update_elp_run s hc)]
  change ((readReg Register.nextPC) >>= _).run s = _
  rw [bind_run_ok _ _ (read_register s Register.nextPC next hn)]
  simp only [read_x1, sign_extend, Sail.BitVec.signExtend]
  rw [bind_run_ok _ _ (read_register s Register.x1 base hra)]
  simp only [pure_bind]
  change (jump_to (Sail.BitVec.update (base+16#64) 0 0#1) >>= _).run s = _
  rw [bind_run_ok _ _ (jump_run s _ hc.2.2 ha.1 ha.2)]
  rfl

theorem x1_memoryConfig (s : State) (v : BitVec 64) (regions : List PMA_Region)
    (h : MemoryConfig s regions) : MemoryConfig (setRegister s .x1 v) regions := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem x1_config (s : State) (v : BitVec 64) (h : ConfigOK s) :
    ConfigOK (setRegister s .x1 v) := by
  simpa [ConfigOK, setRegister, Std.ExtDHashMap.get?_insert] using h

theorem x1_stepProfile (s : State) (v : BitVec 64) (h : StepProfile s) :
    StepProfile (setRegister s .x1 v) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem x1_clockProfile (s : State) (v c t d : BitVec 64) (h : ClockProfile s c t d) :
    ClockProfile (setRegister s .x1 v) c t d := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

/-- Generic fetched step, retaining generated fetch/decode/execute/try_step.
Concrete startup lemmas below discharge each intermediate success premise. -/
theorem word_step (s t : State) (pc target : BitVec 64) (word : BitVec 32)
    (inst : instruction) (step : Nat) (regions : List PMA_Region) (region : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (ht : StepProfile t) (halign : pc.toNat % 4 = 0)
    (hbytes : ∀ i : Fin 4, s.mem.get? (pc.toNat + i.val) = some (word.extractLsb' (8 * i.val) 8))
    (hexec : ExecutableRegion regions pc region) (hlow : LowCodeRAM pc)
    (hbase : isRVC (Sail.BitVec.extractLsb word 15 0) = false)
    (hdecode : encdec_backwards word = decoderChecks inst)
    (hbody : (execute inst).run (controlState s pc (pc+4#64)) =
      .ok RETIRE_SUCCESS (controlState t pc target)) :
    (try_step step true).run (controlState s pc pc) =
      .ok false (controlState t target target) := by
  let start := controlState s pc pc
  let finish := controlState t pc target
  have hsp := control_stepProfile s pc pc hp
  have htp := control_stepProfile t pc target ht
  have hf : (fetch ()).run start = .ok (.F_Base word) start := by
    apply fetch_base_run start pc word regions region (control_memoryConfig s pc pc regions hc) hsp.isa
      (by simp [start, controlState, setRegister, Std.ExtDHashMap.get?_insert])
      halign hexec hlow hbytes hbase
  have hd : (ext_decode word).run start = .ok inst start := by
    unfold ext_decode
    rw [hdecode]
    exact decoderChecks_run start inst (control_config s pc pc hcfg)
  have he : (execute inst).run (setRegister start .nextPC (pc+4#64)) =
      .ok RETIRE_SUCCESS finish := by
    simpa only [start, finish, control_next] using hbody
  have active := run_hart_active_success start finish step pc word inst
    hsp.privilege (by simp [start, controlState, setRegister, Std.ExtDHashMap.get?_insert])
    (hsp.dispatch start) hf hd (hsp.landing_pad start) he
  have run := try_step_success start finish step true word target hsp.privilege
    (hsp.counter start) hsp.active (by simpa only [start, control_increment] using active)
    htp.active (by simp [finish, controlState, setRegister, Std.ExtDHashMap.get?_insert])
    (by simp [finish, controlState, setRegister, Std.ExtDHashMap.get?_insert])
  simpa only [start, finish, control_pc] using run

theorem clear_aligned (x : BitVec 64) (h : x.toNat % 4 = 0) : Sail.BitVec.update x 0 0#1 = x := by
  have h0 : x.getLsbD 0 = false := by simp [BitVec.getLsbD, Nat.testBit_zero]; omega
  change ((~~~(1#64)) &&& x ||| 0#64) = x
  rw [BitVec.or_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases hz : i = 0
  · subst i
    simp only [h0, Bool.and_false]
  · simp only [hz, decide_false, Bool.and_false, Bool.not_false, Bool.and_true,
      hi, decide_true, Bool.true_and]

theorem control_x1 (s : State) (pc next v : BitVec 64) :
    setRegister (controlState s pc next) .x1 v = controlState (setRegister s .x1 v) pc next := by
  unfold controlState
  rw [setRegister_comm _ .minstret_increment .x1 false v (by decide),
    setRegister_comm _ .nextPC .x1 next v (by decide),
    setRegister_comm _ .PC .x1 pc v (by decide)]

def EntryCodeAt (s : State) (entry : BitVec 64) : Prop :=
  BytesAt s entry.toNat startupBytes ∧ entry.toNat % 4 = 0 ∧ entry.toNat + 20 ≤ 2^64

def entryWord (i : Fin 2) : BitVec 32 := if i.val = 0 then 0x00000097 else 0x010080e7

def entryInst (i : Fin 2) : instruction :=
  if i.val = 0 then .UTYPE (0,.Regidx 1,.AUIPC) else .JALR (16,.Regidx 1,.Regidx 1)

def entryPC (entry : BitVec 64) (i : Fin 2) : BitVec 64 := entry + BitVec.ofNat 64 (4 * i.val)

theorem entry_add_toNat (entry : BitVec 64) (n : Nat)
    (h : entry.toNat + 20 ≤ 2^64) (hn : n ≤ 16) :
    (entry + BitVec.ofNat 64 n).toNat = entry.toNat + n := by
  have hb : n < 2^64 := by omega
  rw [_root_.BitVec.toNat_add_of_lt]
  · simp only [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  · simp only [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    omega

theorem entry_add_aligned (entry : BitVec 64) (n : Nat)
    (h : entry.toNat + 20 ≤ 2^64) (ha : entry.toNat % 4 = 0) (hn : n ≤ 16)
    (hm : n % 4 = 0) : (entry + BitVec.ofNat 64 n).toNat % 4 = 0 := by
  rw [entry_add_toNat entry n h hn]
  omega

theorem entry_bytes (s : State) (entry : BitVec 64) (h : EntryCodeAt s entry) (i : Fin 2) :
    ∀ j : Fin 4, s.mem.get? ((entryPC entry i).toNat + j.val) =
      some ((entryWord i).extractLsb' (8 * j.val) 8) := by
  intro j
  have hi := i.isLt
  have hj := j.isLt
  have b := h.1 ⟨4 * i.val + j.val, by change 4 * i.val + j.val < 8; omega⟩
  unfold entryPC
  rw [entry_add_toNat entry (4 * i.val) h.2.2 (by omega)]
  have ci : i.val = 0 ∨ i.val = 1 := by omega
  have cj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases ci with hi|hi <;> rcases cj with hj|hj|hj|hj <;>
    simpa [entryWord, startupBytes, hi, hj, Nat.add_assoc] using b

def calledState (s : State) (entry : BitVec 64) : State :=
  controlState (setRegister s .x1 (entry+8#64)) (entry+16#64) (entry+16#64)

/-- The call changes only control bookkeeping and x1, before the actual tick.
In particular SP, both arguments and all callee-saved registers are untouched. -/
theorem called_register_other (s : State) (entry : BitVec 64) (r : Register)
    (hra : Register.x1 ≠ r) (hpc : Register.PC ≠ r)
    (hn : Register.nextPC ≠ r) (hi : Register.minstret_increment ≠ r) :
    (calledState s entry).regs.get? r = s.regs.get? r := by
  unfold calledState controlState
  rw [lookup_set_other _ _ _ _ hi, lookup_set_other _ _ _ _ hn,
    lookup_set_other _ _ _ _ hpc, lookup_set_other _ _ _ _ hra]

theorem called_control (s : State) (entry : BitVec 64) :
    (calledState s entry).regs.get? Register.PC = some (entry+16#64) ∧
    (calledState s entry).regs.get? Register.nextPC = some (entry+16#64) ∧
    (calledState s entry).regs.get? Register.x1 = some (entry+8#64) ∧
    (calledState s entry).regs.get? Register.minstret_increment = some false := by
  simp [calledState, controlState, setRegister, Std.ExtDHashMap.get?_insert]

theorem called_nonregister_state (s : State) (entry : BitVec 64) :
    (calledState s entry).mem = s.mem ∧
    (calledState s entry).cycleCount = s.cycleCount ∧
    (calledState s entry).sailOutput = s.sailOutput ∧
    (calledState s entry).choiceState = s.choiceState ∧
    (calledState s entry).tags = s.tags := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem startup_steps (s : State) (entry : BitVec 64) (step : Nat)
    (regions : List PMA_Region) (region : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (hcode : EntryCodeAt s entry)
    (hexec : ∀ i : Fin 2, ExecutableRegion regions (entryPC entry i) region)
    (hlow : ∀ i : Fin 2, LowCodeRAM (entryPC entry i)) :
    (try_step step true).run (controlState s entry entry) =
      .ok false (controlState (setRegister s .x1 entry) (entry+4#64) (entry+4#64)) ∧
    (try_step step true).run (controlState (setRegister s .x1 entry) (entry+4#64) (entry+4#64)) =
      .ok false (calledState s entry) := by
  constructor
  · apply word_step s (setRegister s .x1 entry) entry (entry+4#64) 0x00000097
      (.UTYPE (0,.Regidx 1,.AUIPC)) step regions region hc hcfg hp (x1_stepProfile s entry hp)
      hcode.2.1
      (by simpa [entryPC, entryWord] using entry_bytes s entry hcode ⟨0,by decide⟩)
      (by simpa [entryPC] using hexec ⟨0,by decide⟩)
      (by simpa [entryPC] using hlow ⟨0,by decide⟩) (by decide +kernel) decode_start_auipc
    have h := execute_start_auipc_run (controlState s entry (entry+4#64)) entry
      (by simp [controlState, setRegister, Std.ExtDHashMap.get?_insert])
    rw [control_x1] at h
    exact h
  · apply word_step (setRegister s .x1 entry) (setRegister s .x1 (entry+8#64))
      (entry+4#64) (entry+16#64) 0x010080e7 (.JALR (16,.Regidx 1,.Regidx 1)) step regions region
      (x1_memoryConfig s entry regions hc) (x1_config s entry hcfg)
      (x1_stepProfile s entry hp) (x1_stepProfile s (entry+8#64) hp)
      (entry_add_aligned entry 4 hcode.2.2 hcode.2.1 (by decide) (by decide))
      (by simpa [entryPC, entryWord, setRegister] using entry_bytes s entry hcode ⟨1,by decide⟩)
      (by simpa [entryPC] using hexec ⟨1,by decide⟩)
      (by simpa [entryPC] using hlow ⟨1,by decide⟩) (by decide +kernel) decode_start_call
    have ha := entry_add_aligned entry 16 hcode.2.2 hcode.2.1 (by decide) (by decide)
    have heq := clear_aligned (entry+16#64) ha
    have halign : ReturnAligned (entry+16#64) := by
      unfold ReturnAligned
      rw [heq]
      exact aligned4_bits _ ha
    have h := execute_start_call_run
      (controlState (setRegister s .x1 entry) (entry+4#64) (entry+4#64+4#64)) entry (entry+8#64)
      (control_config _ _ _ (x1_config s entry hcfg))
      (by simp [controlState, setRegister, Std.ExtDHashMap.get?_insert])
      (by simp [controlState, setRegister, Std.ExtDHashMap.get?_insert, _root_.BitVec.add_assoc]) halign
    rw [heq, control_next, control_x1, setRegister_same] at h
    exact h

theorem startup_callbacks (s : State) (entry : BitVec 64) (step : Nat) (c t d : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat+1 < d.toNat)
    (hcode : EntryCodeAt s entry)
    (hexec : ∀ i : Fin 2, ExecutableRegion regions (entryPC entry i) region)
    (hlow : ∀ i : Fin 2, LowCodeRAM (entryPC entry i)) :
    (boundedPlatform 2 (0,step)).run (controlState s entry entry) =
      .ok (0,step) (clockState (calledState s entry) (c+1#64) (t+1#64)) := by
  have steps := startup_steps s entry step regions region hc hcfg hp hcode hexec hlow
  let mid := controlState (setRegister s .x1 entry) (entry+4#64) (entry+4#64)
  have hstart := control_clockProfile s c t d entry entry hclock
  have hmid : ClockProfile mid c t d := control_clockProfile _ c t d _ _ (x1_clockProfile _ _ _ _ _ hclock)
  have hend : ClockProfile (calledState s entry) c t d :=
    control_clockProfile _ c t d _ _ (x1_clockProfile _ _ _ _ _ hclock)
  have hpend : StepProfile (calledState s entry) := control_stepProfile _ _ _ (x1_stepProfile _ _ hp)
  have first := phase_zero_callback _ mid step hstart.done hmid.done steps.1
  have second := phase_one_callback mid (calledState s entry) _ step hmid.done hend.done steps.2
    (tick_clock_run _ c t d hpend hend hdeadline)
  simp only [boundedPlatform]
  rw [bind_run_ok _ _ first]
  rw [bind_run_ok _ _ second]
  rfl

theorem startup_then (s : State) (entry : BitVec 64) (step : Nat) (c t d : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat+1 < d.toNat)
    (hcode : EntryCodeAt s entry)
    (hexec : ∀ i : Fin 2, ExecutableRegion regions (entryPC entry i) region)
    (hlow : ∀ i : Fin 2, LowCodeRAM (entryPC entry i))
    (n : Nat) (cursor : Nat × Nat) (final : State)
    (rest : (boundedPlatform n (0,step)).run
      (clockState (calledState s entry) (c+1#64) (t+1#64)) = .ok cursor final) :
    (boundedPlatform (n+2) (0,step)).run (controlState s entry entry) = .ok cursor final := by
  have steps := startup_steps s entry step regions region hc hcfg hp hcode hexec hlow
  let mid := controlState (setRegister s .x1 entry) (entry+4#64) (entry+4#64)
  have hstart := control_clockProfile s c t d entry entry hclock
  have hmid : ClockProfile mid c t d := control_clockProfile _ c t d _ _ (x1_clockProfile _ _ _ _ _ hclock)
  have hend : ClockProfile (calledState s entry) c t d :=
    control_clockProfile _ c t d _ _ (x1_clockProfile _ _ _ _ _ hclock)
  have hpend : StepProfile (calledState s entry) := control_stepProfile _ _ _ (x1_stepProfile _ _ hp)
  have first := phase_zero_callback _ mid step hstart.done hmid.done steps.1
  have second := phase_one_callback mid (calledState s entry) _ step hmid.done hend.done steps.2
    (tick_clock_run _ c t d hpend hend hdeadline)
  simp only [boundedPlatform]
  rw [bind_run_ok _ _ first]
  rw [bind_run_ok _ _ second]
  exact rest

end OakSailEntryInstructions
