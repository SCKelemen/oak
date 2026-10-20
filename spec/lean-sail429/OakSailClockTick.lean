import OakSailSteppedFrame
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailClockTick
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailFetchedFrame OakSailSteppedState OakSailSteppedFrame
attribute [local irreducible] store64

/-- The extra mapped registers eagerly read by the actual platform clock and loop. -/
structure ClockProfile (s : State) (c t d : BitVec 64) : Prop where
  cycleConfig : s.regs.get? Register.mcyclecfg = some (0#64)
  cycle : s.regs.get? Register.mcycle = some c
  time : s.regs.get? Register.mtime = some t
  deadline : s.regs.get? Register.mtimecmp = some d
  env : s.regs.get? Register.menvcfg = some (0#64)
  done : s.regs.get? Register.htif_done = some false

/-- Description of the resulting state, not a replacement clock implementation. -/
def clockState (s : State) (c t : BitVec 64) : State :=
  setRegister (setRegister s .mcycle c) .mtime t

theorem should_inc_mcycle_machine_run (s : State)
    (hi : s.regs.get? Register.mcountinhibit = some (4#32))
    (hc : s.regs.get? Register.mcyclecfg = some (0#64)) :
    (should_inc_mcycle .Machine).run s = .ok true s := by
  simp [should_inc_mcycle, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    hi, hc, Pure.pure, EStateM.pure, _get_Counterin_CY, counter_priv_filter_bit,
    _get_CountSmcntrpmf_MINH, Sail.BitVec.extractLsb]

theorem enabled_sstc_run (s : State) :
    (currentlyEnabled .Ext_Sstc).run s = .ok true s := by
  simp [currentlyEnabled, hartSupports, EStateM.run, Pure.pure, EStateM.pure]

theorem timer_below_compare (t d : BitVec 64) (h : t.toNat < d.toNat) :
    zopz0zIzJ_u d t = false := by
  simp [zopz0zIzJ_u, Sail.BitVec.toNatInt]
  omega

theorem timer_below_run (s : State) (t d : BitVec 64)
    (hp : s.regs.get? Register.mip = some (0#64))
    (ht : s.regs.get? Register.mtime = some t)
    (hd : s.regs.get? Register.mtimecmp = some d)
    (he : s.regs.get? Register.menvcfg = some (0#64))
    (h : t.toNat < d.toNat) :
    (clint_dispatch false).run s = .ok () s := by
  have hcmp := timer_below_compare t d h
  have hsstc := enabled_sstc_run s
  have hw := setRegister_self s Register.mip (0#64) hp
  have hmap : s.regs.insert Register.mip (0#64) = s.regs := congrArg (fun q => q.regs) hw
  have hzero : Sail.BitVec.updateSubrange' (0#64) 7 1 (0#1) = (0#64) := by decide +kernel
  simp only [EStateM.run] at hsstc
  simp [clint_dispatch, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, PreSail.writeReg, MonadState.get, getThe, MonadStateOf.get,
    EStateM.get, EStateM.set, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Pure.pure, EStateM.pure, hp, ht, hd, he, hcmp, bool_to_bit, bool_bit_forwards,
    Sail.BitVec.updateSubrange, _get_MEnvcfg_STCE, Sail.BitVec.extractLsb,
    hsstc, get_config_print_clint, hmap, hzero]

/-- At or past the deadline the actual dispatcher writes MTIP and takes the CSR callback. -/
theorem timer_reached_run (s : State) (t d : BitVec 64)
    (hp : s.regs.get? Register.mip = some (0#64))
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (hs : s.regs.get? Register.sig_meip = some (0#1))
    (ht : s.regs.get? Register.mtime = some t)
    (hd : s.regs.get? Register.mtimecmp = some d)
    (he : s.regs.get? Register.menvcfg = some (0#64))
    (h : d.toNat ≤ t.toNat) :
    (clint_dispatch false).run s = .ok () (setRegister s Register.mip (128#64)) := by
  have hcmp : zopz0zIzJ_u d t = true := by
    simp [zopz0zIzJ_u, Sail.BitVec.toNatInt]
    omega
  have hsstc := enabled_sstc_run (setRegister s Register.mip (128#64))
  have hip := read_mip_run (setRegister s Register.mip (128#64)) (128#64)
    (by simpa [setRegister, Std.ExtDHashMap.get?_insert] using hm)
    (by simpa [setRegister, Std.ExtDHashMap.get?_insert] using hs)
    (by simp [setRegister, Std.ExtDHashMap.get?_insert])
  have hcallback : (csr_name_write_callback "mip" (128#64)).run
      (setRegister s Register.mip (128#64)) =
      .ok () (setRegister s Register.mip (128#64)) := by rfl
  have hbit : Sail.BitVec.updateSubrange' (0#64) 7 1 (1#1) = (128#64) := by decide +kernel
  simp only [EStateM.run, setRegister] at hsstc hip hcallback
  simp [clint_dispatch, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, PreSail.writeReg, MonadState.get, getThe, MonadStateOf.get,
    EStateM.get, EStateM.set, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Pure.pure, EStateM.pure, hp, ht, hd, he, hcmp, bool_to_bit, bool_bit_forwards,
    Sail.BitVec.updateSubrange, _get_MEnvcfg_STCE, Sail.BitVec.extractLsb,
    hsstc, get_config_print_clint, hbit, setRegister, Std.ExtDHashMap.get?_insert,
    hip, hcallback]

/-- The timer bound excludes wraparound; the cycle counter deliberately remains modular. -/
theorem timer_add_one_toNat (t d : BitVec 64) (h : t.toNat + 1 < d.toNat) :
    (t + 1#64).toNat = t.toNat + 1 := by
  have hd := d.isLt
  rw [_root_.BitVec.toNat_add]
  simp only [_root_.BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

theorem tick_clock_run (s : State) (c t d : BitVec 64)
    (hp : StepProfile s) (hc : ClockProfile s c t d)
    (hbound : t.toNat + 1 < d.toNat) :
    (tick_clock ()).run s = .ok () (clockState s (c + 1#64) (t + 1#64)) := by
  have htime : (t + 1#64).toNat < d.toNat := by
    rw [timer_add_one_toNat t d hbound]
    exact hbound
  have hinc := should_inc_mcycle_machine_run s hp.inhibit hc.cycleConfig
  unfold tick_clock
  rw [bind_run_ok _ _ (read_register s Register.cur_privilege .Machine hp.privilege)]
  rw [bind_run_ok _ _ hinc]
  simp only [Bool.true_eq, ↓reduceIte]
  rw [bind_run_ok _ _ (read_register s Register.mcycle c hc.cycle)]
  rw [bind_run_ok _ _ (write_register s Register.mcycle (Sail.BitVec.addInt c 1))]
  have ht : (setRegister s Register.mcycle (Sail.BitVec.addInt c 1)).regs.get? Register.mtime = some t := by
    simpa [setRegister, Std.ExtDHashMap.get?_insert] using hc.time
  rw [bind_run_ok _ _ (read_register _ Register.mtime t ht)]
  rw [bind_run_ok _ _ (write_register _ Register.mtime (Sail.BitVec.addInt t 1))]
  change (clint_dispatch false).run (clockState s (c + 1#64) (t + 1#64)) = _
  apply timer_below_run _ (t + 1#64) d
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hp.pending
  · simp [clockState, setRegister, Std.ExtDHashMap.get?_insert]
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hc.deadline
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hc.env
  · exact htime


/-- At the exact next-tick deadline the generated clock sets MTIP, so the
below-deadline state equality cannot be extended to a non-strict bound. -/
theorem tick_clock_at_deadline (s : State) (c t d : BitVec 64)
    (hp : StepProfile s) (hc : ClockProfile s c t d)
    (hbound : t.toNat + 1 = d.toNat) :
    (tick_clock ()).run s =
      .ok () (setRegister (clockState s (c + 1#64) (t + 1#64)) Register.mip (128#64)) := by
  have htime : (t + 1#64).toNat = d.toNat := by
    rw [_root_.BitVec.toNat_add]
    simp only [_root_.BitVec.toNat_ofNat]
    rw [show 1 % 2^64 = 1 by decide, hbound, Nat.mod_eq_of_lt d.isLt]
  have hinc := should_inc_mcycle_machine_run s hp.inhibit hc.cycleConfig
  unfold tick_clock
  rw [bind_run_ok _ _ (read_register s Register.cur_privilege .Machine hp.privilege)]
  rw [bind_run_ok _ _ hinc]
  simp only [Bool.true_eq, ↓reduceIte]
  rw [bind_run_ok _ _ (read_register s Register.mcycle c hc.cycle)]
  rw [bind_run_ok _ _ (write_register s Register.mcycle (Sail.BitVec.addInt c 1))]
  have ht : (setRegister s Register.mcycle (Sail.BitVec.addInt c 1)).regs.get? Register.mtime = some t := by
    simpa [setRegister, Std.ExtDHashMap.get?_insert] using hc.time
  rw [bind_run_ok _ _ (read_register _ Register.mtime t ht)]
  rw [bind_run_ok _ _ (write_register _ Register.mtime (Sail.BitVec.addInt t 1))]
  change (clint_dispatch false).run (clockState s (c + 1#64) (t + 1#64)) = _
  apply timer_reached_run _ (t + 1#64) d
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hp.pending
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hp.isa
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hp.machineExternal
  · simp [clockState, setRegister, Std.ExtDHashMap.get?_insert]
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hc.deadline
  · simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using hc.env
  · omega

theorem clockState_stepProfile (s : State) (c t : BitVec 64) (h : StepProfile s) :
    StepProfile (clockState s c t) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  constructor <;> simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem clockState_profile (s : State) (c t d newC newT : BitVec 64)
    (h : ClockProfile s c t d) : ClockProfile (clockState s newC newT) newC newT d := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> simp_all [clockState, setRegister, Std.ExtDHashMap.get?_insert]

theorem ClockProfile.clockState (s : State) (c t d newC newT : BitVec 64)
    (h : ClockProfile s c t d) : ClockProfile (OakSailClockTick.clockState s newC newT) newC newT d :=
  clockState_profile s c t d newC newT h

theorem clockState_lookup_other (s : State) (c t : BitVec 64) (r : Register)
    (hc : Register.mcycle ≠ r) (ht : Register.mtime ≠ r) :
    (clockState s c t).regs.get? r = s.regs.get? r := by
  unfold clockState
  rw [lookup_set_other _ _ _ _ ht, lookup_set_other _ _ _ _ hc]

theorem clockState_self (s : State) (c t : BitVec 64)
    (hc : s.regs.get? Register.mcycle = some c)
    (ht : s.regs.get? Register.mtime = some t) : clockState s c t = s := by
  unfold clockState
  rw [setRegister_self s Register.mcycle c hc, setRegister_self s Register.mtime t ht]

theorem clockState_nonregister_state (s : State) (c t : BitVec 64) :
    (clockState s c t).mem = s.mem ∧
    (clockState s c t).cycleCount = s.cycleCount ∧
    (clockState s c t).sailOutput = s.sailOutput ∧
    (clockState s c t).choiceState = s.choiceState ∧
    (clockState s c t).tags = s.tags := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem clockState_same (s : State) (c t newC newT : BitVec 64) :
    clockState (clockState s c t) newC newT = clockState s newC newT := by
  unfold clockState
  rw [setRegister_comm (setRegister s Register.mcycle c) Register.mtime Register.mcycle
    t newC (by decide), setRegister_same, setRegister_same]

theorem clockState_memoryConfig (s : State) (c t : BitVec 64) (regions : List PMA_Region)
    (h : MemoryConfig s regions) : MemoryConfig (clockState s c t) regions := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  constructor <;> simpa [clockState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem clockState_config (s : State) (c t : BitVec 64) (h : ConfigOK s) :
    ConfigOK (clockState s c t) := by
  simpa [ConfigOK, clockState, setRegister, Std.ExtDHashMap.get?_insert] using h

theorem clockState_code (s : State) (c t code : BitVec 64) (op : Oak.BitwiseFunction.Op)
    (h : FrameCodeAt s code op) : FrameCodeAt (clockState s c t) code op := h

theorem clockProfile_set (s : State) (c t d : BitVec 64)
    (r : Register) (v : RegisterType r) (hr : StepWriteRegister r) (h : ClockProfile s c t d) :
    ClockProfile (setRegister s r v) c t d := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  rcases hr with (hr | hr | hr | hr | hr) | hr | hr <;> subst r <;>
    constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem clockProfile_store64 (s : State) (c t d : BitVec 64) (addr : Nat)
    (value : BitVec 64) (h : ClockProfile s c t d) :
    ClockProfile (store64 s addr value) c t d := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> simpa only [store64_regs] using ‹_›

theorem control_clockProfile (s : State) (c t d pc next : BitVec 64)
    (h : ClockProfile s c t d) : ClockProfile (controlState s pc next) c t d := by
  unfold controlState
  repeat first
    | apply clockProfile_set _ _ _ _ _ _ (by simp [StepWriteRegister, FrameRegister])
    | exact h

theorem body_clockProfile (s : State) (sp saved1 saved2 left right ra c t d : BitVec 64)
    (op : Oak.BitwiseFunction.Op) (h : ClockProfile s c t d) (n : Fin 10) :
    ClockProfile (bodyStage s sp saved1 saved2 left right ra op n.val) c t d := by
  have hn := n.isLt
  have cases : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨
      n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 := by omega
  rcases cases with hn|hn|hn|hn|hn|hn|hn|hn|hn|hn <;> simp only [hn, bodyStage]
  all_goals repeat first
    | apply clockProfile_store64
    | apply clockProfile_set _ _ _ _ _ _ (by simp [StepWriteRegister, FrameRegister])
    | exact h

/-- A constructive clock profile that leaves memory and all unrelated registers intact. -/
def clockProfileState (s : State) (c t d : BitVec 64) : State :=
  setRegister (setRegister (setRegister (setRegister
    (clockState s c t) .mcyclecfg (0#64)) .mtimecmp d) .menvcfg (0#64)) .htif_done false

theorem clockProfileState_profile (s : State) (c t d : BitVec 64) :
    ClockProfile (clockProfileState s c t d) c t d := by
  constructor <;> simp [clockProfileState, clockState, setRegister, Std.ExtDHashMap.get?_insert]

theorem clockProfileState_stepProfile (s : State) (c t d : BitVec 64) (h : StepProfile s) :
    StepProfile (clockProfileState s c t d) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  constructor <;> simpa [clockProfileState, clockState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem clockProfileState_code (s : State) (c t d code : BitVec 64)
    (op : Oak.BitwiseFunction.Op) (h : FrameCodeAt s code op) :
    FrameCodeAt (clockProfileState s c t d) code op := h

theorem clockProfileState_memoryConfig (s : State) (c t d : BitVec 64) (regions : List PMA_Region)
    (h : MemoryConfig s regions) : MemoryConfig (clockProfileState s c t d) regions := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  constructor <;> simpa [clockProfileState, clockState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem clockProfileState_config (s : State) (c t d : BitVec 64) (h : ConfigOK s) :
    ConfigOK (clockProfileState s c t d) := by
  simpa [ConfigOK, clockProfileState, clockState, setRegister, Std.ExtDHashMap.get?_insert] using h

theorem clockProfileState_mem (s : State) (c t d : BitVec 64) :
    (clockProfileState s c t d).mem = s.mem := rfl

theorem clockProfileState_register_other (s : State) (c t d : BitVec 64) (r : Register)
    (hc : Register.mcycle ≠ r) (ht : Register.mtime ≠ r)
    (hcfg : Register.mcyclecfg ≠ r) (hd : Register.mtimecmp ≠ r)
    (he : Register.menvcfg ≠ r) (hh : Register.htif_done ≠ r) :
    (clockProfileState s c t d).regs.get? r = s.regs.get? r := by
  unfold clockProfileState clockState
  rw [lookup_set_other _ _ _ _ hh, lookup_set_other _ _ _ _ he,
    lookup_set_other _ _ _ _ hd, lookup_set_other _ _ _ _ hcfg,
    lookup_set_other _ _ _ _ ht, lookup_set_other _ _ _ _ hc]

theorem clock_profile_nonempty (c t d : BitVec 64) :
    ∃ s : State, StepProfile s ∧ ClockProfile s c t d :=
  ⟨clockProfileState (stepProfileState default) c t d,
    clockProfileState_stepProfile _ c t d (stepProfileState_profile default),
    clockProfileState_profile _ c t d⟩

theorem cycle_increment_modular (c : BitVec 64) :
    (c + 1#64).toNat = (c.toNat + 1) % 2^64 := by
  rw [_root_.BitVec.toNat_add]
  rfl

/-- Negative control for the unchanged timer comparison at the exact deadline. -/
theorem timer_at_deadline (t d : BitVec 64) (h : t.toNat + 1 = d.toNat) :
    bool_to_bit (zopz0zIzJ_u d (t + 1#64)) = (1#1) := by
  have hd := d.isLt
  have ht : (t + 1#64).toNat = d.toNat := by
    rw [_root_.BitVec.toNat_add]
    simp only [_root_.BitVec.toNat_ofNat]
    rw [show 1 % 2^64 = 1 by decide, h, Nat.mod_eq_of_lt hd]
  simp [zopz0zIzJ_u, Sail.BitVec.toNatInt, ht, bool_to_bit, bool_bit_forwards]


theorem deadline_state_mtip (s : State) (c t : BitVec 64) :
    _get_Minterrupts_MTI
      (match (setRegister (clockState s c t) Register.mip (128#64)).regs.get? Register.mip with
       | some value => value
       | none => 0#64) = (1#1) := by
  simp [setRegister, Std.ExtDHashMap.get?_insert, _get_Minterrupts_MTI, Sail.BitVec.extractLsb]

theorem tick_clock_at_deadline_not_below (s : State) (c t d : BitVec 64)
    (hp : StepProfile s) (hc : ClockProfile s c t d)
    (hbound : t.toNat + 1 = d.toNat) :
    (tick_clock ()).run s ≠ .ok () (clockState s (c + 1#64) (t + 1#64)) := by
  rw [tick_clock_at_deadline s c t d hp hc hbound]
  intro h
  have he : setRegister (clockState s (c + 1#64) (t + 1#64)) Register.mip (128#64) =
      clockState s (c + 1#64) (t + 1#64) := (EStateM.Result.ok.inj h).2
  have hr := congrArg (fun q => q.regs.get? Register.mip) he
  simp [clockState, setRegister, Std.ExtDHashMap.get?_insert, hp.pending] at hr

theorem cycle_increment_wraps : (0xffffffffffffffff#64 + 1#64) = (0#64) := by decide +kernel

end OakSailClockTick
