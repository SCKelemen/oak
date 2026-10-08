import OakSailBridge.FetchedInstruction
import OakSailBridge.FramedState
import LeanRV64D.SysControl
import LeanRV64D.Platform

/-! Concrete mapped-register hypotheses for the bounded, active RV64 step.
The primitive results below unfold the unchanged generated Sail definitions;
they do not assume successful interrupt, retirement-counter, or ELP checks. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem enabled_supervisor_run (s : State)
    (hm : s.regs.get? Register.misa = some misaRV64I) :
    (currentlyEnabled .Ext_S).run s = .ok false s := by
  simp [currentlyEnabled, hartSupports, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    hm, Pure.pure, EStateM.pure, misaRV64I, _get_Misa_S,
    Sail.BitVec.extractLsb]

theorem external_interrupts_pending_run (s : State)
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (hs : s.regs.get? Register.sig_meip = some (0#1)) :
    (external_interrupts_pending ()).run s = .ok (0#64) s := by
  have he := enabled_supervisor_run s hm
  simp only [EStateM.run] at he
  simp [external_interrupts_pending, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    hs, he, Pure.pure, EStateM.pure, _update_Minterrupts_SEI,
    _update_Minterrupts_MEI, Mk_Minterrupts, zeros, Sail.BitVec.updateSubrange]
  rfl

theorem read_mip_run (s : State) (pending : BitVec 64)
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (hs : s.regs.get? Register.sig_meip = some (0#1))
    (hp : s.regs.get? Register.mip = some pending) :
    (read_mip .IncludePlatformInterrupts).run s = .ok pending s := by
  have he := external_interrupts_pending_run s hm hs
  simp only [EStateM.run] at he
  simp [read_mip, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    hp, he, Pure.pure, EStateM.pure, Mk_Minterrupts]

/-- All eager reads are accounted for, even though Machine interrupts are
disabled by mstatus. The mapped pending/enabled masks may be arbitrary. -/
theorem getPendingSet_machine_run (s : State) (pending enabled : BitVec 64)
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (hs : s.regs.get? Register.sig_meip = some (0#1))
    (hp : s.regs.get? Register.mip = some pending)
    (he : s.regs.get? Register.mie = some enabled)
    (hst : s.regs.get? Register.mstatus = some (0#64)) :
    (getPendingSet .Machine).run s = .ok none s := by
  have hS := enabled_supervisor_run s hm
  have hip := read_mip_run s pending hm hs hp
  simp only [EStateM.run] at hS hip
  simp [getPendingSet, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    hS, hip, he, hst, Pure.pure, EStateM.pure,
    _get_Mstatus_MIE, _get_Mstatus_SIE, Sail.BitVec.extractLsb]
  rfl

theorem dispatchInterrupt_machine_run (s : State) (pending enabled : BitVec 64)
    (hm : s.regs.get? Register.misa = some misaRV64I)
    (hs : s.regs.get? Register.sig_meip = some (0#1))
    (hp : s.regs.get? Register.mip = some pending)
    (he : s.regs.get? Register.mie = some enabled)
    (hst : s.regs.get? Register.mstatus = some (0#64)) :
    (dispatchInterrupt .Machine).run s = .ok none s := by
  unfold dispatchInterrupt
  rw [bind_run_ok _ _ (getPendingSet_machine_run s pending enabled hm hs hp he hst)]
  rfl

/-- Inhibiting IR does not eliminate the generated eager minstretcfg read. -/
theorem should_inc_minstret_machine_run (s : State) (cfg : BitVec 64)
    (hi : s.regs.get? Register.mcountinhibit = some (4#32))
    (hc : s.regs.get? Register.minstretcfg = some cfg) :
    (should_inc_minstret .Machine).run s = .ok false s := by
  simp [should_inc_minstret, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    hi, hc, Pure.pure, EStateM.pure, _get_Counterin_IR, Sail.BitVec.extractLsb]

theorem is_landing_pad_expected_run (s : State)
    (he : s.regs.get? Register.elp = some (0#1)) :
    (is_landing_pad_expected ()).run s = .ok false s := by
  simp [is_landing_pad_expected, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    he, Pure.pure, EStateM.pure, landing_pad_bits_backwards]

/-- The extra state needed by the generated active step, beyond fetch and
instruction-body premises. All requirements concern concrete register maps. -/
structure StepProfile (s : State) : Prop where
  privilege : s.regs.get? Register.cur_privilege = some Privilege.Machine
  status : s.regs.get? Register.mstatus = some (0#64)
  isa : s.regs.get? Register.misa = some misaRV64I
  pending : s.regs.get? Register.mip = some (0#64)
  enabled : s.regs.get? Register.mie = some (0#64)
  machineExternal : s.regs.get? Register.sig_meip = some (0#1)
  inhibit : s.regs.get? Register.mcountinhibit = some (4#32)
  retirementConfig : s.regs.get? Register.minstretcfg = some (0#64)
  landingPad : s.regs.get? Register.elp = some (0#1)
  active : s.regs.get? Register.hart_state = some (.HART_ACTIVE ())

theorem StepProfile.dispatch (s : State) (h : StepProfile s) :
    (dispatchInterrupt .Machine).run s = .ok none s :=
  dispatchInterrupt_machine_run s 0 0 h.isa h.machineExternal h.pending h.enabled h.status

theorem StepProfile.counter (s : State) (h : StepProfile s) :
    (should_inc_minstret .Machine).run s = .ok false s :=
  should_inc_minstret_machine_run s 0 h.inhibit h.retirementConfig

theorem StepProfile.landing_pad (s : State) (h : StepProfile s) :
    (is_landing_pad_expected ()).run s = .ok false s :=
  is_landing_pad_expected_run s h.landingPad

/-- These are exactly the frame's register writes and the step-driver writes. -/
def StepWriteRegister (r : Register) : Prop :=
  FrameRegister r ∨ r = .PC ∨ r = .minstret_increment

theorem stepProfile_set (s : State) (r : Register) (v : RegisterType r)
    (hr : StepWriteRegister r) (h : StepProfile s) :
    StepProfile (setRegister s r v) := by
  rcases h with ⟨hp, hs, hi, hpend, he, hm, hc, hcfg, hl, ha⟩
  rcases hr with (hr | hr | hr | hr | hr) | hr | hr <;> subst r <;>
    constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem stepProfile_store64 (s : State) (addr : Nat) (value : BitVec 64)
    (h : StepProfile s) : StepProfile (store64 s addr value) := by
  rcases h with ⟨hp, hs, hi, hpend, he, hm, hc, hcfg, hl, ha⟩
  constructor <;> simpa only [store64_regs] using ‹_›

/-- A concrete profile constructor leaves memory and all other state intact. -/
def stepProfileState (s : State) : State :=
  setRegister
    (setRegister
      (setRegister
        (setRegister
          (setRegister
            (setRegister
              (setRegister
                (setRegister
                  (setRegister
                    (setRegister s .cur_privilege .Machine)
                    .mstatus (0#64))
                  .misa misaRV64I)
                .mip (0#64))
              .mie (0#64))
            .sig_meip (0#1))
          .mcountinhibit (4#32))
        .minstretcfg (0#64))
      .elp (0#1))
    .hart_state (.HART_ACTIVE ())

theorem stepProfileState_profile (s : State) : StepProfile (stepProfileState s) := by
  constructor <;> simp [stepProfileState, setRegister, Std.ExtDHashMap.get?_insert]

theorem stepProfileState_mem (s : State) : (stepProfileState s).mem = s.mem := rfl

theorem stepProfile_nonempty : ∃ s : State, StepProfile s :=
  ⟨stepProfileState default, stepProfileState_profile default⟩

/-- Negative control: clearing inhibition changes the actual primitive result. -/
theorem should_inc_minstret_uninhibited_run (s : State)
    (hi : s.regs.get? Register.mcountinhibit = some (0#32))
    (hc : s.regs.get? Register.minstretcfg = some (0#64)) :
    (should_inc_minstret .Machine).run s = .ok true s := by
  simp [should_inc_minstret, EStateM.run, Bind.bind, EStateM.bind,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    hi, hc, Pure.pure, EStateM.pure, _get_Counterin_IR, counter_priv_filter_bit,
    _get_CountSmcntrpmf_MINH, Sail.BitVec.extractLsb]

theorem stepProfileState_uninhibited (s : State) :
    (should_inc_minstret .Machine).run
      (setRegister (stepProfileState s) .mcountinhibit (0#32)) =
      .ok true (setRegister (stepProfileState s) .mcountinhibit (0#32)) := by
  apply should_inc_minstret_uninhibited_run
  · simp [setRegister, Std.ExtDHashMap.get?_insert]
  · simpa [setRegister, Std.ExtDHashMap.get?_insert] using
      (stepProfileState_profile s).retirementConfig

theorem stepProfileState_uninhibited_not_profile (s : State) :
    ¬ StepProfile (setRegister (stepProfileState s) .mcountinhibit (0#32)) := by
  intro h
  have hi := h.inhibit
  simp [setRegister, Std.ExtDHashMap.get?_insert] at hi

end OakSailBridge.BitwiseDecoded
