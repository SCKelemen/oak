import OakSailPlatformCallback
import OakSailClockTick
set_option autoImplicit false
noncomputable section
namespace OakSailClockChecks
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailPlatformCallback OakSailClockTick

/-- The alternate valid phase invokes the actual clock, not the phase-zero
transition. The instruction transition is a reusable premise of this control rule. -/
theorem phase_one_actual_tick (s u : State) (step : Nat) (c t d : BitVec 64)
    (hd : s.regs.get? Register.htif_done = some false)
    (hs : (try_step step true).run s = .ok false u)
    (hp : StepProfile u) (hc : ClockProfile u c t d) (hb : t.toNat+1<d.toNat) :
    (platformCallback () (1,step)).run s =
      .ok (.yield (0,step)) (clockState u (c+1#64) (t+1#64)) :=
  phase_one_callback s u _ step hd hc.done hs (tick_clock_run u c t d hp hc hb)

theorem phase_one_not_phase_zero (s u final : State) (step : Nat) (c t d : BitVec 64)
    (hd : s.regs.get? Register.htif_done = some false)
    (hs : (try_step step true).run s = .ok false u)
    (hp : StepProfile u) (hc : ClockProfile u c t d) (hb : t.toNat+1<d.toNat) :
    (platformCallback () (1,step)).run s ≠ .ok (.yield (1,step)) final := by
  rw [phase_one_actual_tick s u step c t d hd hs hp hc hb]
  intro bad
  have value := (EStateM.Result.ok.inj bad).1
  cases value

/-- Four ticks can wrap the cycle counter; no saturation or hidden nowrap premise. -/
theorem four_cycles_modular (c : BitVec 64) :
    (c+4#64).toNat = (c.toNat+4) % 2^64 := by
  rw [_root_.BitVec.toNat_add]
  rfl

theorem four_cycles_wrap : (0xfffffffffffffffe#64+4#64) = (2#64) := by decide +kernel

/-- A concrete clock profile coexists with the original step profile. -/
theorem witness_clock_profile :
    ∃ s : State, StepProfile s ∧ ClockProfile s (0xfffffffffffffffe#64) (0#64) (100#64) ∧
      (0#64).toNat+4 < (100#64).toNat := by
  obtain ⟨s,hp,hc⟩ := clock_profile_nonempty (0xfffffffffffffffe#64) (0#64) (100#64)
  exact ⟨s,hp,hc,by decide⟩

end OakSailClockChecks
