import OakSailSteppedFrame
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailPlatformCallback
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
open OakSailBridge.BitwiseDecoded

/-- Exactly the callback supplied to the generated loop's opaque iterator.
Its equality below does not assert an unfolding rule for that iterator. -/
def platformCallback (_ : Unit) (phaseStep : Nat × Nat) : SailM (ForInStep (Nat × Nat)) := do
  if Functions.not (← readReg Register.htif_done) then
    let (phase,step) := phaseStep
    let stepped ← try_step step true
    let step ← if stepped then do
        cycle_count ()
        pure (step+1)
      else pure step
    let phase ← if Functions.not (← readReg Register.htif_done) then do
        let phase := phase+1
        if phase == 2 then do
          tick_clock ()
          pure 0
        else pure phase
      else pure phase
    pure (.yield (phase,step))
  else pure (.done phaseStep)

private theorem bind_if {α β : Type} (p : Prop) [Decidable p]
    (a b : SailM α) (f : α → SailM β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl

private theorem map_if {α β : Type} (p : Prop) [Decidable p]
    (a b : SailM α) (f : α → β) :
    (f <$> (if p then a else b)) = (if p then f <$> a else f <$> b) := by
  split <;> rfl

/-- Kernel-checked identification of the actual generated callback, retaining
its original opaque iterator and exit-code read. No full-loop execution claim. -/
theorem generated_loop_callback : loop () = (do
    let (_phase,_step) ← forIn Lean.Loop.mk (0,0) platformCallback
    let exitCode ← readReg Register.htif_exit_code
    pure exitCode.toNat : SailM Nat) := by
  simp only [loop, platformCallback, get_config_print_instr, Bool.false_eq_true, if_false, bind_assoc, pure_bind, plat_insns_per_tick, Sail.BitVec.toNatInt]
  congr 1
  congr 1
  funext u pair
  rcases pair with ⟨phase,step⟩
  simp [platformCallback, pure_bind, bind_assoc, bind_if, map_if]

/-- Explicitly bounded iteration of the identified callback. This is not an
execution or termination theorem for Lean.Loop.forIn. -/
def boundedPlatform : Nat → (Nat × Nat) → SailM (Nat × Nat)
  | 0, phaseStep => pure phaseStep
  | count+1, phaseStep => do
      match ← platformCallback () phaseStep with
      | .done final => pure final
      | .yield next => boundedPlatform count next

theorem stopped_callback (s : State) (phase step : Nat)
    (hd : s.regs.get? Register.htif_done = some true) :
    (platformCallback () (phase,step)).run s = .ok (.done (phase,step)) s := by
  unfold platformCallback
  rw [bind_run_ok _ _ (read_register s Register.htif_done true hd)]
  rfl

theorem phase_zero_callback (s t : State) (step : Nat)
    (hd : s.regs.get? Register.htif_done = some false)
    (ht : t.regs.get? Register.htif_done = some false)
    (hs : (try_step step true).run s = .ok false t) :
    (platformCallback () (0,step)).run s = .ok (.yield (1,step)) t := by
  unfold platformCallback
  rw [bind_run_ok _ _ (read_register s Register.htif_done false hd)]
  simp only [Functions.not, Bool.not_false, if_true]
  rw [bind_run_ok _ _ hs]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [bind_run_ok _ _ (read_register t Register.htif_done false ht)]
  rfl

theorem phase_one_callback (s t u : State) (step : Nat)
    (hd : s.regs.get? Register.htif_done = some false)
    (ht : t.regs.get? Register.htif_done = some false)
    (hs : (try_step step true).run s = .ok false t)
    (hc : (tick_clock ()).run t = .ok () u) :
    (platformCallback () (1,step)).run s = .ok (.yield (0,step)) u := by
  unfold platformCallback
  rw [bind_run_ok _ _ (read_register s Register.htif_done false hd)]
  simp only [Functions.not, Bool.not_false, if_true]
  rw [bind_run_ok _ _ hs]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [bind_run_ok _ _ (read_register t Register.htif_done false ht)]
  simp only [Functions.not, Bool.not_false, if_true]
  change (tick_clock () >>= _).run t = _
  rw [bind_run_ok _ _ hc]
  rfl

end OakSailPlatformCallback
