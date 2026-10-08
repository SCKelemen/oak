import OakSailPlatformCallback
import OakSailClockedState

/-! Nine actual generated platform callbacks, with four actual clock ticks.
The bounded iterator below is separate from the generated opaque full loop. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailClockedPrefix
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailFetchedFrame OakSailSteppedState OakSailSteppedFetch OakSailSteppedFrame
open OakSailClockTick OakSailClockedState OakSailPlatformCallback
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

/-- Compose a finite sequence of the actual generated loop callback. -/
theorem bounded_of_transitions (count : Nat) (states : Nat → State)
    (cursors : Nat → Nat × Nat)
    (h : ∀ k, k < count → (platformCallback () (cursors k)).run (states k) =
      .ok (.yield (cursors (k+1))) (states (k+1))) :
    (boundedPlatform count (cursors 0)).run (states 0) =
      .ok (cursors count) (states count) := by
  induction count generalizing states cursors with
  | zero => rfl
  | succ count ih =>
      have first := h 0 (by omega)
      simp only [boundedPlatform]
      rw [bind_run_ok _ _ first]
      exact ih (fun k => states (k+1)) (fun k => cursors (k+1)) (by
        intro k hk
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h (k+1) (by omega))

/-- The timer remains a natural-number increment throughout this prefix. -/
theorem timer_add_toNat (t d : BitVec 64) (n : Nat)
    (h : t.toNat + n < d.toNat) :
    (t + BitVec.ofNat 64 n).toNat = t.toNat + n := by
  have hd := d.isLt
  have hn : n < 2^64 := by omega
  rw [_root_.BitVec.toNat_add, _root_.BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]

/-- Exact bounded execution of the generated callback: nine actual fetched
instructions, four actual clock ticks, and a final half-tick phase of one.
The actual waiting flag is false throughout, so the callback's step cursor
stays fixed and cycle_count is never called. This does not unfold Lean.Loop. -/
theorem clocked_nine_steps (op : Op) (s : State)
    (sp saved1 saved2 left right ra code : BitVec 64) (step : Nat)
    (c t d : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (codeRegion : Fin 9 → PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat + 4 < d.toNat)
    (ha : OakSailFramedComposition.FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra) (halign : ReturnAligned ra)
    (hcode : FrameCodeAt s code op) (hsep : CodeStackDisjoint code (sp-96#64))
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) :
    (boundedPlatform 9 (0,step)).run (controlState s code code) =
      .ok (1,step)
        (clockState (finalSteppedState s sp saved1 saved2
          (Oak.RiscVBitwiseFunction.eval64 op left right) ra) (c + 4#64) (t + 4#64)) := by
  let cores := fun n => controlState (bodyStage s sp saved1 saved2 left right ra op n)
    (progressionPC code ra n) (progressionPC code ra n)
  let states := fun n => clockState (cores n)
    (c + BitVec.ofNat 64 (n/2)) (t + BitVec.ofNat 64 (n/2))
  have coreProfile : ∀ n : Fin 10, StepProfile (cores n.val) := by
    intro n
    exact control_stepProfile _ _ _
      (body_stepProfile s sp saved1 saved2 left right ra op hp n)
  have coreClock : ∀ n : Fin 10, ClockProfile (cores n.val) c t d := by
    intro n
    exact control_clockProfile _ c t d _ _
      (body_clockProfile s sp saved1 saved2 left right ra c t d op hclock n)
  have coreStep : ∀ (k : Nat), k < 9 → ∀ (newC newT : BitVec 64),
      (try_step step true).run (clockState (cores k) newC newT) =
        .ok false (clockState (cores (k+1)) newC newT) := by
    intro k hk newC newT
    let i : Fin 9 := ⟨k,hk⟩
    let base := clockState s newC newT
    have bm : MemoryConfig base regions := clockState_memoryConfig s newC newT regions hc
    have bc : ConfigOK base := clockState_config s newC newT hcfg
    have bp : StepProfile base := clockState_stepProfile s newC newT hp
    have bcode : FrameCodeAt base code op := clockState_code s newC newT code op hcode
    have bbody := OakSailSteppedBody.frame_body_step op base sp saved1 saved2 left right ra code
      regions first second bm bc ha
      (by simpa only [base, clockState_lookup_other _ _ _ Register.x2 (by decide) (by decide)] using hsp)
      (by simpa only [base, clockState_lookup_other _ _ _ Register.x9 (by decide) (by decide)] using h1)
      (by simpa only [base, clockState_lookup_other _ _ _ Register.x18 (by decide) (by decide)] using h2)
      (by simpa only [base, clockState_lookup_other _ _ _ Register.x10 (by decide) (by decide)] using hl)
      (by simpa only [base, clockState_lookup_other _ _ _ Register.x11 (by decide) (by decide)] using hr)
      (by simpa only [base, clockState_lookup_other _ _ _ Register.x1 (by decide) (by decide)] using hra)
      halign i
    have done := frame_word_step (bodyStage base sp saved1 saved2 left right ra op k)
      (bodyStage base sp saved1 saved2 left right ra op (k+1)) code
      (progressionPC code ra (k+1)) op i step true regions (codeRegion i)
      (body_memoryConfig base sp saved1 saved2 left right ra op regions bm ⟨k,by omega⟩)
      (body_config base sp saved1 saved2 left right ra op bc ⟨k,by omega⟩)
      (body_stepProfile base sp saved1 saved2 left right ra op bp ⟨k,by omega⟩)
      (body_stepProfile base sp saved1 saved2 left right ra op bp ⟨k+1,by omega⟩)
      (body_code base sp saved1 saved2 left right ra code op bcode hsep ⟨k,by omega⟩)
      (hexec i) (hlow i) (by rw [next_codePC]; exact bbody)
    have b0 := body_clockState s sp saved1 saved2 left right ra newC newT op ⟨k,by omega⟩
    have b1 := body_clockState s sp saved1 saved2 left right ra newC newT op ⟨k+1,by omega⟩
    simpa only [base, b0, b1, control_clockState, cores, progressionPC,
      if_pos hk, codePC, i] using done
  have active : ∀ (k : Nat), k < 10 → ∀ (newC newT : BitVec 64),
      (clockState (cores k) newC newT).regs.get? Register.htif_done = some false := by
    intro k hk newC newT
    exact (clockState_profile (cores k) c t d newC newT (coreClock ⟨k,hk⟩)).done
  have tick : ∀ (k n : Nat), k < 10 → n < 4 →
      (tick_clock ()).run (clockState (cores k)
        (c + BitVec.ofNat 64 n) (t + BitVec.ofNat 64 n)) =
      .ok () (clockState (cores k)
        (c + BitVec.ofNat 64 (n+1)) (t + BitVec.ofNat 64 (n+1))) := by
    intro k n hk hn
    have hbound : (t + BitVec.ofNat 64 n).toNat + 1 < d.toNat := by
      rw [timer_add_toNat t d n (by omega)]
      omega
    have run := tick_clock_run (clockState (cores k)
      (c + BitVec.ofNat 64 n) (t + BitVec.ofNat 64 n))
      (c + BitVec.ofNat 64 n) (t + BitVec.ofNat 64 n) d
      (clockState_stepProfile _ _ _ (coreProfile ⟨k,hk⟩))
      (clockState_profile _ c t d _ _ (coreClock ⟨k,hk⟩)) hbound
    simpa only [clockState_same, _root_.BitVec.ofNat_add, _root_.BitVec.add_assoc] using run
  have transitions : ∀ k, k < 9 →
      (platformCallback () (k%2,step)).run (states k) =
        .ok (.yield ((k+1)%2,step)) (states (k+1)) := by
    intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
        k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases cases with hk|hk|hk|hk|hk|hk|hk|hk|hk <;> subst k
    all_goals simp only [states, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd]
    all_goals first
      | exact phase_zero_callback _ _ step (active _ (by omega) _ _) (active _ (by omega) _ _)
          (coreStep _ (by omega) _ _)
      | exact phase_one_callback _ _ _ step (active _ (by omega) _ _) (active _ (by omega) _ _)
          (coreStep _ (by omega) _ _) (tick _ _ (by omega) (by omega))
  have run := bounded_of_transitions 9 states (fun k => (k%2,step)) transitions
  have final := stagedFrameState_eq_finalFrameState s (sp-96#64) sp saved1 saved2 right
    (Oak.RiscVBitwiseFunction.eval64 op left right) (Sail.BitVec.update ra 0 0#1) hsp h1 h2
  have bodyFinal : bodyStage s sp saved1 saved2 left right ra op 9 =
      finalFrameState s (sp-96#64) saved1 saved2
        (Oak.RiscVBitwiseFunction.eval64 op left right) (Sail.BitVec.update ra 0 0#1) := by
    simpa only [bodyStage, stagedFrameState] using final
  have initial : states 0 = controlState s code code := by
    simp only [states, cores, bodyStage, progressionPC, Nat.zero_lt_succ, if_true,
      Nat.mul_zero, Nat.zero_div, _root_.BitVec.add_zero]
    rw [← control_clockState, clockState_self s c t hclock.cycle hclock.time]
  rw [initial] at run
  simpa only [states, cores, Nat.reduceMod, Nat.reduceDiv, bodyFinal,
    progressionPC, Nat.lt_irrefl, if_false, finalSteppedState] using run

end OakSailClockedPrefix
