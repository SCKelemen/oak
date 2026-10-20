import Oak.SessionObligationsProved
/-!
# Refuted universal session obligations

These are counterexamples to the exact named propositions, not admissions
and not a claim that the initialized Oak source programs diverge. `fill`
has a guarded fixed point with a total zero callee and in-range scalars;
`walk` and `drive` expose the absent state-representation premise by using
`n = 2^32`. Do not weaken a compiler gate or claim source correctness by
adding arbitrary assumptions. Revised contracts require justified reachable
states, actual callee behavior, and separate proofs.
-/
open Oak.Loops Oak.Session
namespace Oak.Session.Refutations

def zeroF : Funs := fun _ _ => 0
def fillState : State :=
  ⟨fun i => if i = 0 then 1 else 0, fun a j => if a = 0 ∧ j = 1 then 2 else 0⟩

theorem fill_fixed : loop_fill_3.step zeroF fillState = fillState := by
  apply (show ∀ (a b : State), a.vars = b.vars → a.mem = b.mem → a = b from by intro ⟨a,b⟩ ⟨c,d⟩ h k; cases h; cases k; rfl)
  · funext x
    by_cases hx : x = 0
    · subst x; simp [Loop.step, loop_fill_3, fillState, zeroF, Expr.eval, Op.apply, Ty.wrap, ofBool]
    · have hx' : 0 ≠ x := Ne.symm hx
      simp [hx, hx', Loop.step, loop_fill_3, fillState]
  · funext x j
    simp [Loop.step, loop_fill_3, fillState, Write.apply, Expr.eval, Op.apply, Ty.wrap]

theorem fill_holds : loop_fill_3.holds zeroF fillState := by simp [Loop.holds, loop_fill_3, Expr.eval, Op.apply, fillState, ofBool]

theorem fixed_not_terminates (F : Funs) (L : Loop) (s : State)
    (hs : L.step F s = s) (hg : L.holds F s) : ¬ Terminates F L s := by
  rintro ⟨m, hm⟩
  have bad : ∀ n, ¬ Run F L s n := by
    intro n
    induction n with
    | zero => intro h; cases h with | done h => exact h hg
    | succ n ih =>
      intro h
      cases h with
      | step _ rest => exact ih (hs ▸ rest)
  exact bad m hm

theorem fill_not_terminates : ¬ Terminates zeroF loop_fill_3 fillState :=
  fixed_not_terminates _ _ _ fill_fixed fill_holds


theorem invariant_not_terminates (F : Funs) (L : Loop) (P : State → Prop)
    (hg : ∀ s, P s → L.holds F s)
    (hp : ∀ s, P s → P (L.step F s)) (s : State) (hs : P s) : ¬ Terminates F L s := by
  rintro ⟨m, hm⟩
  have bad : ∀ n s, P s → ¬ Run F L s n := by
    intro n
    induction n with
    | zero => intro s ps h; cases h with | done h => exact h (hg s ps)
    | succ n ih => intro s ps h; cases h with | step _ rest => exact ih _ (hp s ps) rest
  exact bad m s hs hm

def walkState : State := ⟨fun i => if i = 0 then 1 else if i = 3 then 4294967296 else 0, fun _ _ => 0⟩
theorem walk_not_terminates : ¬ Terminates zeroF loop_walk_4 walkState := by
  apply invariant_not_terminates zeroF loop_walk_4 (fun s => s.vars 0 ≠ 0 ∧ s.vars 3 = 4294967296)
  · intro s h; simpa [Loop.holds, loop_walk_4, Expr.eval] using h.1
  · intro s h
    simp [Loop.step, loop_walk_4, Expr.eval, Op.apply, Ty.wrap, ofBool, h.2, two_pow_32]
    omega
  · simp [walkState]

def driveState : State := ⟨fun i => if i = 1 then 4294967296 else 0, fun _ _ => 0⟩
theorem drive_not_terminates : ¬ Terminates zeroF loop_drive_5 driveState := by
  apply invariant_not_terminates zeroF loop_drive_5 (fun s => s.vars 0 < 4294967296 ∧ s.vars 1 = 4294967296)
  · intro s h; simpa [Loop.holds, loop_drive_5, Expr.eval, Op.apply, ofBool, h.2] using h.1
  · intro s h
    simp [Loop.step, loop_drive_5, Expr.eval, Op.apply, Ty.wrap, ofBool, h.2, two_pow_32]
    omega
  · simp [driveState]
end Oak.Session.Refutations

namespace Oak.Session

/-- No callee or initial-state premises were present in the generated claim. -/
theorem loop_fill_3_terminates_refuted : ¬ loop_fill_3_terminates := by
  intro h
  exact Refutations.fill_not_terminates (h Refutations.zeroF Refutations.fillState)

/-- The universally quantified state admits an unrepresentable `u32` bound. -/
theorem loop_walk_4_terminates_refuted : ¬ loop_walk_4_terminates := by
  intro h
  exact Refutations.walk_not_terminates (h Refutations.zeroF Refutations.walkState)

/-- The universally quantified state admits an unrepresentable `u32` bound. -/
theorem loop_drive_5_terminates_refuted : ¬ loop_drive_5_terminates := by
  intro h
  exact Refutations.drive_not_terminates (h Refutations.zeroF Refutations.driveState)

end Oak.Session
