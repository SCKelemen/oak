/-!
# The choice tape's heavy-tailed and swarm samplers

`docs/spec/110-testing.md` "Choice tapes": `test_geometric` counts the
consecutive set bits at the head of the tape, capped; `test_swarm_mask`
keeps each fault kind with probability one half and never keeps none.
Both are plain Oak over `test_byte`/`test_bool`; these are their models.
-/

namespace Oak.ChoiceTape

/-- Consecutive set bits before the first clear one, at most `max`. An
    exhausted tape is a tape of clear bits. -/
def leadingOnes : List Bool → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | false :: _, _ + 1 => 0
  | true :: rest, max + 1 => leadingOnes rest max + 1

theorem leadingOnes_le (bits : List Bool) (max : Nat) : leadingOnes bits max ≤ max := by
  induction bits generalizing max with
  | nil => cases max <;> simp [leadingOnes]
  | cons b rest ih =>
      cases max with
      | zero => simp [leadingOnes]
      | succ m =>
          cases b with
          | false => simp [leadingOnes]
          | true =>
              simp only [leadingOnes]
              exact Nat.succ_le_succ (ih m)

/-- An exhausted tape draws nothing: shrinking to the empty tape shortens
    every delay to its floor. -/
theorem leadingOnes_exhausted (max : Nat) : leadingOnes [] max = 0 := by
  cases max <;> rfl

/-- A clear bit at the head ends the count. -/
theorem leadingOnes_clear (rest : List Bool) (max : Nat) :
    leadingOnes (false :: rest) max = 0 := by
  cases max <;> rfl

/-- The swarm mask over `kinds` kept flags: bit i set when flag i is kept. -/
def swarmBits : List Bool → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | b :: rest, k + 1 => (if b then 1 else 0) + 2 * swarmBits rest k

theorem swarmBits_lt (flags : List Bool) (kinds : Nat) : swarmBits flags kinds < 2 ^ kinds := by
  induction flags generalizing kinds with
  | nil =>
      cases kinds with
      | zero => simp [swarmBits]
      | succ n =>
          simp only [swarmBits]
          exact Nat.two_pow_pos _
  | cons b rest ih =>
      cases kinds with
      | zero => simp [swarmBits]
      | succ k =>
          simp only [swarmBits, Nat.pow_succ]
          have h := ih k
          cases b <;> simp <;> omega

/-- The mask `test_swarm_mask` returns: the drawn bits, or one kind when
    every bit fell. It is never zero for a positive number of kinds. -/
def swarmMask (flags : List Bool) (kinds fallback : Nat) : Nat :=
  if swarmBits flags kinds = 0 ∧ 0 < kinds then 2 ^ (fallback % kinds) else swarmBits flags kinds

theorem swarmMask_pos (flags : List Bool) (kinds fallback : Nat) (h : 0 < kinds) :
    0 < swarmMask flags kinds fallback := by
  unfold swarmMask
  split
  · exact Nat.two_pow_pos _
  · rename_i hn
    have : swarmBits flags kinds ≠ 0 := fun hz => hn ⟨hz, h⟩
    omega

theorem swarmMask_lt (flags : List Bool) (kinds fallback : Nat) (h : 0 < kinds) :
    swarmMask flags kinds fallback < 2 ^ kinds := by
  unfold swarmMask
  split
  · exact Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ h)
  · exact swarmBits_lt flags kinds

end Oak.ChoiceTape
