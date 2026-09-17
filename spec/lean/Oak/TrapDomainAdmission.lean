/-!
# Non-circular admission of excluded trap inputs

`asm/trap_domain.go` separately checks that machine traps imply collected
source traps, without assuming the machine does not trap. This theorem
states the admission rule for arbitrary result/effect observations. It
does not establish that the Go collector, executor, or decider implements
the premises, nor that an architectural exception cannot resume.
-/

namespace Oak.TrapDomainAdmission

/-- A sound (possibly incomplete) source trap collector suffices. No
machine-trap exclusion is allowed in `covered` or `collectedSound`. -/
theorem admit_on_source_returns {Input Observation : Type}
    (typed machineTrap collectedTrap sourceTrap : Input → Prop)
    (machine source : Input → Observation)
    (collectedSound : ∀ i, typed i → collectedTrap i → sourceTrap i)
    (covered : ∀ i, typed i → machineTrap i → collectedTrap i)
    (values : ∀ i, typed i → ¬ machineTrap i → machine i = source i) :
    ∀ i, typed i → ¬ sourceTrap i →
      ¬ machineTrap i ∧ machine i = source i := by
  intro i hi returns
  have noMachineTrap : ¬ machineTrap i := by
    intro traps
    exact returns (collectedSound i hi (covered i hi traps))
  exact ⟨noMachineTrap, values i hi noMachineTrap⟩

/-- An implication proved only after excluding the machine trap is
vacuous: it cannot justify that exclusion. -/
theorem circular_premise_is_vacuous {Input : Type}
    (machineTrap sourceTrap : Input → Prop) :
    ∀ i, ¬ machineTrap i → machineTrap i → sourceTrap i := by
  intro i returns traps
  exact False.elim (returns traps)

/-- Equal return values do not justify an extra trap at an unsampled input. -/
theorem rare_trap_counterexample :
    (∀ i : Nat, i ≠ 1234 → i = i) ∧
    ¬ (∀ i : Nat, i = 1234 → False) := by
  constructor
  · intro i _
    rfl
  · intro covered
    exact covered 1234 rfl

end Oak.TrapDomainAdmission
