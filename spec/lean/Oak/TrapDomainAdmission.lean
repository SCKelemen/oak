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

/-- Header guards execute even on the exiting iteration. A body trap is
covered only under the source continue condition. `State` is the selected
coupled symbolic state; soundness of that coupling is not established here. -/
theorem admit_loop_iteration {State : Type}
    (reached continues machineHeader machineBody : State → Prop)
    (collectedHeader collectedBody sourceHeader sourceBody : State → Prop)
    (headerSound : ∀ s, reached s → collectedHeader s → sourceHeader s)
    (bodySound : ∀ s, reached s → continues s → collectedBody s → sourceBody s)
    (headerCovered : ∀ s, reached s → machineHeader s → collectedHeader s)
    (bodyCovered : ∀ s, reached s → continues s → machineBody s →
      collectedHeader s ∨ collectedBody s) :
    ∀ s, reached s → ¬ sourceHeader s →
      ¬ machineHeader s ∧
        (continues s → ¬ sourceBody s → ¬ machineBody s) := by
  intro s hr noHeader
  constructor
  · intro traps
    exact noHeader (headerSound s hr (headerCovered s hr traps))
  · intro hc noBody traps
    cases bodyCovered s hr hc traps with
    | inl header => exact noHeader (headerSound s hr header)
    | inr body => exact noBody (bodySound s hr hc body)

/-- A trap projected at the actual first entry may justify a peeled
guard. Projection and collector soundness are explicit premises: an
arbitrary later iteration is not such an entry, and a body trap requires
source continuation. Source path guards are included in the predicates. -/
theorem first_iteration_trap_sound {Input State : Type}
    (entry : Input → State)
    (header body continues : State → Prop) (projected sourceTrap : Input → Prop)
    (projection : ∀ i, projected i →
      header (entry i) ∨ (continues (entry i) ∧ body (entry i)))
    (headerSound : ∀ i, header (entry i) → sourceTrap i)
    (bodySound : ∀ i, continues (entry i) → body (entry i) → sourceTrap i) :
    ∀ i, projected i → sourceTrap i := by
  intro i hp
  cases projection i hp with
  | inl header => exact headerSound i header
  | inr body => exact bodySound i body.1 body.2

/-- Trap freedom for a finite prefix of an abstract loop trajectory. At
zero remaining bodies the header still executes. `next` and `continues`
are source operations; relating them to machine execution is a separate
coupling obligation, not encoded by this predicate. -/
def LoopTrapFree {State : Type}
    (header body continues : State → Prop) (next : State → State) :
    Nat → State → Prop
  | 0, s => ¬ header s
  | n + 1, s => ¬ header s ∧
      (continues s → ¬ body s ∧ LoopTrapFree header body continues next n (next s))

/-- Separate, non-circular phase obligations compose along every finite
source-safe prefix, provided source reachability is preserved. This does
not establish termination or architectural exception non-resumption. -/
theorem admit_loop_prefix {State : Type}
    (reached continues machineHeader machineBody sourceHeader sourceBody : State → Prop)
    (next : State → State)
    (reachStep : ∀ s, reached s → continues s → reached (next s))
    (phases : ∀ s, reached s → ¬ sourceHeader s →
      ¬ machineHeader s ∧ (continues s → ¬ sourceBody s → ¬ machineBody s)) :
    ∀ n s, reached s → LoopTrapFree sourceHeader sourceBody continues next n s →
      LoopTrapFree machineHeader machineBody continues next n s := by
  intro n
  induction n with
  | zero =>
    intro s hr safe
    exact (phases s hr safe).1
  | succ n ih =>
    intro s hr safe
    have phase := phases s hr safe.1
    refine ⟨phase.1, ?_⟩
    intro hc
    have rest := safe.2 hc
    exact ⟨phase.2 hc rest.1, ih (next s) (reachStep s hr hc) rest.2⟩

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
