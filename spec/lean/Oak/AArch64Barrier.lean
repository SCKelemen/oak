namespace Oak.AArch64Barrier

/-- Shareability/domain classification retained by the Oak source spelling. -/
inductive Scope where
  | innerShareable
  | system
  deriving DecidableEq, Repr

/-- Deliberately coarse data-ordering capability. This is an Oak machine-profile
    classification, not a replacement for the Arm axiomatic memory model. -/
inductive DataOrdering where
  | none
  | load
  | full
  deriving DecidableEq, Repr

/-- The capabilities Oak relies on when selecting a barrier instruction.

`completion` records the additional completion property claimed for DSB over
DMB in the selected domain. `instructionSync` is reserved for ISB. -/
structure Capability where
  dataOrdering : DataOrdering
  completion : Bool
  instructionSync : Bool
  scope : Option Scope
  deriving DecidableEq, Repr

inductive Barrier where
  | dmbIshld
  | dmbIsh
  | dmbSy
  | dsbIsh
  | dsbSy
  | isb
  deriving DecidableEq, Repr

def capability : Barrier -> Capability
  | .dmbIshld => ⟨.load, false, false, some .innerShareable⟩
  | .dmbIsh   => ⟨.full, false, false, some .innerShareable⟩
  | .dmbSy    => ⟨.full, false, false, some .system⟩
  | .dsbIsh   => ⟨.full, true, false, some .innerShareable⟩
  | .dsbSy    => ⟨.full, true, false, some .system⟩
  | .isb      => ⟨.none, false, true, none⟩

/-- DMB is modeled as ordering, never as completion. -/
theorem dmb_does_not_claim_completion (b : Barrier)
    (h : b = .dmbIshld ∨ b = .dmbIsh ∨ b = .dmbSy) :
    (capability b).completion = false := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- DSB carries the completion capability in each admitted data scope. -/
theorem dsb_claims_completion (b : Barrier)
    (h : b = .dsbIsh ∨ b = .dsbSy) :
    (capability b).completion = true := by
  rcases h with rfl | rfl <;> rfl

/-- ISB is the only admitted instruction-stream synchronization primitive. -/
theorem isb_instruction_sync : (capability .isb).instructionSync = true := rfl

theorem data_barriers_do_not_claim_instruction_sync (b : Barrier)
    (h : b ≠ .isb) : (capability b).instructionSync = false := by
  cases b <;> simp_all [capability]

/-- The inner-shareable DSB preserves full data ordering and adds completion
    relative to the corresponding DMB profile. -/
theorem dsb_ish_extends_dmb_ish :
    (capability .dsbIsh).dataOrdering = (capability .dmbIsh).dataOrdering ∧
    (capability .dmbIsh).completion = false ∧
    (capability .dsbIsh).completion = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- The system-scope DSB similarly extends system-scope DMB with completion. -/
theorem dsb_sy_extends_dmb_sy :
    (capability .dsbSy).dataOrdering = (capability .dmbSy).dataOrdering ∧
    (capability .dmbSy).completion = false ∧
    (capability .dsbSy).completion = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- ISHLD is intentionally weaker than the full inner-shareable data barrier in
    the Oak profile; users must request `dmb_ish` when full data ordering is
    required. -/
theorem ishld_is_not_full :
    (capability .dmbIshld).dataOrdering ≠ .full := by
  decide

/-- ISB makes no claim of DMB/DSB-style data ordering or completion. -/
theorem isb_is_not_data_barrier :
    (capability .isb).dataOrdering = .none ∧
    (capability .isb).completion = false := by
  exact ⟨rfl, rfl⟩

end Oak.AArch64Barrier
