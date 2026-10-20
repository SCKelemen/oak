import Oak.AssemblerEntryProvenance

/-!
# Native symbolic verifier: full caller-saved register-state contract

The existing GPR entry-provenance transition model is lifted to the native
call boundary's remaining register classes. Go's `verifierISA.forgetCallerSaved`
is the implementation being compared against this abstract model.

AArch64 vector v8–v15 are preserved in the verifier's existing low-half
contract, while other vector registers and NZCV facts are invalidated.
RV64 preserves only f8–f9 and f18–f27 among modeled FPRs; the entire
RVV register file plus vl/vtype configuration is invalidated.
The AArch64 FPR map is unused; floating point values reside in vector views.

A `Bool` bound fact models availability, not the contents or lane widths of a
machine register. `join` records necessary availability only. These theorems
do NOT establish implementation-level equivalence, vector-lane ABI semantics,
memory ordering, instruction encoding or source-to-machine correctness.
-/

namespace Oak.AssemblerCallState

abbrev Arch := Oak.AssemblerEntryProvenance.Arch

/-- The independent ABI contract for caller-owned GPRs. -/
def callerSavedGPR : Arch → Nat → Bool
  | .arm64, r => decide (r ≤ 17 ∨ r = 30)
  | .rv64, r => decide
      (r = 1 ∨ (5 ≤ r ∧ r ≤ 7) ∨ (10 ≤ r ∧ r ≤ 17) ∨ (28 ≤ r ∧ r ≤ 31))

/-- RV64 floating-point registers fs0–fs11 (f8, f9, f18–f27)
are preserved. AArch64 floating point is represented in vector lanes, not
in the RV64-specific Go `fregs` map. -/
def callerSavedFPR : Arch → Nat → Bool
  | .arm64, _ => false
  | .rv64, r => decide (r ≠ 8 ∧ r ≠ 9 ∧ (r < 18 ∨ r > 27))

/-- RVV standard-ABI vector registers are all call-clobbered.
AArch64 preserves only the low-half contract for v8–v15. -/
def callerSavedVector : Arch → Nat → Bool
  | .arm64, r => decide (r < 8 ∨ r > 15)
  | .rv64, _ => true

def forgetRVVConfig : Arch → Bool
  | .arm64 => false
  | .rv64 => true

def forgetFlags : Arch → Bool
  | .arm64 => true
  | .rv64 => false

/-- The GPR state is indexed by a single architecture. Other registers
carry abstract availability only, independent of value contents. -/
structure State (arch : Arch) where
  gpr : Oak.AssemblerEntryProvenance.State arch
  fprBound : Nat → Bool
  vectorBound : Nat → Bool
  rvvConfig : Option Nat
  flagsKnown : Bool

/-- One common ABI call transition is applied before result writes.
The entry-GPR invalidation bit is monotonic even after explicit writes. -/
def call {arch : Arch} (s : State arch) : State arch :=
  { gpr :=
      { regs := fun r =>
          if callerSavedGPR arch r then none else s.gpr.regs r
        invalidEntry := fun r =>
          s.gpr.invalidEntry r ||
            (callerSavedGPR arch r && Oak.AssemblerEntryProvenance.entryReadable arch r) }
    fprBound := fun r =>
      if callerSavedFPR arch r then false else s.fprBound r
    vectorBound := fun r =>
      if callerSavedVector arch r then false else s.vectorBound r
    rvvConfig := if forgetRVVConfig arch then none else s.rvvConfig
    flagsKnown := if forgetFlags arch then false else s.flagsKnown }

/-- New return values are written after the common call transition. -/
def writeFPR {arch : Arch} (s : State arch) (reg : Nat) : State arch :=
  { s with fprBound := fun r => if r = reg then true else s.fprBound r }

def writeVector {arch : Arch} (s : State arch) (reg : Nat) : State arch :=
  { s with vectorBound := fun r => if r = reg then true else s.vectorBound r }

def writeGPR {arch : Arch} (s : State arch) (reg value : Nat) : State arch :=
  { s with gpr := Oak.AssemblerEntryProvenance.write s.gpr reg (.written value) }

/-- The Boolean join is a necessary condition for availability. Concrete
terms and vector lanes must additionally agree structurally in the Go
executor; their value-level merge is outside this abstraction. -/
def join {arch : Arch} (a b : State arch) : State arch :=
  { gpr := Oak.AssemblerEntryProvenance.join a.gpr b.gpr
    fprBound := fun r => a.fprBound r && b.fprBound r
    vectorBound := fun r => a.vectorBound r && b.vectorBound r
    rvvConfig :=
      if a.rvvConfig == b.rvvConfig then a.rvvConfig else none
    flagsKnown := a.flagsKnown && b.flagsKnown }

/-- A caller-clobbered FPR cannot keep a materialized pre-call value. -/
theorem caller_fpr_dead {arch : Arch} (s : State arch) (r : Nat)
    (h : callerSavedFPR arch r = true) :
    (call s).fprBound r = false := by
  simp [call, h]

theorem callee_fpr_retained {arch : Arch} (s : State arch) (r : Nat)
    (h : callerSavedFPR arch r = false) :
    (call s).fprBound r = s.fprBound r := by
  simp [call, h]

theorem caller_vector_dead {arch : Arch} (s : State arch) (r : Nat)
    (h : callerSavedVector arch r = true) :
    (call s).vectorBound r = false := by
  simp [call, h]

theorem callee_vector_retained {arch : Arch} (s : State arch) (r : Nat)
    (h : callerSavedVector arch r = false) :
    (call s).vectorBound r = s.vectorBound r := by
  simp [call, h]

theorem caller_gpr_dead {arch : Arch} (s : State arch) (r : Nat)
    (h : callerSavedGPR arch r = true) :
    (call s).gpr.regs r = none := by
  simp [call, h]

/-- Lazy entry-provenance cannot be restored for an entry-readable GPR
that the native calling convention clobbers. -/
theorem caller_entry_gpr_invalid {arch : Arch} (s : State arch) (r : Nat)
    (h : callerSavedGPR arch r = true)
    (he : Oak.AssemblerEntryProvenance.entryReadable arch r = true) :
    (call s).gpr.invalidEntry r = true := by
  simp [call, h, he]

theorem caller_entry_gpr_unreadable {arch : Arch} (s : State arch) (r : Nat)
    (h : callerSavedGPR arch r = true)
    (he : Oak.AssemblerEntryProvenance.entryReadable arch r = true) :
    Oak.AssemblerEntryProvenance.read (call s).gpr r = none := by
  simp [Oak.AssemblerEntryProvenance.read, call, h, he]

theorem return_fpr_rebound {arch : Arch} (s : State arch) (r : Nat) :
    (writeFPR (call s) r).fprBound r = true := by
  simp [writeFPR]

theorem return_vector_rebound {arch : Arch} (s : State arch) (r : Nat) :
    (writeVector (call s) r).vectorBound r = true := by
  simp [writeVector]

theorem return_gpr_keeps_entry_invalidation {arch : Arch}
    (s : State arch) (r n value : Nat) :
    (writeGPR (call s) r value).gpr.invalidEntry n =
      (call s).gpr.invalidEntry n := by
  rfl

theorem join_fpr_requires_both {arch : Arch}
    (a b : State arch) (r : Nat) :
    (join a b).fprBound r = (a.fprBound r && b.fprBound r) := rfl

theorem join_vector_requires_both {arch : Arch}
    (a b : State arch) (r : Nat) :
    (join a b).vectorBound r =
      (a.vectorBound r && b.vectorBound r) := rfl

/-- Even if the other branch has a value, a call-clobbered register
cannot be joined into a definite FPR/vector fact. -/
theorem join_called_fpr_left_dead {arch : Arch}
    (a b : State arch) (r : Nat)
    (h : callerSavedFPR arch r = true) :
    (join (call a) b).fprBound r = false := by
  simp [join, call, h]

theorem join_called_fpr_right_dead {arch : Arch}
    (a b : State arch) (r : Nat)
    (h : callerSavedFPR arch r = true) :
    (join a (call b)).fprBound r = false := by
  simp [join, call, h]

theorem join_called_vector_left_dead {arch : Arch}
    (a b : State arch) (r : Nat)
    (h : callerSavedVector arch r = true) :
    (join (call a) b).vectorBound r = false := by
  simp [join, call, h]

theorem join_called_vector_right_dead {arch : Arch}
    (a b : State arch) (r : Nat)
    (h : callerSavedVector arch r = true) :
    (join a (call b)).vectorBound r = false := by
  simp [join, call, h]

theorem rv64_all_vector_dead (s : State .rv64) (r : Nat) :
    (call s).vectorBound r = false := by
  simp [call, callerSavedVector]

theorem rv64_config_dead (s : State .rv64) :
    (call s).rvvConfig = none := by
  simp [call, forgetRVVConfig]

theorem arm64_flags_dead (s : State .arm64) :
    (call s).flagsKnown = false := by
  simp [call, forgetFlags]

theorem rv64_fs8_retained (s : State .rv64) :
    (call s).fprBound 8 = s.fprBound 8 := by
  simp [call, callerSavedFPR]

theorem rv64_fa0_dead (s : State .rv64) :
    (call s).fprBound 10 = false := by
  simp [call, callerSavedFPR]

theorem arm64_v8_retained (s : State .arm64) :
    (call s).vectorBound 8 = s.vectorBound 8 := by
  simp [call, callerSavedVector]

theorem arm64_v16_dead (s : State .arm64) :
    (call s).vectorBound 16 = false := by
  simp [call, callerSavedVector]

/-- Explicit examples pin the ABI mask independently of the Go policy. -/
example : callerSavedGPR .rv64 1 = true := by decide
example : callerSavedGPR .arm64 30 = true := by decide
example : callerSavedFPR .rv64 8 = false := by decide
example : callerSavedFPR .rv64 9 = false := by decide
example : callerSavedFPR .rv64 18 = false := by decide
example : callerSavedFPR .rv64 27 = false := by decide
example : callerSavedFPR .rv64 10 = true := by decide
example : callerSavedVector .arm64 8 = false := by decide
example : callerSavedVector .arm64 15 = false := by decide
example : callerSavedVector .arm64 16 = true := by decide
example : callerSavedVector .rv64 8 = true := by decide

end Oak.AssemblerCallState
