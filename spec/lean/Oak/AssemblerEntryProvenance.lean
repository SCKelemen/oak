/-!
# Native verifier: entry-register provenance across calls and joins

This small, pure model records the *authority* to recreate entry-register
symbols, independently of the symbolic terms themselves. Its two supported
architectures match the reviewed native `verifierISAFor` policy.

The production correspondence points are `symbolicState.read`,
`clobberGPR`, `write`, `clone`, and `mergeTwo` in `asm/verify.go`.
An explicit write can rebind a value after clobber, but it does not restore
the original entry authority. A join requires the same architecture and
conservatively combines invalidation from either path.

This is a universal mathematical theorem about the stated transition model,
NOT a complete refinement proof of Go, machine instruction semantics,
call-result layout, or exact ARM64/RV64 bytes. Go regressions pin the
production correspondence; the full verifier remains separately audited.
-/

namespace Oak.AssemblerEntryProvenance

inductive Arch where
  | arm64
  | rv64
  deriving DecidableEq, Repr

/-- Precisely the GPRs lazily readable on entry by the current verifier. -/
def entryReadable : Arch → Nat → Bool
  | .arm64, n => decide (19 ≤ n ∧ n ≤ 30)
  | .rv64, n => decide (n = 1 ∨ n = 8 ∨ n = 9 ∨ (18 ≤ n ∧ n ≤ 27))

/-- Symbolic values are opaque to provenance. A restored entry value is a
legitimate *explicit write*, rather than an implicitly resurrected read. -/
inductive Value where
  | entry (reg : Nat)
  | written (word : Nat)
  | selected (left right : Value)
  deriving Repr, DecidableEq

/-- The architecture index makes cross-ISA joins unrepresentable here.
Production checks this equality explicitly in `mergeTwo`. -/
structure State (arch : Arch) where
  regs : Nat → Option Value
  invalidEntry : Nat → Bool

/-- Missing machine values may be materialized from entry only while the
entry is readable and no call has invalidated it on this path. -/
def read {arch : Arch} (s : State arch) (r : Nat) : Option Value :=
  match s.regs r with
  | some v => some v
  | none =>
      if s.invalidEntry r then none
      else if entryReadable arch r then some (.entry r)
      else none

/-- An actual machine write supplies a new value, but never revives
entry provenance previously invalidated by a call. -/
def write {arch : Arch} (s : State arch) (r : Nat) (v : Value) : State arch :=
  { s with regs := fun n => if n = r then some v else s.regs n }

/-- A call-clobber deletes the current value and permanently invalidates
the implicit incoming value when that register was entry-readable. -/
def clobber {arch : Arch} (s : State arch) (r : Nat) : State arch :=
  { regs := fun n => if n = r then none else s.regs n
    invalidEntry := fun n =>
      if n = r then (s.invalidEntry n || entryReadable arch n)
      else s.invalidEntry n }

/-- Go clones all maps; this mathematical fork has independent immutable
states. Its implementation aliasing is tested separately in Go. -/
def fork {arch : Arch} (s : State arch) : State arch × State arch := (s, s)

/-- A value materialized on only one path is not available after the join.
For two materialized values the solver later chooses under the path
condition; provenance needs only to record that both were defined. -/
def mergeValues : Option Value → Option Value → Option Value
  | some a, some b => some (.selected a b)
  | _, _ => none

/-- The Go verifier's join-of-negative-information rule: a clobber on
either predecessor prevents lazily materializing the old entry value. -/
def join {arch : Arch} (a b : State arch) : State arch :=
  { regs := fun r => mergeValues (a.regs r) (b.regs r)
    invalidEntry := fun r => a.invalidEntry r || b.invalidEntry r }

/-- A native call cannot resurrect a register via the entry-read fallback. -/
theorem read_clobber_none {arch : Arch} (s : State arch) (r : Nat) :
    read (clobber s r) r = none := by
  cases hInv : s.invalidEntry r <;>
    cases hEntry : entryReadable arch r <;>
    simp [read, clobber, hInv, hEntry]

/-- Non-clobbered registers retain the same readable value. -/
theorem read_clobber_other {arch : Arch} (s : State arch) (r n : Nat)
    (h : n ≠ r) : read (clobber s r) n = read s n := by
  simp [read, clobber, h]

/-- Real writes rebind a register, including one previously clobbered. -/
theorem read_write {arch : Arch} (s : State arch) (r : Nat) (v : Value) :
    read (write s r v) r = some v := by
  simp [read, write]

theorem read_write_after_clobber {arch : Arch} (s : State arch)
    (r : Nat) (v : Value) :
    read (write (clobber s r) r v) r = some v := by
  simp [read, write]

/-- No write silently restores the right to recreate the incoming value. -/
theorem write_keeps_invalidation {arch : Arch} (s : State arch)
    (r n : Nat) (v : Value) :
    (write s r v).invalidEntry n = s.invalidEntry n := rfl

theorem read_second_clobber_none {arch : Arch} (s : State arch)
    (r : Nat) (v : Value) :
    read (clobber (write (clobber s r) r v) r) r = none :=
  read_clobber_none _ _

/-- Immutable forks isolate a clobber from the untouched sibling. -/
theorem fork_sibling_unchanged {arch : Arch} (s : State arch) (r : Nat) :
    read (fork s).2 r = read s r := rfl

theorem fork_clobbered_side_none {arch : Arch} (s : State arch) (r : Nat) :
    read (clobber (fork s).1 r) r = none :=
  read_clobber_none _ _

theorem join_invalid_left {arch : Arch} (a b : State arch) (r : Nat)
    (h : a.invalidEntry r = true) :
    (join a b).invalidEntry r = true := by
  simp [join, h]

theorem join_invalid_right {arch : Arch} (a b : State arch) (r : Nat)
    (h : b.invalidEntry r = true) :
    (join a b).invalidEntry r = true := by
  simp [join, h]

/-- Clobber on either branch means that a join with that branch may not
manufacture the original register, whether the other path read it or not. -/
theorem read_join_clobber_right_none {arch : Arch}
    (a b : State arch) (r : Nat) :
    read (join a (clobber b r)) r = none := by
  cases hVal : a.regs r <;>
    cases hInv : a.invalidEntry r <;>
    cases hOther : b.invalidEntry r <;>
    cases hEntry : entryReadable arch r <;>
    simp [read, join, mergeValues, clobber, hVal, hInv, hOther, hEntry]

theorem read_join_clobber_left_none {arch : Arch}
    (a b : State arch) (r : Nat) :
    read (join (clobber a r) b) r = none := by
  cases hVal : b.regs r <;>
    cases hInv : a.invalidEntry r <;>
    cases hOther : b.invalidEntry r <;>
    cases hEntry : entryReadable arch r <;>
    simp [read, join, mergeValues, clobber, hVal, hInv, hOther, hEntry]

/-- Two explicit writes survive the join as a selected value. -/
theorem read_join_writes {arch : Arch} (a b : State arch) (r : Nat)
    (left right : Value) :
    read (join (write a r left) (write b r right)) r =
      some (.selected left right) := by
  simp [read, join, mergeValues, write]

/-- These concrete labels pin the ARM64/RV64 entry-readable Go predicates,
including both call-clobbered link registers. -/
example : entryReadable .arm64 30 = true := by decide
example : entryReadable .arm64 19 = true := by decide
example : entryReadable .arm64 18 = false := by decide
example : entryReadable .rv64 1 = true := by decide
example : entryReadable .rv64 8 = true := by decide
example : entryReadable .rv64 5 = false := by decide
example : entryReadable .rv64 30 = false := by decide

end Oak.AssemblerEntryProvenance
