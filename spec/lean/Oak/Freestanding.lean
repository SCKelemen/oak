/-!
# The freestanding host boundary (docs/spec/90-backend.md §2a)

A freestanding Oak object — a kernel, a hypervisor, firmware — has no libc.
What it may still call is a small set of *hooks* the host defines:

* `oak_host_write`, weak: a diagnostic that a hosted build prints to
  stderr reaches it as one bounded line, then the program traps as it
  always did (`emitHostBoundary` in Go);
* `oak_time_host_realtime_nanos`, `oak_time_host_monotonic_nanos`: the
  clocks of the `timehost` realization of the time port;
* `oak_io_host_*`: the seven bindings of the io port's native realization.

The model states what the tooling promises about the diagnostic path and
about the host time realization: a diagnostic path always ends in the
trap, delivers the message exactly when the hook is present, and never
depends on anything but compile-time text and the source position; and
`timehost_refresh` keeps the time port's monotonic invariant whenever the
host's monotonic hook is non-decreasing across reads.
-/

namespace Oak.Freestanding

/-- What a diagnostic path does, as observable events. -/
inductive Event where
  | write (fd : Nat) (line : String)
  | trap
  deriving DecidableEq, Repr

/-- The rendered line: compile-time text plus the source position; no
    format string, no runtime data. -/
def render (what file : String) (line : Nat) : String :=
  "oak: " ++ what ++ " at " ++ file ++ ":" ++ toString line ++ "\n"

/-- The freestanding diagnostic path: `oak_report` then `__builtin_trap`.
    `hook` is whether the weak symbol is defined. -/
def report (hook : Bool) (what file : String) (line : Nat) : List Event :=
  (if hook then [Event.write 2 (render what file line)] else []) ++ [Event.trap]

/-- Every diagnostic path traps. -/
theorem report_traps (hook : Bool) (what file : String) (line : Nat) :
    (report hook what file line).getLast? = some Event.trap := by
  cases hook <;> simp [report]

/-- The message is delivered exactly when the hook is present. -/
theorem report_delivers_iff (what file : String) (line : Nat) :
    (Event.write 2 (render what file line) ∈ report true what file line) ∧
    (∀ fd s, Event.write fd s ∉ report false what file line) := by
  constructor
  · simp [report]
  · intro fd s; simp [report]

/-- Diagnostics go to fd 2 only. -/
theorem report_fd (hook : Bool) (what file : String) (line : Nat) (fd : Nat) (s : String)
    (h : Event.write fd s ∈ report hook what file line) : fd = 2 := by
  cases hook <;> simp [report] at h
  exact h.1

/-- The trap is the last event: nothing runs after a failed check. -/
theorem report_length (hook : Bool) (what file : String) (line : Nat) :
    (report hook what file line).length = (if hook then 2 else 1) := by
  cases hook <;> simp [report]

/-! ## The host time realization -/

/-- The time port's source as far as `refresh` sees it: the last monotonic
    reading (`time_source_refresh` keeps it from moving backwards). -/
structure Source where
  wall : Int
  mono : Int
  deriving DecidableEq, Repr

/-- `time_source_refresh` (stdlib/time.oak): the wall clock is taken, the
    monotonic reading advances only forwards. -/
def refresh (s : Source) (wall mono : Int) : Source :=
  { wall := wall, mono := max s.mono mono }

/-- A host: its two hooks as functions of the read count (the harness's
    counter in `compiler/e2e_mcu_test.go`). -/
structure Host where
  realtime : Nat → Int
  monotonic : Nat → Int

/-- `timehost_refresh` on the k-th read. -/
def hostRefresh (h : Host) (k : Nat) (s : Source) : Source :=
  refresh s (h.realtime k) (h.monotonic k)

/-- The monotonic reading never decreases across refreshes, whatever the
    host's hook does. -/
theorem hostRefresh_mono_le (h : Host) (k : Nat) (s : Source) : s.mono ≤ (hostRefresh h k s).mono := by
  simp only [hostRefresh, refresh]; omega

/-- When the host's monotonic hook is non-decreasing, the source tracks it
    exactly from the first read on. -/
theorem hostRefresh_tracks (h : Host) (k : Nat) (s : Source)
    (hs : s.mono ≤ h.monotonic k) : (hostRefresh h k s).mono = h.monotonic k := by
  simp only [hostRefresh, refresh]; omega

/-- A stalled host clock (the same reading twice) is admitted: the source
    keeps its value. -/
theorem hostRefresh_stall (h : Host) (k : Nat) (s : Source) (hs : h.monotonic k ≤ s.mono) :
    (hostRefresh h k s).mono = s.mono := by
  simp only [hostRefresh, refresh]; omega

end Oak.Freestanding
