namespace Oak.ClosureCapture

/-! # Closure capture storage discipline

Model for `docs/spec/05-ergonomics-and-cost.md` and
`docs/spec/60-effects-allocation.md` section 10: a capturing closure is
`code pointer + environment`, and the environment's storage must be
justified explicitly — capturing a local never silently heap-promotes it.

Scopes are lexical depths, as in `Oak.Escape`. A captureless closure is a
bare code pointer and may flow anywhere. A stack-stored environment is alive
exactly while execution has not left its frame, so a capturing closure may
not outlive the frame that stores its environment. -/

/-- Environment storage of a closure value. -/
inductive Env where
  | none                 -- captureless: bare code pointer
  | stack (frame : Nat)  -- environment lives in the frame at this depth
  deriving DecidableEq, Repr

/-- A closure value observed at `depth` is usable when its environment is
    still alive. -/
def Alive : Env → Nat → Prop
  | .none, _ => True
  | .stack frame, depth => frame ≤ depth

/-- **Captureless closures escape freely**: a bare code pointer has no
    environment to outlive. -/
theorem captureless_escapes_anywhere (depth : Nat) : Alive .none depth :=
  trivial

/-- **A stack environment cannot outlive its frame**: observing the closure
    after execution has left the storing frame dangles. This is the case the
    compiler must reject until storage justification surfaces exist. -/
theorem stack_env_cannot_outlive_frame {frame depth : Nat} (h : depth < frame) :
    ¬ Alive (.stack frame) depth := by
  intro halive
  have : frame ≤ depth := halive
  omega

/-- **Non-escaping capture is safe**: within (or below) the storing frame the
    environment is alive — the headroom a stack-storage justification surface
    can claim. -/
theorem nonescaping_stack_env_alive {frame depth : Nat} (h : frame ≤ depth) :
    Alive (.stack frame) depth := h

end Oak.ClosureCapture
