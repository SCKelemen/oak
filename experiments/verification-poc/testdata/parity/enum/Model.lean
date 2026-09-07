import Std.Tactic.BVDecide
namespace OakFinite
inductive E_Phase where
  | c_Idle
  | c_Reading
  | c_Writing
  | c_Conflict
  deriving DecidableEq
structure State where
  f_phase : E_Phase
  deriving DecidableEq
def oakInitial (s : State) : Bool := (decide (s.f_phase = E_Phase.c_Idle))
def oakInvariant (s : State) : Bool := (decide (s.f_phase ≠ E_Phase.c_Conflict))
def oakStep (s t : State) : Bool := (bif (decide (s.f_phase = E_Phase.c_Idle)) then (decide (t.f_phase ≠ E_Phase.c_Conflict)) else (bif (decide (s.f_phase = E_Phase.c_Reading)) then (decide (t.f_phase = E_Phase.c_Idle)) else (bif (decide (s.f_phase = E_Phase.c_Writing)) then (decide (t.f_phase = E_Phase.c_Idle)) else (decide (t.f_phase = E_Phase.c_Conflict)))))
theorem base (s : State) : oakInitial s = true → oakInvariant s = true := by
  rcases s with ⟨s0⟩
  cases s0 <;> simp_all only [oakInitial, oakInvariant, oakStep] <;> bv_decide
theorem step (s t : State) : oakInvariant s = true → oakStep s t = true → oakInvariant t = true := by
  rcases s with ⟨s0⟩
  rcases t with ⟨t0⟩
  cases s0 <;> cases t0 <;> simp_all only [oakInitial, oakInvariant, oakStep] <;> bv_decide
end OakFinite
