import Std.Tactic.BVDecide
namespace OakFinite
structure State where
  f_count : BitVec 8
  deriving DecidableEq
def oakInitial (s : State) : Bool := (decide (s.f_count = (BitVec.ofNat 8 0)))
def oakInvariant (s : State) : Bool := (decide (s.f_count <= (BitVec.ofNat 8 3)))
def oakStep (s t : State) : Bool := (bif (decide (s.f_count = (BitVec.ofNat 8 0))) then (decide (t.f_count = (BitVec.ofNat 8 1))) else (bif (decide (s.f_count = (BitVec.ofNat 8 1))) then (decide (t.f_count = (BitVec.ofNat 8 2))) else (bif (decide (s.f_count = (BitVec.ofNat 8 2))) then (decide (t.f_count = (BitVec.ofNat 8 3))) else (decide (t.f_count = s.f_count)))))
theorem base (s : State) : oakInitial s = true → oakInvariant s = true := by
  rcases s with ⟨s0⟩
  simp_all only [oakInitial, oakInvariant, oakStep] <;> bv_decide
theorem step (s t : State) : oakInvariant s = true → oakStep s t = true → oakInvariant t = true := by
  rcases s with ⟨s0⟩
  rcases t with ⟨t0⟩
  simp_all only [oakInitial, oakInvariant, oakStep] <;> bv_decide
end OakFinite
