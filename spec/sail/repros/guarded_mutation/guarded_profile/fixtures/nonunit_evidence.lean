import Out
theorem normal : Out.Functions.probe false 1 = 1007 := by rfl
theorem fallback : Out.Functions.probe false 0 = 2009 := by rfl
theorem early : Out.Functions.probe true 1 = 31 := by rfl
#print axioms normal
#print axioms fallback
#print axioms early
