import Out
/-- This records a reproduced exporter defect; 63 is not the Sail source result. -/
theorem exported_total_result : Out.Functions.repro false 1 = 63 := by rfl
#print axioms exported_total_result
#eval Out.Functions.repro false 1
