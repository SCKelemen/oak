import Out
open Sail PreSail
abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource
theorem nested1 : Out.Functions.nested false 1 = 1113 := by rfl
theorem nested2 : Out.Functions.nested false 2 = 1907 := by rfl
theorem nested0 : Out.Functions.nested false 0 = 323 := by rfl
theorem nested_early : Out.Functions.nested true 1 = 31 := by rfl
theorem shadow_case1 (s : State) : (Out.Functions.shadow_case false 1).run s = .ok 10 s := by rfl
theorem shadow_case0_export (s : State) : (Out.Functions.shadow_case false 0).run s = .ok 99 s := by rfl
#print axioms shadow_case0_export
