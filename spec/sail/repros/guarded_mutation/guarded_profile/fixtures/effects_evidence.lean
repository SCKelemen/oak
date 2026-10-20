import Out
import Std.Data.ExtDHashMap.Lemmas
open Sail PreSail
set_option linter.unusedSimpArgs false
abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource
def put (s : State) (v : Int) : State := {s with regs := s.regs.insert Register.OBS v}
private theorem overwrite (s : State) (a b : Int) :
 (s.regs.insert Register.OBS a).insert Register.OBS b = s.regs.insert Register.OBS b := by
 apply Std.ExtDHashMap.ext_get?
 intro k
 cases k
 simp
theorem normal_run (s : State) : (Out.Functions.probe false false 1).run s = .ok 10 (put s 2) := by
 simp [Out.Functions.probe, put, Sail.writeReg, PreSail.writeReg, PreSail.assert, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, overwrite]
theorem early_run (s : State) : (Out.Functions.probe true false 1).run s = .ok 31 (put s 1) := by rfl
theorem fallback_run (s : State) : (Out.Functions.probe false false 0).run s = .ok 5 (put s 3) := by
 simp [Out.Functions.probe, put, Sail.writeReg, PreSail.writeReg, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, overwrite]
#print axioms normal_run
#print axioms early_run
#print axioms fallback_run
theorem failure_run (s : State) : (Out.Functions.probe false true 1).run s =
 .error (.Assertion "effects.sail:10.58-10.59") (put s 2) := by
 simp [Out.Functions.probe, put, Sail.writeReg, PreSail.writeReg, PreSail.assert,
 EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, modify, modifyGet,
 MonadStateOf.modifyGet, EStateM.modifyGet, throw, throwThe, MonadExceptOf.throw, EStateM.throw, overwrite]
#print axioms failure_run
