---- MODULE Model ----
EXTENDS Integers, TLC
VARIABLE state
StateSpace == [f_phase : {"Phase.Idle", "Phase.Reading", "Phase.Writing", "Phase.Conflict"}]
OakInitial(s) == (s.f_phase = "Phase.Idle")
OakInvariant(s) == (s.f_phase # "Phase.Conflict")
OakStep(s, t) == (IF (s.f_phase = "Phase.Idle") THEN (t.f_phase # "Phase.Conflict") ELSE (IF (s.f_phase = "Phase.Reading") THEN (t.f_phase = "Phase.Idle") ELSE (IF (s.f_phase = "Phase.Writing") THEN (t.f_phase = "Phase.Idle") ELSE (t.f_phase = "Phase.Conflict"))))
Init == state \in StateSpace /\ OakInitial(state)
Next == \E target \in StateSpace : state' = target /\ OakStep(state, target)
Spec == Init /\ [][Next]_state
TypeOK == state \in StateSpace
Safe == OakInvariant(state)
====
