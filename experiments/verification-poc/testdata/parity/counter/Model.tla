---- MODULE Model ----
EXTENDS Integers, TLC
VARIABLE state
StateSpace == [f_count : 0..255]
OakInitial(s) == (s.f_count = 0)
OakInvariant(s) == (s.f_count <= 3)
OakStep(s, t) == (IF (s.f_count = 0) THEN (t.f_count = 1) ELSE (IF (s.f_count = 1) THEN (t.f_count = 2) ELSE (IF (s.f_count = 2) THEN (t.f_count = 3) ELSE (t.f_count = s.f_count))))
Init == state \in StateSpace /\ OakInitial(state)
Next == \E target \in StateSpace : state' = target /\ OakStep(state, target)
Spec == Init /\ [][Next]_state
TypeOK == state \in StateSpace
Safe == OakInvariant(state)
====
