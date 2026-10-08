MODULE BoundedCounterSystem
EXTENDS Naturals

VARIABLE c

Init == c = 0

SubInc ==
  /\ c < 3
  /\ c' = c + 1

Stutter ==
  /\ TRUE
  /\ c' = c

Next == SubInc \/ Stutter

Spec == Init /\ [][Next]_c /\ WF_0(SubInc)

SafetyInvariant ==
  /\ c >= 0
  /\ c <= 3

LivenessGoal == <> (c = 3)

THEOREM SafetyTheorem == Spec => []SafetyInvariant

THEOREM LivenessTheorem == Spec => LivenessGoal

===============================================================================