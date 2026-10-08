------------------------------- MODULE ToggleSystem -------------------------------
EXTENDS Naturals, TLC

CONSTANTS Action1, Action2

VARIABLES state

Init == state = FALSE

Next ==
  \/ /\ state = FALSE
     /\ (\/ state' = TRUE \land action = Action1
         \/ state' = TRUE \land action = Action2)
  \/ /\ state = TRUE
     /\ (\/ state' = FALSE \land action = Action1
         \/ state' = FALSE \land action = Action2)

Spec ==
  Init /\ [][Next]_<<state>>

SafetyProperties ==
  /\ \A s \in {FALSE, TRUE} : s \in {FALSE, TRUE}
  /\ \A s, s' \in {FALSE, TRUE} : s /= s'

LivenessProperties ==
  \/ <>[](state = FALSE) \/ <>[](state = TRUE)

Fairness ==
  WF_next(<<action>>)

CorrectnessProperties ==
  /\ SafetyProperties
  /\ LivenessProperties

THEOREM Spec => []SafetyProperties
THEOREM Spec => Fairness => CorrectnessProperties
=============================================================================