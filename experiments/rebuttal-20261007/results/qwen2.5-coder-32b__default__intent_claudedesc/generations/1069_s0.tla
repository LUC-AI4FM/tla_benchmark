------------------------------- MODULE TerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of nodes in the ring

VARIABLES active, pendingMessages, terminated

Init == /\ active \in [1..N -> BOOLEAN]
        /\ pendingMessages \in [1..N -> 0..N] \* Bounding pending messages for model checking
        /\ terminated = FALSE
        /\ (/\ (\A i \in 1..N : ~active[i]) => terminated)

Next == \/ \E i \in 1..N, j \in 1..N : active[i] /\ i # j /\ 
                            (active' = [active EXCEPT ![i] = FALSE])
                            /\ (pendingMessages' = [pendingMessages EXCEPT ![j] = pendingMessages[j] + 1])
                            /\ terminated' = terminated
          \/ \E i \in 1..N : ~active[i] /\ pendingMessages[i] > 0 /\
                             (active' = [active EXCEPT ![i] = TRUE])
                             /\ (pendingMessages' = [pendingMessages EXCEPT ![i] = pendingMessages[i] - 1])
                             /\ terminated' = terminated
          \/ \E i \in 1..N : active[i] /\ 
                             (active' = [active EXCEPT ![i] = FALSE])
                             /\ pendingMessages' = pendingMessages
                             /\ terminated' = terminated
          \/ (\A i \in 1..N : ~active[i] /\ pendingMessages[i] = 0) /\
             (active' = active)
             /\ pendingMessages' = pendingMessages
             /\ terminated'

Spec == Init /\ [][Next]_<<active, pendingMessages, terminated>>

TerminationDetected ==> (\A i \in 1..N : ~active[i] /\ pendingMessages[i] = 0) => terminated

Quiescence ==> <>[](terminated => []<>(terminated))

SafetyInvariant == Spec /\ [](terminated => TerminationDetected)

LivenessProperty == <>(terminated)

FairnessAssumption == WF_next(Next)

THEOREM SafetyInvariant /\ LivenessProperty
=============================================================================