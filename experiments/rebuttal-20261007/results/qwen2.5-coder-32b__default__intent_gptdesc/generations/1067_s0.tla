------------------------------- MODULE DistributedTerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES states, terminated

\* Process states: TRUE for active, FALSE for inactive
Init == /\ states \in [1..N -> BOOLEAN]
        /\ terminated = FALSE

Next ==
    \/ \E i \in 1..N : 
            (\* Local termination decision \*)
            /\ states' = [states EXCEPT ![i] = FALSE]
            /\ terminated' = terminated
    \/ \E i, j \in 1..N : i # j /\ states[i] 
            (\* Activation of another process \*)
            /\ states' = [states EXCEPT ![j] = TRUE]
            /\ terminated' = terminated
    \/ \A i \in 1..N : ~states[i]
            (\* Termination detection event \*)
            /\ states' = states
            /\ terminated' = TRUE

Spec == Init /\ [][Next]_<<states, terminated>>

\* Safety: Once termination is declared, the system state must be quiescent (no active processes)
TerminationSafety == G(terminated -> (\A i \in 1..N : ~states[i]))

\* Quiescence persistence: Once the system reaches the all-inactive state it remains all-inactive thereafter
QuiescencePersistence == G((\A i \in 1..N : ~states[i]) -> X(\A i \in 1..N : ~states'[i]))

\* Liveness: Whenever the system is quiescent, termination detection will eventually be raised
TerminationLiveness == <>(terminated)

Invariant == TerminationSafety /\ QuiescencePersistence

Fairness ==
    WF_next(<>[](\E i \in 1..N : states[i] -> (\E j \in 1..N : ~states[j])))

THEOREM Spec => []Invariant
THEOREM Spec => Fairness => TerminationLiveness
================================================================================