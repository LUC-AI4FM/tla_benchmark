------------------------------- MODULE AsyncTermDetect --------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES active, pending, detected

ASSUME N \in Nat \ {0}

Init == /\ active \in [1..N -> BOOLEAN]
        /\ pending \in [1..N -> Nat]
        /\ detected = FALSE
        /\ (\A i \in 1..N : active[i] \/ pending[i] > 0)

Next ==
    \/ \E i \in 1..N :
        \/ /\ ~active[i]
           /\ pending[i] = 0
           /\ LET nextI == (i % N) + 1 IN
                CHOOSE j \in 1..N : j # i /\ j # nextI : 
                    active' = [active EXCEPT ![j] = FALSE]
                    /\ pending' = [pending EXCEPT ![j] = pending[j] - 1, ![nextI] = pending[nextI] + 1]
        \/ /\ active[i]
           /\ ~detected
           /\ LET nextI == (i % N) + 1 IN
                CHOOSE j \in 1..N : j # i /\ j # nextI : 
                    active' = [active EXCEPT ![i] = FALSE]
                    /\ pending' = [pending EXCEPT ![j] = pending[j] + 1]
        \/ /\ ~active[i]
           /\ pending[i] > 0
           /\ LET nextI == (i % N) + 1 IN
                CHOOSE j \in 1..N : j # i /\ j # nextI : 
                    pending' = [pending EXCEPT ![i] = pending[i] - 1, ![nextI] = pending[nextI] + 1]
    \/ DetectTermination

DetectTermination ==
    /\ ~detected
    /\ (\A i \in 1..N : ~active[i] /\ pending[i] = 0)
    /\ detected' = TRUE

Spec ==
    /\ Init
    /\ [][Next]_<<active, pending, detected>>
    /\ WF_[<>]_DetectTermination

StableDetected ==
    /\ detected
    => [](detected)

NoFalseDetection ==
    /\ ~(\E i \in 1..N : active[i] \/ pending[i] > 0) => detected

StateConstraint ==
    /\ (/\ i \in 1..N : active[i] \in BOOLEAN)
    /\ (/\ i \in 1..N : pending[i] \in Nat)

Invariant ==
    StableDetected /\ NoFalseDetection /\ StateConstraint

THEOREM Spec => []Invariant
================================================================================