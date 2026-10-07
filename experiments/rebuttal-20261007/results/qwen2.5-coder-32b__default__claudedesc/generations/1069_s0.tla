------------------------------- MODULE TerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES active, pending, terminationDetected

Init == 
    /\ active \in [1..N -> BOOLEAN]
    /\ pending \in [1..N -> {0, 1, 2, 3}]
    /\ terminationDetected = (\A i \in 1..N: ~active[i])
    
Terminate ==
    \E i \in 1..N:
        active[i] 
        /\ (pending[i] = 0)
        /\ (terminationDetected' = IF (\A j \in 1..N: ~active[j]) THEN TRUE ELSE terminationDetected)
        /\ (active' = [active EXCEPT ![i] = FALSE])
        /\ (pending' = pending)

SendMsg ==
    \E i, j \in 1..N:
        active[i]
        /\ (i /= j)
        /\ (pending'[j] = pending[j] + 1)
        /\ (active' = active)
        /\ (terminationDetected' = terminationDetected)
        /\ (pending''[k] = IF k = i \/ k = j THEN pending'[k] ELSE pending[k]) \forall k \in 1..N

RcvMsg ==
    \E i \in 1..N:
        (pending[i] > 0)
        /\ (active'[i] = TRUE)
        /\ (pending'[i] = pending[i] - 1)
        /\ (terminationDetected' = terminationDetected)
        /\ (pending''[k] = IF k = i THEN pending'[k] ELSE pending[k]) \forall k \in 1..N

DetectTermination ==
    (\A i \in 1..N: ~active[i])
    /\ (pending = [i \in 1..N |-> 0])
    /\ (terminationDetected' = TRUE)
    /\ (active' = active)
    /\ (pending' = pending)

Next == 
    \/ Terminate
    \/ SendMsg
    \/ RcvMsg
    \/ DetectTermination

Spec ==
    /\ Init
    /\ [][Next]_<<active, pending, terminationDetected>>
    /\ WF_[DetectTermination]_<<active, pending, terminationDetected>>

Safe == 
    terminationDetected => (\A i \in 1..N: ~active[i]) /\ (pending = [i \in 1..N |-> 0])

Live ==
    <>(terminationDetected)

Quiescence ==
    [](terminationDetected => []terminationDetected)

IndInv ==
    TypeOK /\ Safe

TypeOK ==
    /\ active \in [1..N -> BOOLEAN]
    /\ pending \in [1..N -> {0, 1, 2, 3}]
    /\ terminationDetected \in BOOLEAN

=============================================================================