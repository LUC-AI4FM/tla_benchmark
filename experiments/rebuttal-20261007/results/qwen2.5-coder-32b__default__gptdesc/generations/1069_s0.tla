------------------------------- MODULE AsyncTermDetect -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of nodes

VARIABLES active, pending, detected

Init == /\ active = {n \in 1..N : TRUE}
        /\ pending = [n \in 1..N -> 0]
        /\ detected = FALSE

Next ==
    \/ \E n \in 1..N :
        /\ active[n]
        /\ pending[n] > 0
        /\ /\* Send message to next node
           LET nextNode == IF n = N THEN 1 ELSE n + 1
           IN pending[nextNode]' = pending[nextNode] + 1
              /\ UNCHANGED <<active, pending EXCEPT ![n], detected>>
    \/ \E n \in 1..N :
        /\ active[n]
        /\ pending[n] > 0
        /\ /\* Receive message
           pending'[n] = pending[n] - 1
           /\ UNCHANGED <<active, pending EXCEPT ![n], detected>>
    \/ \E n \in 1..N :
        /\ active[n]
        /\ /\* Node terminates
           active'[n] = FALSE
           /\ UNCHANGED <<pending, detected>>
    \/ /\* Detect termination
       /\ \A n \in 1..N : ~active[n] /\ pending[n] = 0
       /\ detected'
       /\ UNCHANGED <<active, pending>>

Spec ==
    /\ Init
    /\ [][Next]_<<active, pending, detected>>
    /\ WF_next(<<active, pending, detected>>, DetectTermination)

DetectTermination ==
    /\ \A n \in 1..N : ~active[n] /\ pending[n] = 0
    /\ detected

InvariantDetectedImpliesActualTermination ==
    /\ detected => (\A n \in 1..N : ~active[n] /\ pending[n] = 0)

InvariantStabilityOfDetection ==
    /\ detected => []detected

InvariantBoundedModelChecking ==
    /\ \A n \in 1..N : pending[n] < N

=============================================================================