------------------------------- MODULE AsyncTermDet ---------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N  \* Number of nodes
ASSUME N \in Nat /\ N > 0

VARIABLES active, pending, detected

vars == <<active, pending, detected>>

Init ==
    /\ active = [1..N -> TRUE]
    /\ pending = [1..N -> 0]
    /\ detected = FALSE

Next ==
    \/ \E i \in 1..N : 
        (active[i] 
         /\ pending[i] > 0
         /\ /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
            /\ UNCHANGED <<active, detected>>)
    \/ \E i \in 1..N :
        (active[i]
         /\ pending'[i] = pending[i] + 1
         /\ UNCHANGED <<active, detected, EXCEPT ![OTHER_ELEMS]>>)
    \/ \E i \in 1..N :
        (active[i]
         /\ active' = [active EXCEPT ![i] = FALSE]
         /\ UNCHANGED <<pending, detected>>)
    \/ DetectTermination

DetectTermination ==
    /\ \A i \in 1..N : ~active[i] /\ pending[i] = 0
    /\ detected'
    /\ UNCHANGED <<active, pending>>

Spec ==
    Init /\ [][Next]_<<vars>>
    
\* Safety properties
SafetyDetectedImpliesTermination ==
    G \/ ~detected \/ (\A i \in 1..N : ~active[i] /\ pending[i] = 0)

SafetyStableOnceReached ==
    [](detected => []detected)

SafetyStateConstraint ==
    G (/\ active \in [1..N -> BOOLEAN]
       /\ pending \in [1..N -> Nat]
       /\ detected \in BOOLEAN)

\* Liveness properties
LivenessDetectionAfterTermination ==
    WF_vars(DetectTermination) /\ <>(~(\E i \in 1..N : active[i] \/ pending[i] > 0))

=============================================================================