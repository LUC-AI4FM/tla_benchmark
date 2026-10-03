---- MODULE RingTermination ----
EXTENDS Integers, TLC

CONSTANTS N, MaxPending

VARIABLES active, pending, detected

vars == <<active, pending, detected>>
Nodes == 0..(N-1)

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ detected \in BOOLEAN

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ \E i \in Nodes : active[i]  \* System starts in a non-terminated state.
    /\ pending = [i \in Nodes |-> 0]
    /\ detected = FALSE

Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, detected>>

SendMessage(i) ==
    /\ active[i]
    /\ LET succ == (i + 1) % N IN
        pending[succ] < MaxPending
    /\ LET succ == (i + 1) % N IN
        pending' = [pending EXCEPT ![succ] = @ + 1]
    /\ UNCHANGED <<active, detected>>

ReceiveMessage(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<detected>>

DetectTermination ==
    /\ ~detected
    /\ \A j \in Nodes : ~active[j]
    /\ \A j \in Nodes : pending[j] = 0
    /\ detected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \/ \E i \in Nodes : Terminate(i)
    \/ \E i \in Nodes : SendMessage(i)
    \/ \E i \in Nodes : ReceiveMessage(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

Termination ==
    /\ \A i \in Nodes : ~active[i]
    /\ \A i \in Nodes : pending[i] = 0

DetectionImpliesTermination == detected => Termination

TerminationIsStable == Termination => [][Termination]_vars

TerminationLeadsToDetection == Termination ~> detected

StateConstraint == \A i \in Nodes : pending[i] <= MaxPending

=============================================================================