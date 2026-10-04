---------------------------- MODULE spec ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES
    active,
    pending,
    detected

vars == <<active, pending, detected>>

Nodes == 0..(N-1)

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ detected \in BOOLEAN

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [n \in Nodes |-> 0]
    /\ detected = FALSE

Terminated ==
    /\ \A n \in Nodes : ~active[n]
    /\ \A n \in Nodes : pending[n] = 0

Terminate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<pending, detected>>

SendMsg(sender, receiver) ==
    /\ active[sender]
    /\ pending' = [pending EXCEPT ![receiver] = @ + 1]
    /\ UNCHANGED <<active, detected>>

ReceiveMsg(n) ==
    /\ pending[n] > 0
    /\ pending' = [pending EXCEPT ![n] = @ - 1]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ UNCHANGED detected

DetectTermination ==
    /\ ~detected
    /\ Terminated
    /\ detected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \/ \E n \in Nodes : Terminate(n)
    \/ \E s, r \in Nodes : SendMsg(s, r)
    \/ \E n \in Nodes : ReceiveMsg(n)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(DetectTermination)

Safety ==
    detected => Terminated

StableTermination ==
    Terminated => [][Terminated]_vars

DetectionLiveness ==
    Terminated ~> detected

Inv ==
    /\ TypeOK
    /\ (detected => Terminated)

StateConstraint ==
    \A n \in Nodes : pending[n] <= 3

=============================================================================