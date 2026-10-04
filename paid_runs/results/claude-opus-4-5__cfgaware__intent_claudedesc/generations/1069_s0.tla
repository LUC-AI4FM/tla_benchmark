---------------------------- MODULE TerminationDetection ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N, MaxPending

ASSUME N \in Nat /\ N > 0
ASSUME MaxPending \in Nat /\ MaxPending >= 0

Nodes == 0..(N-1)

VARIABLES active, pending, terminated, detected

vars == <<active, pending, terminated, detected>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> 0..MaxPending]
    /\ terminated \in BOOLEAN
    /\ detected \in BOOLEAN

Terminated ==
    /\ \A n \in Nodes : ~active[n]
    /\ \A n \in Nodes : pending[n] = 0

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [n \in Nodes |-> 0]
    /\ terminated = (\A n \in Nodes : ~active[n])
    /\ detected \in IF (\A n \in Nodes : ~active[n]) THEN {TRUE, FALSE} ELSE {FALSE}

SendMessage(sender, receiver) ==
    /\ active[sender]
    /\ pending[receiver] < MaxPending
    /\ pending' = [pending EXCEPT ![receiver] = @ + 1]
    /\ UNCHANGED <<active, terminated, detected>>

Deactivate(node) ==
    /\ active[node]
    /\ active' = [active EXCEPT ![node] = FALSE]
    /\ UNCHANGED <<pending, terminated, detected>>

ReceiveMessage(node) ==
    /\ pending[node] > 0
    /\ pending' = [pending EXCEPT ![node] = @ - 1]
    /\ active' = [active EXCEPT ![node] = TRUE]
    /\ UNCHANGED <<terminated, detected>>

UpdateTerminated ==
    /\ ~terminated
    /\ \A n \in Nodes : ~active[n]
    /\ \A n \in Nodes : pending[n] = 0
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, pending, detected>>

DetectTermination ==
    /\ terminated
    /\ ~detected
    /\ detected' = TRUE
    /\ UNCHANGED <<active, pending, terminated>>

Stutter ==
    /\ terminated
    /\ detected
    /\ UNCHANGED vars

Next ==
    \/ \E sender, receiver \in Nodes : SendMessage(sender, receiver)
    \/ \E node \in Nodes : Deactivate(node)
    \/ \E node \in Nodes : ReceiveMessage(node)
    \/ UpdateTerminated
    \/ DetectTermination
    \/ Stutter

Fairness ==
    /\ WF_vars(UpdateTerminated)
    /\ WF_vars(DetectTermination)

Spec == Init /\ [][Next]_vars /\ Fairness

Safety == detected => Terminated

Quiescence == terminated => []terminated

Liveness == Terminated ~> detected

=============================================================================