------------------------------ MODULE TerminationRing ------------------------------
EXTENDS Naturals

CONSTANTS N, MaxMsg

Node == 1 .. N

VARIABLES active, pending, termDetected

(* Helper: successor in the ring *)
NextNode(i) ==
    IF i = N THEN 1 ELSE i + 1

Init ==
   /\ active = [i \in Node |-> TRUE]
   /\ pending = [i \in Node |-> 0]
   /\ termDetected = FALSE

SendMsg(i) ==
    /\ active[i]
    /\ pending[i] > 0
    /\ LET j == NextNode(i)
       IN pending' = [k \in Node |
                        IF k = i THEN pending[k]-1
                        ELSE IF k = j THEN pending[k]+1
                        ELSE pending[k]]
    /\ active' = active
    /\ termDetected' = termDetected

TerminateNode(i) ==
    /\ active[i]
    /\ pending[i] = 0
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    /\ termDetected' = termDetected

DetectTermination ==
    /\ (\A i \in Node : ~active[i] /\ pending[i] = 0)
    /\ termDetected' = TRUE
    /\ active' = active
    /\ pending' = pending

Next ==
   (\E i \in Node : SendMsg(i))
   \/ (\E i \in Node : TerminateNode(i))
   \/ DetectTermination

vars == <<active, pending, termDetected>>

Spec ==
   Init
   /\ [][Next]_vars
   \/ WF_vars[DetectTermination]

(* Safety invariants *)
DetectImplyTermination ==
   [] (termDetected -> (\A i \in Node : ~active[i] /\ pending[i] = 0))

TerminationStable ==
   [] (termDetected -> UNCHANGED termDetected)

BoundInvariant ==
   [] (\A i \in Node : pending[i] <= MaxMsg)

(* Liveness property: actual termination leads to eventual detection *)
ActualToDetect ==
   [] ((\A i \in Node : ~active[i] /\ pending[i] = 0) -> <> termDetected)

THEOREM Safety == Spec => DetectImplyTermination
THEOREM Stability == Spec => TerminationStable
THEOREM Liveness == Spec => ActualToDetect
=============================================================================