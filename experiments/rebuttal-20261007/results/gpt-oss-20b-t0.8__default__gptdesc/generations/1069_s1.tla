MODULE RingTermination
EXTENDS Naturals

CONSTANT N \in Nat  \* Number of nodes in the ring (N > 0)
CONSTANT MaxPending \in Nat  \* Upper bound on pending message count per node

(* --------------------------------------------------------------------------- *)
(* State variables *)
VARIABLES active, pending, terminated

(* --------------------------------------------------------------------------- *)
(* Helper definitions *)
Succ(i) == IF i = N THEN 1 ELSE i + 1

vars == <<active, pending, terminated>>

(* --------------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ active \in [1..N -> BOOLEAN]
    /\ pending \in [1..N -> Nat]
    /\ terminated = FALSE
    /\ \A i \in 1..N : pending[i] <= MaxPending

(* --------------------------------------------------------------------------- *)
(* Actions *)

Send(i) ==
    /\ i \in 1..N
    /\ active[i]
    /\ pending' = [pending EXCEPT ![Succ(i)] = @ + 1]
    /\ UNCHANGED <<active, terminated>>

Receive(i) ==
    /\ i \in 1..N
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED <<active, terminated>>

Terminate(i) ==
    /\ i \in 1..N
    /\ active[i]
    /\ pending[i] = 0
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, terminated>>

DetectTermination ==
    /\ (\A i \in 1..N : ~active[i] /\ pending[i] = 0)
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, pending>>

(* --------------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ \E i \in 1..N: Send(i)
    \/ \E i \in 1..N: Receive(i)
    \/ \E i \in 1..N: Terminate(i)
    \/ DetectTermination

(* --------------------------------------------------------------------------- *)
(* Safety invariants *)

InvDetectionImpliesNoActivity ==
    terminated => (\A i \in 1..N : ~active[i] /\ pending[i] = 0)

InvTerminationStable ==
    terminated => terminated'

BoundedInvariant ==
    \A i \in 1..N : pending[i] <= MaxPending

(* --------------------------------------------------------------------------- *)
(* Fairness condition *)

WF_DetectTermination == WF/DetectTermination

(* --------------------------------------------------------------------------- *)
(* Complete specification *)

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_DetectTermination
    /\ InvDetectionImpliesNoActivity
    /\ InvTerminationStable
    /\ BoundedInvariant

(* --------------------------------------------------------------------------- *)
(* End of module *)
===============================================================================