------------------------------ MODULE RingTermination ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxPending
ASSUME N > 0 /\ MaxPending >= 0

NodeSet == 1..N
StatusVal == {"active", "inactive"}

VARIABLE status, pending, detection

(* Derived predicate: all nodes inactive and no pending messages *)
terminated == \A i \in NodeSet : status[i] = "inactive" /\ pending[i] = 0

Init ==
    /\ status \in [NodeSet -> StatusVal]
    /\ pending \in [NodeSet -> Nat]
    /\ detection \in BOOLEAN
    /\ status = [i \in NodeSet |-> "active"]
    /\ pending = [i \in NodeSet |-> 0]
    /\ detection = FALSE

SendMsg ==
    \E i, j \in NodeSet :
        /\ status[i] = "active"
        /\ pending' = [pending EXCEPT ![j] = @ + 1]
        /\ UNCHANGED <<status, detection>>

RecvMsg ==
    \E i \in NodeSet :
        /\ pending[i] > 0
        /\ pending' = [pending EXCEPT ![i] = @ - 1]
        /\ UNCHANGED <<status, detection>>

TerminateNodeAction ==
    \E i \in NodeSet :
        /\ status[i] = "active"
        /\ pending[i] = 0
        /\ status' = [status EXCEPT ![i] = "inactive"]
        /\ UNCHANGED <<pending, detection>>

DetectTermination ==
    /\ terminated
    /\ detection' = TRUE
    /\ UNCHANGED <<status, pending>>

Next == SendMsg \/ RecvMsg \/ TerminateNodeAction \/ DetectTermination

vars == <<status, pending, detection>>
Spec == Init /\ [][Next]_vars

(* Invariants *)
SafetyInvariant == [] (detection -> terminated)

TerminationStable == [] (detection -> detection)

PendingNonNegative == \A i \in NodeSet : pending[i] >= 0
BoundedPending      == \A i \in NodeSet : pending[i] <= MaxPending
AuxInvariants       == PendingNonNegative /\ BoundedPending

StateConstraint     == BoundedPending

(* Liveness property *)
LivenessProperty    == [] (terminated -> <> detection)

=============================================================================