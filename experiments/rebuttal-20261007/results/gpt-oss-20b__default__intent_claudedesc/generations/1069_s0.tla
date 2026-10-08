MODULE RingTermination
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxPending

(* ------------------------------------------------------------------ *)
(* Types and helper predicates *)

NodeSet == 1..N

StateType == [i \in NodeSet -> {"active", "inactive"}]

AllInactive(s) == \A i \in NodeSet : s[i] = "inactive"

Terminated(s,p) == AllInactive(s) /\ \A i \in NodeSet : p[i] = 0

BoundedPending(p) == \A i \in NodeSet : p[i] <= MaxPending

(* ------------------------------------------------------------------ *)
(* Variables *)

VARIABLES state, pending, flag

(* ------------------------------------------------------------------ *)
(* Initial condition *)

Init ==
    /\ state \in StateType
    /\ pending \in [NodeSet -> Nat]
    /\ BoundedPending(pending)
    /\ pending = [i \in NodeSet |-> 0]
    /\ IF AllInactive(state) THEN flag \in BOOLEAN ELSE flag = FALSE

(* ------------------------------------------------------------------ *)
(* Actions *)

Send(i,j) ==
    /\ i \in NodeSet
    /\ j \in NodeSet
    /\ state[i] = "active"
    /\ pending[j] < MaxPending
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED <<state, flag>>

Deactivate(i) ==
    /\ i \in NodeSet
    /\ state[i] = "active"
    /\ state' = [state EXCEPT ![i] = "inactive"]
    /\ UNCHANGED <<pending, flag>>

Receive(i) ==
    /\ i \in NodeSet
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ state' = [state EXCEPT ![i] = "active"]
    /\ UNCHANGED flag

Detect ==
    /\ Terminated(state, pending)
    /\ flag' = TRUE
    /\ UNCHANGED <<state, pending>>

(* ------------------------------------------------------------------ *)
(* Next-state relation *)

Next ==
    IF flag = TRUE THEN
        Detect
    ELSE
        \/ \E i,j \in NodeSet : Send(i,j)
        \/ \E i \in NodeSet : Deactivate(i)
        \/ \E i \in NodeSet : Receive(i)
        \/ Detect

(* ------------------------------------------------------------------ *)
(* Specification *)

Spec == Init /\ [][Next]_<<state, pending, flag>>

(* ------------------------------------------------------------------ *)
(* Invariants *)

FlagInvariant ==
    (flag = FALSE) \/ Terminated(state, pending)

BoundedPendingInv ==
    BoundedPending(pending)

(* ------------------------------------------------------------------ *)
(* Liveness property: eventual detection of termination *)

TerminationDetected == [](Terminated(state, pending) => <> (flag = TRUE))

(* ------------------------------------------------------------------ *)