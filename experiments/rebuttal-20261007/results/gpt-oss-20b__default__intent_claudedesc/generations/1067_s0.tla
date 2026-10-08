MODULE RingTermination

EXTENDS Naturals

CONSTANT N \in Nat

VARIABLES status, detected

(* Type of the status variable *)
StatusType == [1..N -> BOOLEAN]

(* Predicate: all nodes are inactive *)
AllInactive == \A i \in 1..N : ~status[i]

(* Actions *)

Deactivate(i) ==
    /\ i \in 1..N
    /\ status[i] = TRUE
    /\ status' = [status EXCEPT ![i] = FALSE]
    /\ detected' = detected

WakeUp(i,j) ==
    /\ i \in 1..N
    /\ j \in 1..N
    /\ i # j
    /\ status[i] = TRUE
    /\ status[j] = FALSE
    /\ status' = [status EXCEPT ![j] = TRUE]
    /\ detected' = detected

Detect ==
    /\ AllInactive
    /\ detected' = TRUE
    /\ status' = status

Next ==
    (\E i \in 1..N : Deactivate(i))
    \/ (\E i,j \in 1..N : WakeUp(i,j))
    \/ Detect

Init ==
    /\ status \in StatusType
    /\ detected = IF AllInactive THEN TRUE ELSE FALSE

(* Safety invariants *)
NoFalseDetection == detected => AllInactive

(* Stability property: once all nodes are inactive, they remain so *)
StabilityProperty == G(AllInactive -> X AllInactive)

(* Liveness property: termination is eventually reported *)
TerminationLiveness == G(AllInactive -> <> detected)

Spec ==
    Init /\ [][Next]_<<status, detected>> /\ WF_vars(Detect)

END MODULE