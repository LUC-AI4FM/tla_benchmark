------------------------------ MODULE RingTerminationDetection ------------------------------
EXTENDS Naturals

CONSTANT N \* Number of nodes in the ring (must be a positive integer)

VARIABLES state, detected

(* --------------------------------------------------------------------------- *)
(*  State representation:  state[i] = TRUE  ⇔ node i is active; FALSE ⇔ inactive   *)
(* --------------------------------------------------------------------------- *)

AllInactive == ∀k ∈ 1..N : state[k] = FALSE

(* --------------------------------------------------------------------------- *)
(*  Initial condition: any combination of active/inactive nodes.               *)
(*  The termination flag may be set only if all nodes are already inactive.    *)
(* --------------------------------------------------------------------------- *)
Init ==
    /\ state \in [1..N -> BOOLEAN]
    /\ (detected => AllInactive)

(* --------------------------------------------------------------------------- *)
(*  Actions that change the system state.                                      *)
(* --------------------------------------------------------------------------- *)

Deactivate(i) ==
    /\ i ∈ 1..N
    /\ state[i] = TRUE
    /\ state' = [state EXCEPT ![i] = FALSE]
    /\ detected' = detected

WakeUp(i, j) ==
    /\ i ∈ 1..N
    /\ j ∈ 1..N
    /\ i # j
    /\ state[i] = TRUE
    /\ state' = [state EXCEPT ![j] = TRUE]
    /\ detected' = detected

Detect ==
    /\ AllInactive
    /\ ~detected
    /\ state' = state
    /\ detected' = TRUE

Next == \/ ∃i ∈ 1..N : Deactivate(i)
        \/ ∃i,j ∈ 1..N : i # j /\ WakeUp(i, j)
        \/ Detect

vars == <<state, detected>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Detect)

(* --------------------------------------------------------------------------- *)
(*  Safety properties.                                                        *)
(* --------------------------------------------------------------------------- *)

TerminationFalseReport == detected => AllInactive
StableTermination      == [] (AllInactive -> [] AllInactive)

(* --------------------------------------------------------------------------- *)
(*  Liveness property.                                                       *)
(* --------------------------------------------------------------------------- *)

TerminationEventuallyDetected ==
    [](AllInactive /\ ~detected -> <> detected)

THEOREM TerminationFalseReportIsInvariant == Spec => [] TerminationFalseReport
THEOREM StableTerminationIsInvariant      == Spec => StableTermination
THEOREM TerminationEventuallyDetectedHolds == Spec => TerminationEventuallyDetected

===============================================================================