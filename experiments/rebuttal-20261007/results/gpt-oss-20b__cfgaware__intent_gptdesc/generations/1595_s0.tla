------------------------------ MODULE SingleProcessCounter ------------------------------
CONSTANT BOUND

VARIABLES c, procState

(* --------------------------------------------------------------------------- *)
(* State predicates and actions                                            *)
(* --------------------------------------------------------------------------- *)

Init ==
    /\ c = 0
    /\ procState = "running"

Inc ==
    /\ procState = "running"
    /\ c < BOUND
    /\ c' = c + 1
    /\ procState' = "running"

Terminate ==
    /\ procState = "running"
    /\ c >= BOUND
    /\ procState' = "terminated"
    /\ c' = c

Idle ==
    /\ procState = "terminated"
    /\ procState' = "terminated"
    /\ c' = c

Next == Inc \/ Terminate \/ Idle

(* --------------------------------------------------------------------------- *)
(* Temporal specification with fairness on the increment action             *)
(* --------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)

(* --------------------------------------------------------------------------- *)
(* Predicate that identifies the terminated state                           *)
(* --------------------------------------------------------------------------- *)

Termination ==
    /\ procState = "terminated"
    /\ c = BOUND

===============================================================================