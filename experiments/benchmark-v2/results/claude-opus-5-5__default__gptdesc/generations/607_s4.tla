------------------------------- MODULE MC -------------------------------
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Single-user component specification (the per-user view).               *)
(***************************************************************************)
---------------------------- MODULE SingleUser ----------------------------
CONSTANT User
VARIABLE state

States == {"idle", "waiting", "using"}

TypeOK == state \in States

Init == state = "idle"

Request == /\ state = "idle"
           /\ state' = "waiting"

Enter   == /\ state = "waiting"
           /\ state' = "using"

Exit    == /\ state = "using"
           /\ state' = "idle"

Next == Request \/ Enter \/ Exit

Spec == Init /\ [][Next]_state /\ WF_state(Next)
===========================================================================