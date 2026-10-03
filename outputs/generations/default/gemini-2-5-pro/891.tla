---- MODULE Handshake ----
EXTENDS TLC

CONSTANTS Data

VARIABLES rdy, ack, val

vars == <<rdy, ack, val>>

TypeInvariant ==
    /\ rdy \in BOOLEAN
    /\ ack \in BOOLEAN
    /\ val \in Data

Init ==
    /\ rdy = FALSE
    /\ ack = FALSE
    /\ val \in Data

(* The sender may send a new value when the channel is ready. *)
Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = ~rdy
    /\ ack' = ack

(* The receiver may receive a value when one is available. *)
Rcv ==
    /\ rdy # ack
    /\ ack' = ~ack
    /\ UNCHANGED <<rdy, val>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant

=============================================================================