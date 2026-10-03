------------------------------- MODULE AsyncSenderReceiver -------------------------------

CONSTANTS Data

VARIABLES rdy, ack, val

(*--algorithm AsyncSenderReceiver

variables rdy \in BOOLEAN,
          ack \in BOOLEAN,
          val \in Data;

Init == /\ rdy = FALSE
        /\ ack = FALSE
        /\ val \in Data

Send ==
    /\ rdy = ack
    /\ \/ \E v \in Data : val' = v
       /\ rdy' = ~rdy
       /\ ack' = ack

Rcv ==
    /\ rdy # ack
    /\ val' = val
    /\ rdy' = rdy
    /\ ack' = ~ack

Next == \/ Send
        \/ Rcv

Spec == Init /\ [][Next]_<<rdy, ack, val>>

TypeInvariant == /\ rdy \in BOOLEAN
                 /\ ack \in BOOLEAN
                 /\ val \in Data

THEOREM Spec => []TypeInvariant

end algorithm *)
=============================================================================