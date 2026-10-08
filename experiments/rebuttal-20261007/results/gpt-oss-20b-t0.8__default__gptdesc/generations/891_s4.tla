MODULE AsyncSenderReceiver

CONSTANT Data

VARIABLES rdy, ack, val

TypeInv == 
  /\ rdy \in {TRUE, FALSE}
  /\ ack \in {TRUE, FALSE}
  /\ val \in Data

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val \in Data

Send ==
  /\ rdy = ack
  /\ val' \in Data
  /\ rdy' = ~rdy
  /\ ack' = ack

Rcv ==
  /\ rdy # ack
  /\ rdy' = rdy
  /\ ack' = ~ack
  /\ val' = val

Stutter ==
  /\ rdy' = rdy
  /\ ack' = ack
  /\ val' = val

Next == Send \/ Rcv

Spec == Init /\ [] (Next \/ Stutter)

THEOREM Spec => [] TypeInv