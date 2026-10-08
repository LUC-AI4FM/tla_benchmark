```
MODULE SenderReceiver
EXTENDS Integers, TLC

CONSTANTS Data

VARIABLES rdy, ack, val

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val \in Data

Next ==
  \/ (\* Send \*)
      (rdy = ack)
      /\ rdy' = ~rdy
      /\ ack' = ack
      /\ val' \in Data
  \/ (\* Rcv \*)
      (rdy # ack)
      /\ rdy' = rdy
      /\ ack' = ~ack
      /\ val' = val
  \/ (\* stuttering \*)
      rdy' = rdy
      /\ ack' = ack
      /\ val' = val

Spec == Init /\ [][Next]_<<rdy, ack, val>>
           /\ WF_rdy(Next) /\ SF_rdy(Next)

TypeInvariant == /\ rdy \in BOOLEAN
                 /\ ack \in BOOLEAN
                 /\ val \in Data

THEOREM Spec => []TypeInvariant
```