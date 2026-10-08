```
MODULE SimpleSenderReceiver
EXTENDS Integers, FiniteSets
CONSTANTS Data
VARIABLES rdy, ack, val

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val \in Data

Next ==
  \/ (rdy = ack) /\ E v \in Data : 
      /\ val' = v
      /\ rdy' = ~rdy
      /\ ack' = ack
  \/ (rdy # ack) /\ 
      /\ ack' = ~ack
      /\ val' = val
      /\ rdy' = rdy
  \/ UNCHANGED <<rdy, ack, val>>

Spec == Init /\ [][Next]_<<rdy, ack, val>>
TypeInvariant == rdy \in BOOLEAN /\ ack \in BOOLEAN /\ val \in Data

THEOREM Spec => []TypeInvariant
```