```
MODULE SenderReceiver
EXTENDS Integers, FiniteSets
CONSTANTS Data
VARIABLES rdy, ack, val

Init == (rdy = ack) /\ (val \in Data)

Next == 
  \/ (\E d \in Data : (rdy = ack) /\ (val' = d) /\ (rdy' = ~rdy) /\ (ack' = ack))
  \/ ((rdy # ack) /\ (ack' = ~ack) /\ (val' = val) /\ (rdy' = rdy))

Spec == Init /\ [][Next]_<<rdy, ack, val>>
  
TypeInvariant == <<rdy, ack, val>> \in [BOOLEAN \X BOOLEAN \X Data]

THEOREM Spec => []TypeInvariant
```