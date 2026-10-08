```
MODULE SenderReceiver
EXTENDS Integers, TLC
CONSTANTS Data
VARIABLES rdy, ack, val

Init == (rdy = ack) /\ (val \in Data)

Next == 
  \/ (rdy = ack) /\ (rdy' = ~rdy) /\ (ack' = ack) /\ (val' \in Data)
  \/ (rdy # ack) /\ (rdy' = rdy) /\ (ack' = ~ack) /\ (val' = val)

Spec == Init /\ [][Next]_<<rdy, ack, val>>
THEOREM Spec => []TypeInvariant
TypeInvariant == rdy \in BOOLEAN /\ ack \in BOOLEAN /\ val \in Data
```
Note: This TLA+ module assumes that `BOOLEAN` is defined as a set `{TRUE, FALSE}` and `~` denotes the logical NOT operator. Also, `TLC` is extended to provide the `Integers` module for integer constants and operators, although none are explicitly used in this example. The `_` in `[Next]_<<rdy, ack, val>>` is used to specify the variables that can change from one state to another according to the `Next` relation.