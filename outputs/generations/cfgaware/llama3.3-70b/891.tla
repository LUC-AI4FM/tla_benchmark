---------------------------- MODULE SenderReceiver ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Data

VARIABLE rdy, ack, val

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val \in Data

Next ==
  \/ /\ rdy = ack
     /\ val' \in Data
     /\ rdy' = ~rdy
     /\ ack' = ack
  \/ /\ rdy # ack
     /\ rdy' = rdy
     /\ ack' = ~ack
     /\ val' = val
  \/ UNCHANGED <<rdy, ack, val>>

Spec ==
  Init /\ [][Next]_<<rdy, ack, val>>

TypeInvariant ==
  /\ rdy \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ val \in Data

THEOREM Spec => []TypeInvariant
=============================================================================