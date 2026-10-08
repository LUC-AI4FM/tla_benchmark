---------------------------- MODULE Channel ----------------------------

CONSTANT Data

VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

TypeInvariant == 
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}

Init ==
    /\ val \in Data
    /\ rdy = 0
    /\ ack = 0

Send ==
    /\ rdy = ack
    /\ \E d \in Data:
        /\ val' = d
        /\ rdy' = 1 - rdy
        /\ ack' = ack

Receive ==
    /\ rdy # ack
    /\ ack' = rdy
    /\ val' = val
    /\ rdy' = rdy

Next == Send \/ Receive

Spec == Init /\ [][Next]_vars

HandshakeInvariant ==
    /\ (rdy = ack) => (ENABLED Send)
    /\ (rdy # ack) => (ENABLED Receive)

NoOverwrite ==
    [][rdy # ack => val' = val \/ ack' = rdy]_vars

SafeAck ==
    [][ack' # ack => rdy # ack]_vars

THEOREM TypePreservation == Spec => []TypeInvariant

THEOREM HandshakeSafety == Spec => [](TypeInvariant /\ (rdy \in {0,1}) /\ (ack \in {0,1}))

=============================================================================