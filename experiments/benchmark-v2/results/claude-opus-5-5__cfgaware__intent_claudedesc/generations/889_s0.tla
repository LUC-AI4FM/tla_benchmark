---------------------------- MODULE AsynchInterface ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

DataVal == {0, 1, 2}

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

ProtocolIntegrity == [][ (rdy' # rdy => rdy = ack) /\ (ack' # ack => rdy # ack) ]_vars

DataStable == [][ (rdy = ack /\ ack' # ack) => FALSE ]_vars

NoDataChangeWhilePending == [][ (rdy # ack) => UNCHANGED val ]_vars

=============================================================================