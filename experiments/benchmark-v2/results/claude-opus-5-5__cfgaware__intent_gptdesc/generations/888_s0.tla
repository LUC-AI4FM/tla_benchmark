------------------------------ MODULE AsynchInterface ------------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack, written, rcvd

vars == <<val, rdy, ack, written, rcvd>>

DataVal == 0..1

NoVal == CHOOSE v : v \notin Data

Pending == rdy = ack + 1

TypeInvariant ==
    /\ val \in Data
    /\ rdy \in Nat
    /\ ack \in Nat
    /\ written \subseteq Data
    /\ rcvd \in Data \cup {NoVal}
    /\ ack <= rdy
    /\ rdy <= ack + 1

Init ==
    /\ val \in Data
    /\ rdy = 0
    /\ ack = 0
    /\ written = {}
    /\ rcvd = NoVal

Send ==
    /\ rdy = ack
    /\ \E d \in Data :
          /\ val' = d
          /\ written' = written \cup {d}
    /\ rdy' = rdy + 1
    /\ UNCHANGED <<ack, rcvd>>

Rcv ==
    /\ Pending
    /\ rcvd' = val
    /\ ack' = ack + 1
    /\ UNCHANGED <<val, rdy, written>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars /\ WF_vars(Send) /\ WF_vars(Rcv)

NoPhantomRead == rcvd # NoVal => rcvd \in written

CountersNonNeg == rdy \in Nat /\ ack \in Nat

ProducerOnlyChangesRdy == [][rdy' # rdy => Send]_vars

ConsumerOnlyChangesAck == [][ack' # ack => Rcv]_vars

CountersMonotone == [][rdy' >= rdy /\ ack' >= ack]_vars

EventualDelivery == \A n \in Nat : (rdy = n + 1) ~> (ack >= n + 1)

ProducerProgress == \A n \in Nat : (rdy = n) ~> (rdy > n)

ConsumerProgress == \A n \in Nat : (ack = n) ~> (ack > n)

HandshakeCompletes == Pending ~> ~Pending

StateBound == rdy <= 3
=============================================================================