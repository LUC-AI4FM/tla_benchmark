---- MODULE HandshakeChannel ----
EXTENDS Naturals

VARIABLES ch

Bits == {0, 1}

Channel == [val: Nat, rdy: Bits, ack: Bits]

TypeInvariant == ch \in Channel

Init ==
  ch = [val |-> 0, rdy |-> 0, ack |-> 0]

Send ==
  /\ ch.rdy = ch.ack
  /\ \E v \in Nat:
       ch' = [ch EXCEPT !.val = v, !.rdy = 1 - @]

Receive ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT !.ack = 1 - @]

Next ==
  Send \/ Receive

Spec ==
  Init /\ [][Next]_ch

THEOREM Spec => []TypeInvariant
====