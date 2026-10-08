MODULE OnePlaceChannel
EXTENDS Naturals

VARIABLES ch

Init ==
  /\ ch.rdy = 0
  /\ ch.ack = 0
  /\ ch.val = 0

Send ==
  /\ ch.rdy = ch.ack
  /\ \E newVal \in Nat :
     ch' = [ch EXCEPT !.val = newVal, !.rdy = 1 - ch.rdy]

Receive ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT !.ack = 1 - ch.ack]

Next == Send \/ Receive

TypeInvariant ==
  /\ ch.rdy \in {0,1}
  /\ ch.ack \in {0,1}
  /\ ch.val \in Nat

Spec == Init /\ [][Next]_ch

THEOREM InvariantPreserved : Spec => [](TypeInvariant)