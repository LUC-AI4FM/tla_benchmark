----------------------------- MODULE OnePlaceChannel -----------------------------
EXTENDS Naturals

CONSTANTS Val

VARIABLE ch

Bits == {0,1}

TypeOK == ch \in [val: Val, rdy: Bits, ack: Bits]

Init ==
  /\ TypeOK
  /\ ch.rdy = 0
  /\ ch.ack = 0

Send ==
  /\ ch.rdy = ch.ack
  /\ \E v \in Val:
        ch' = [ch EXCEPT !.val = v, !.rdy = 1 - @.rdy]

Receive ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT !.ack = 1 - @.ack]

Next == Send \/ Receive

Spec == Init /\ [][Next]_ch

THEOREM TypeInvariant == Spec => []TypeOK
=============================================================================