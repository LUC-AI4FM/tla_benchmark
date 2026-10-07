----------------------------- MODULE OnePlaceChannel -----------------------------

EXTENDS Naturals

CONSTANT Val

VARIABLES ch

Bits == {0, 1}

Flip(b) == IF b = 0 THEN 1 ELSE 0

TypeInv == ch \in [val: Val, rdy: Bits, ack: Bits]

Init ==
  /\ TypeInv
  /\ ch.rdy = 0
  /\ ch.ack = 0

Send(v) ==
  /\ v \in Val
  /\ ch.rdy = ch.ack
  /\ ch' = [ch EXCEPT !.val = v, !.rdy = Flip(@)]

Rcv ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT !.ack = Flip(@)]

Next ==
  (∃ v \in Val: Send(v)) \/ Rcv

Spec ==
  Init /\ [][Next]_ch

THEOREM SpecTypeInvariant == Spec => []TypeInv

=============================================================================