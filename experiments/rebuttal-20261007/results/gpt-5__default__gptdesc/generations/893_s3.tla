---- MODULE HandshakeChannel ----
EXTENDS Naturals

CONSTANT Values

VARIABLES ch

Bits == {0, 1}

TypeInv ==
  ch \in [ val: Values, rdy: Bits, ack: Bits ]

Init ==
  \E v \in Values:
    ch = [ val |-> v, rdy |-> 0, ack |-> 0 ]

Send ==
  /\ ch.rdy = ch.ack
  /\ \E v \in Values:
       ch' = [ ch EXCEPT !.rdy = 1 - @, !.val = v ]

Receive ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ ch EXCEPT !.ack = 1 - @ ]

Next == Send \/ Receive

Spec == Init /\ [][Next]_ch

THEOREM Spec => []TypeInv

====