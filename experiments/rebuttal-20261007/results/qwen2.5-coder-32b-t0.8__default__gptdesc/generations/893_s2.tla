---------------------------- MODULE HandshakeChannel ----------------------------

EXTENDS Naturals, TLC

CONSTANTS ValueDomain

VARIABLES ch

Init == /\ ch = [val |-> 0, rdy |-> 0, ack |-> 0]
        /\ val \in ValueDomain

Next ==
    \/ /\ ch.rdy = ch.ack
       /\ \/ \E v \in ValueDomain : ch' = [ch EXCEPT !.val = v, !.rdy = ~ch.rdy]
          \/ ch' = [ch EXCEPT !.rdy = ~ch.rdy]
    \/ /\ ch.rdy # ch.ack
       /\ ch' = [ch EXCEPT !.ack = ~ch.ack]

Spec ==
    Init /\ [][Next]_<<ch>>

TypeInvariant ==
    /\ ch.rdy \in {0, 1}
    /\ ch.ack \in {0, 1}
    /\ ch.val \in ValueDomain

Inv ==
    TypeInvariant

===============================================================================