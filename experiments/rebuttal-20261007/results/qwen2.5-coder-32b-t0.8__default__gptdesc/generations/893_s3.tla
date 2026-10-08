---- MODULE CommunicationChannel ----

EXTENDS Integers, TLC

CONSTANTS 
    \* No constants are needed for this specification

VARIABLES 
    ch  \* ch is a record with fields val, rdy, ack

Init == /\ ch = [val |-> 0, rdy |-> 0, ack |-> 0]

Next == \/ /\ ch.rdy = ch.ack
           /\ \/ \E v \in Integers : ch' = [ch EXCEPT !.rdy = 1 - ch.rdy, !.val = v]
              /\ ch'.ack = ch.ack
       \/ /\ ch.rdy # ch.ack
          /\ ch'.ack = 1 - ch.ack
          /\ ch'.rdy = ch.rdy
          /\ ch'.val = ch.val

Spec == SpecInit <> Init /\ [][Next]_<<ch>>

TypeInvariant == /\ ch.rdy \in {0, 1}
                 /\ ch.ack \in {0, 1}

Inv == TypeInvariant

\* Fairness conditions can be added if needed
Fairness == WF_next(Next)

====