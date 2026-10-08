------------------------------ MODULE Channel ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS DataSet

VARIABLE ch

(* Record fields: data, ready, ack *)

Init ==
  /\ ch.data \in DataSet
  /\ ch.ready = 0
  /\ ch.ack = 0

SenderAction ==
  /\ ch.ready = ch.ack
  /\ \E newData \in DataSet :
       /\ ch' = [ch EXCEPT !.data = newData,
                  !.ready = 1 - ch.ready]

ReceiverAction ==
  /\ ch.ready # ch.ack
  /\ ch' = [ch EXCEPT !.ack = 1 - ch.ack]

Next == SenderAction \/ ReceiverAction \/ Skip

TypeInvariant ==
  /\ ch.data \in DataSet
  /\ ch.ready \in {0,1}
  /\ ch.ack \in {0,1}

Spec == Init /\ [][Next]_<<ch>>

THEOREM TypeInvariantPreserved == []TypeInvariant
=============================================================================