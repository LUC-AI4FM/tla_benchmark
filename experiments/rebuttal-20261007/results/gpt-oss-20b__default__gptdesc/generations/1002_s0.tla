MODULE Barrier

EXTENDS Naturals, TLC

CONSTANT N

VARIABLES pc

ProcSet == 1 .. N

Init ==
  /\ pc \in [ProcSet -> {"b0","b1"}]
  /\ \A i \in ProcSet : pc[i] = "b0"

TypeInvariant ==
  /\ pc \in [ProcSet -> {"b0","b1"}]

Next ==
  ( \E i \in ProcSet :
      /\ pc[i] = "b0"
      /\ pc' = [pc EXCEPT ![i] = "b1"] )
  \/ ( (\A j \in ProcSet : pc[j] = "b1")
       /\ pc' = [pc EXCEPT ![j] = "b0" |-> j \in ProcSet] )

BarrierProperty ==
  [] ( (pc' = [pc EXCEPT ![j] = "b0" |-> j \in ProcSet]) -> (\A j : pc[j]="b1") )

Spec == Init /\ [][Next]_<<pc>> /\ TypeInvariant /\ BarrierProperty

===============================================================================