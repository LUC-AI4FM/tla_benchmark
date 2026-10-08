---------------------------- MODULE SimpleStateMachine ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Colors

VARIABLES nodeAct, nodeCol, tokPos, tokCol

(* Type invariants *)
NodeActType == [n \in Nodes |-> BOOLEAN]
NodeColType == [n \in Nodes |-> Colors]

Init ==
  /\ nodeAct \in NodeActType
  /\ nodeCol \in NodeColType
  /\ tokPos \in Nodes
  /\ tokCol \in Colors

Next ==
  /\ nodeAct' \in NodeActType
  /\ nodeCol' \in NodeColType
  /\ tokPos' \in Nodes
  /\ tokCol' \in Colors

Spec == Init /\ [] (Next)

=============================================================================