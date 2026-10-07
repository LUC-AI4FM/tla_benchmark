----------------------------- MODULE SimpleStateMachine -----------------------------

EXTENDS Naturals

CONSTANTS Nodes, Colors

ASSUME /\ Nodes = {"n1", "n2", "n3"}
       /\ Colors = {"red", "blue"}

VARIABLES Active, colorOf, tokenPos, tokenColor

vars == << Active, colorOf, tokenPos, tokenColor >>

TypeOK ==
  /\ Active \subseteq Nodes
  /\ colorOf \in [Nodes -> Colors]
  /\ tokenPos \in Nodes
  /\ tokenColor \in Colors

TokenConsistent == tokenColor = colorOf[tokenPos]

TypeOKPrime ==
  /\ Active' \subseteq Nodes
  /\ colorOf' \in [Nodes -> Colors]
  /\ tokenPos' \in Nodes
  /\ tokenColor' \in Colors

TokenConsistentPrime == tokenColor' = colorOf'[tokenPos']

Init ==
  /\ Active \subseteq Nodes
  /\ colorOf \in [Nodes -> Colors]
  /\ tokenPos \in Nodes
  /\ tokenColor = colorOf[tokenPos]

ToggleActive(n) ==
  /\ n \in Nodes
  /\ Active' = IF n \in Active THEN Active \ {n} ELSE Active \cup {n}
  /\ colorOf' = colorOf
  /\ tokenPos' = tokenPos
  /\ TokenConsistentPrime

RecolorNode(n, c) ==
  /\ n \in Nodes
  /\ c \in Colors
  /\ Active' = Active
  /\ colorOf' = [colorOf EXCEPT ![n] = c]
  /\ tokenPos' = tokenPos
  /\ TokenConsistentPrime

MoveToken(m) ==
  /\ m \in Nodes
  /\ Active' = Active
  /\ colorOf' = colorOf
  /\ tokenPos' = m
  /\ TokenConsistentPrime

ToggleAction == \E n \in Nodes: ToggleActive(n)
RecolorAction == \E n \in Nodes, c \in Colors: RecolorNode(n, c)
MoveAction == \E m \in Nodes: MoveToken(m)

Next ==
  /\ ToggleAction \/ RecolorAction \/ MoveAction
  /\ TypeOKPrime

Inv == TypeOK /\ TokenConsistent

Spec == Init /\ [][Next]_vars

=============================================================================