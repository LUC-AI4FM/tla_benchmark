------------------------------ MODULE M ------------------------------

EXTENDS Integers

CONSTANTS

Nodes == 0..2
Colors == {"white", "black"}

VARIABLES active, color, tpos, tcolor

vars == << active, color, tpos, tcolor >>

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Colors]
  /\ tpos \in Nodes
  /\ tcolor \in Colors

Init ==
  /\ active \in [{23, 42, 56} -> BOOLEAN]
  /\ color \in [Nodes -> Colors]
  /\ tpos \in Nodes
  /\ tcolor = "black"

Next ==
  /\ active' \in [{23, 42, 56} -> BOOLEAN]
  /\ color' \in [Nodes -> Colors]
  /\ tpos' \in Nodes
  /\ tcolor' = "black"

Spec == Init /\ [][Next]_vars

=============================================================================