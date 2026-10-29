---------------------------- MODULE EWD840Abstract ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor \in Color

-----------------------------------------------------------------------------

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor \in Color
  /\ tpos = N-1
  /\ tcolor = "black"

Next ==
  /\ active' \in [Nodes -> BOOLEAN]
  /\ color' \in [Nodes -> Color]
  /\ tpos' \in Nodes
  /\ tcolor' \in Color
  /\ \/ /\ tpos' = tpos
        /\ tcolor' = tcolor
     \/ /\ tpos # 0
        /\ tpos' = tpos - 1
     \/ /\ tpos = 0
        /\ tpos' = N-1
        /\ tcolor' = "white"

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM TypeCorrect == Spec => []TypeOK

=============================================================================