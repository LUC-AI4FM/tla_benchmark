MODULE M
EXTENDS Integers

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. 2
ColorSet == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> ColorSet]
  /\ tpos \in Nodes
  /\ tcolor \in ColorSet

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> ColorSet]
  /\ tpos \in Nodes
  /\ tcolor = "black"
  /\ \A n \in {23,42,56} : IF n \in DOMAIN active THEN active[n] \in BOOLEAN ELSE TRUE

Next ==
  /\ active' \in [Nodes -> BOOLEAN]
  /\ color' \in [Nodes -> ColorSet]
  /\ tpos' \in Nodes
  /\ tcolor' = "black"
  /\ \A n \in {23,42,56} : IF n \in DOMAIN active THEN active[n] \in BOOLEAN ELSE TRUE

vars == <<active, color, tpos, tcolor>>

Spec == Init /\ [][Next]_vars