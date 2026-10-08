------------------------------ MODULE BinaryStable ------------------------------

VARIABLES x

Init ==
  ∃ b ∈ {0, 1} : x = b /\ x < 1

Next ==
  UNCHANGED x

Spec ==
  Init /\ [][Next]_x

TypeOK ==
  x ∈ {0, 1}

Inv ==
  x < 1

NoChange ==
  [](x' = x)

===============================================================================