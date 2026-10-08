----------------------------- MODULE SubsetPrimedNext -----------------------------

VARIABLES x, y

Init ==
  /\ x \subseteq {1, 2}
  /\ y = {1, 2, 3}

Next ==
  /\ y' = y
  /\ x' \subseteq y'

TypeOK ==
  x \subseteq {1, 2, 3}

Inv ==
  /\ ENABLED (x' \subseteq {1})
  /\ y = {1, 2, 3}

=============================================================================