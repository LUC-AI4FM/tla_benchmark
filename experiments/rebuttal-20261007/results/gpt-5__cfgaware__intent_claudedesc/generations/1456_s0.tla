------------------------------ MODULE SubsetEnabledPossible ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, u

S2 == {0, 1}
S3 == {0, 1, 2}
vars == << x, u >>

Init ==
  /\ u = S3
  /\ x \subseteq S2

Next ==
  /\ u' = u
  /\ x' \subseteq u

TypeOK ==
  /\ x \subseteq S3
  /\ u = S3

Inv ==
  /\ x \subseteq S3
  /\ ENABLED (Next /\ x' \subseteq {2})

Spec == Init /\ [][Next]_vars

FullSet_POSSIBLE ==
  x = S3

Gain2_POSSIBLE ==
  /\ Next
  /\ ~(2 \in x)
  /\  2 \in x'

Post ==
  /\ FullSet_POSSIBLE = 1
  /\ Gain2_POSSIBLE = 16
=============================================================================