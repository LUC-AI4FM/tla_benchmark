------------------------------ MODULE SingleValueConsensus ------------------------------
EXTENDS TLC
DEADLOCKCHECKING := FALSE

CONSTANTS Candidates

VARIABLES chosen

vars == {chosen}

Init ==
  chosen = {}

Choose ==
  /\ chosen = {}
  /\ \E v \in Candidates : chosen' = {v}

Skip ==
  chosen' = chosen

Next ==
  Skip \/ Choose

SafetyInvariant ==
  chosen \subseteq Candidates
  /\ (#chosen <= 1)

Spec ==
  Init /\ [][Next]_vars

FairSpec ==
  Init /\ WF_vars(Choose) /\ [][Next]_vars

=============================================================================