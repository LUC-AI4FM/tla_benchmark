----------------------------- MODULE SingleValueConsensus -----------------------------
EXTENDS Naturals

CONSTANT Values

VARIABLE chosen

Init ==
  chosen = {}

Next ==
  /\ chosen = {}
  /\ ∃ v ∈ Values: chosen' = {v}

vars == << chosen >>

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  chosen ⊆ Values

AtMostOne(S) ==
  S = {} \/ (∃ v ∈ Values: S = {v})

Inv ==
  /\ TypeOK
  /\ AtMostOne(chosen)

THEOREM Spec => []Inv

LiveSpec ==
  Spec /\ WF_vars(Next)

THEOREM (Values # {}) /\ LiveSpec => <> (chosen # {})

=============================================================================