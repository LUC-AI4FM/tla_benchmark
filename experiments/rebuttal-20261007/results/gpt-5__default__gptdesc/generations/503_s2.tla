---- MODULE SingleValueConsensus ----
EXTENDS Naturals

CONSTANT Values

ASSUME Values # {}

VARIABLE chosen

vars == << chosen >>

Init ==
  chosen = {}

Next ==
  /\ chosen = {}
  /\ \E v \in Values : chosen' = {v}

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  chosen \subseteq Values

AtMostOneChosen ==
  chosen = {} \/ (\E v \in Values : chosen = {v})

Invariant ==
  TypeOK /\ AtMostOneChosen

THEOREM SafetyInvariant ==
  Spec => []Invariant

EventuallyChosen ==
  <> (chosen # {})

SpecWF ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Liveness ==
  SpecWF => EventuallyChosen
====