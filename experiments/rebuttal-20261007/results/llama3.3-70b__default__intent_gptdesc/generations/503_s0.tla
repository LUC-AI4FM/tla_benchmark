```
MODULE Consensus
EXTENDS Integers, TLC

CONSTANTS Values
VARIABLES proposed, chosen

Init ==
  /\ proposed = {}
  /\ chosen = << >>

Next ==
  \/ \E v \in Values :
      /\ v \notin proposed
      /\ proposed' = proposed \cup {v}
      /\ chosen' = chosen
  \/ (chosen = << >>) /\ \E v \in proposed :
      /\ chosen' = << v >>
      /\ proposed' = proposed
  \/ chosen' = chosen
  /\ proposed' = proposed

Spec ==
  Init /\ [][Next]_<<proposed, chosen>>

Validity ==
  chosen \in {<< >>} \cup {<< v >> : v \in Values}

Agreement ==
  \A v1, v2 \in Values :
    ~ (<< v1 >> \in chosen) /\ (<< v2 >> \in chosen)

Integrity ==
  chosen' = chosen

EventualChoice ==
  <>(chosen # << >>)

NonTriviality ==
  proposed = {} => <>~(chosen = << >>)

Fairness == 
  SF_VARIABLES(proposed)
  WF_VARIABLES(chosen, proposed)

THEOREM Spec => []Validity
THEOREM Spec => []Agreement
THEOREM Spec => []Integrity
THEOREM Spec /\ Fairness => EventualChoice
THEOREM Spec /\ Fairness => NonTriviality
```