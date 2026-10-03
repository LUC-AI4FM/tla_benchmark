---- MODULE Consensus ----
EXTENDS FiniteSets

CONSTANT Values
ASSUME Values # {}

VARIABLE chosen

\* The set of chosen values is initially empty.
Init == chosen = {}

\* An action where a value v is chosen.
\* This is only enabled when no value has yet been chosen.
Choose(v) == /\ chosen = {}
             /\ chosen' = {v}

\* The next-state relation allows choosing some value from the set Values,
\* if no value has been chosen yet.
Next == \E v \in Values : Choose(v)

\* The safety specification: the system starts in Init and always takes
\* a step allowed by Next or stutters.
Spec == Init /\ [][Next]_chosen

\* The safety property: at most one value is ever in the `chosen` set.
AtMostOneChosen == Cardinality(chosen) <= 1

\* An invariant-style theorem stating that the safety property always holds.
THEOREM Spec => []AtMostOneChosen

\* The full liveness specification, which adds a weak fairness requirement
\* on the Next action to the safety specification. This ensures that if it
\* is always possible to choose a value, a value is eventually chosen.
LiveSpec == Spec /\ WF_chosen(Next)

\* A liveness theorem stating that under the LiveSpec specification,
\* a value is eventually chosen.
THEOREM LiveSpec => <> (chosen # {})

====================