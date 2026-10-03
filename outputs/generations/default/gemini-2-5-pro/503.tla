---- MODULE AbstractConsensus ----
EXTENDS Integers, FiniteSets

CONSTANTS Values
ASSUME Values /= {}  \* Assume there is at least one value that can be chosen.

VARIABLES chosen

vars == <<chosen>>

\* Type invariant: the chosen set is always a subset of the possible values.
TypeOK == chosen \subseteq Values

\* The key safety property: at most one value is ever chosen.
AtMostOneValueChosen == Cardinality(chosen) <= 1

\* The complete safety invariant.
Invariant == TypeOK /\ AtMostOneValueChosen

\* Initially, no value has been chosen.
Init == chosen = {}

\* The action of choosing a value v. This is enabled only when no value
\* has yet been chosen.
Choose(v) == /\ chosen = {}
             /\ chosen' = {v}

\* The next-state relation. A value v from Values is non-deterministically
\* chosen. If a value has already been chosen, this action is disabled.
Next == \E v \in Values: Choose(v)

\* The safety specification. It allows the system to take a Next step or to
\* stutter (do nothing) if no Next step is enabled.
Spec == Init /\ [][Next]_vars

\* This theorem states that the safety invariant always holds for any behavior
\* allowed by the safety specification.
THEOREM Spec => []Invariant

\* The liveness specification adds a weak fairness requirement on the Next action.
\* This ensures that if it is always possible to take a step (i.e., if no
\* value has been chosen), a step must eventually be taken.
LiveSpec == Spec /\ WF_vars(Next)

\* The liveness property: eventually, some value is chosen.
EventuallyAValueIsChosen == <>(chosen /= {})

\* This theorem states that for any behavior satisfying the liveness
\* specification, a value is eventually chosen.
THEOREM LiveSpec => EventuallyAValueIsChosen

=============================================================================