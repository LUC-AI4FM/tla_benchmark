---------------------------- MODULE FiniteStateMapping ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Indices          \* abstract finite domain of the mapping

ASSUME IndicesAssumption ==
    /\ IsFiniteSet(Indices)
    /\ Cardinality(Indices) >= 3

VARIABLES state,           \* the single integer-valued state
          mapping          \* abstract total function Indices -> Values

vars == <<state, mapping>>

Values == 1..5

-----------------------------------------------------------------------------------
\* Type correctness
TypeOK ==
    /\ state \in Values
    /\ mapping \in [Indices -> Values]

\* Coverage condition: some index maps exactly to the current state
Covers(s, m) == \E i \in Indices : m[i] = s

-----------------------------------------------------------------------------------
\* Initial condition: arbitrary state from the finite set, together with
\* some abstract total mapping that covers it.
Init ==
    /\ state \in Values
    /\ mapping \in [Indices -> Values]
    /\ Covers(state, mapping)

\* Arbitrary step: the state may move to any value in Values, including
\* keeping its current value. The abstract mapping is chosen
\* nondeterministically, subject only to remaining total over Indices and
\* covering the new state.
Step ==
    /\ state' \in Values
    /\ mapping' \in [Indices -> Values]
    /\ Covers(state', mapping')

\* Explicit option to keep the state unchanged
Stay ==
    /\ state' = state
    /\ mapping' \in [Indices -> Values]
    /\ Covers(state', mapping')

Next == Step \/ Stay

\* Weak fairness ensures the system keeps taking steps
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------------
\* Safety invariants
StateInRange == state \in Values

MappingInvariant == \E i \in Indices : mapping[i] = state

Inv == TypeOK /\ StateInRange /\ MappingInvariant

\* Liveness / non-deadlock: a transition is always enabled
NoDeadlock == []ENABLED Next

\* The system keeps making progress (steps occur infinitely often)
Progress == []<><<Next>>_vars \/ []<>(ENABLED Next)

-----------------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => NoDeadlock
===================================================================================