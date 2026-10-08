------------------------------- MODULE SimpleStateModel -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    UNIVERSE,          \* The set of all possible integer values
    THRESHOLD,         \* The numeric threshold for the predicate
    BOOLEAN_CONDITION  \* The additional Boolean condition

VARIABLES state

Init == \/ /\ state \in UNIVERSE
        /\ state > THRESHOLD
        /\ BOOLEAN_CONDITION[state]
      \/ CHOOSE s \in {s \in UNIVERSE : s > THRESHOLD /\ BOOLEAN_CONDITION[s]}

Next == TRUE  \* No further state changes after initialization

Spec == Init /\ [][Next]_<<state>>

\* Safety properties
TypeOK == state \in UNIVERSE
ValueOK == state > THRESHOLD
BooleanOK == BOOLEAN_CONDITION[state]

Safety == TypeOK /\ ValueOK /\ BooleanOK

\* Liveness property (trivially satisfied)
Persistence == [](state = state)

\* Assert that at least one allowed value exists
InitSatisfiable == \E s \in UNIVERSE : s > THRESHOLD /\ BOOLEAN_CONDITION[s]

=============================================================================