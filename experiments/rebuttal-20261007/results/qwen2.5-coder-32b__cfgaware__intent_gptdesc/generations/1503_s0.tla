------------------------------- MODULE SimpleStateModel -------------------------------

CONSTANTS
    UNIVERSE,          \* The set of all possible integer values.
    THRESHOLD,         \* The numeric threshold for the predicate.
    BOOLEAN_CONDITION  \* The additional Boolean condition.

VARIABLES state

Init == 
    /\ state \in UNIVERSE
    /\ state > THRESHOLD
    /\ BOOLEAN_CONDITION[state]

Next ==
    TRUE

Spec == Init /\ [][Next]_<<state>>

\* Correctness properties
TypeOK ==
    \/ ~(\E s \in UNIVERSE : s > THRESHOLD /\ BOOLEAN_CONDITION[s])
    \/ (\A s \in StateTrace : s \in UNIVERSE /\ s > THRESHOLD /\ BOOLEAN_CONDITION[s])

StateTrace == {s \in SUBSET Seq(UNIVERSE) : Init /\ A_(0..Len(s)-2) : Next}

THEOREM Spec => TypeOK

=============================================================================