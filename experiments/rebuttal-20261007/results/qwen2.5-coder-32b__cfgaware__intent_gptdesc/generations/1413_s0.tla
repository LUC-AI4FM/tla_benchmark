------------------------------- MODULE PersistentTautologyDetector -------------------------------

CONSTANTS 
    \* The initial value of the immutable state component
    InitValue

VARIABLES 
    \* The single immutable state component
    State

\* Initial predicate that sets the initial state
Init == State = InitValue

\* Transition relation that forbids any state change
Next == TRUE /\ UNCHANGED State

\* Specification of the system behavior
Spec == Init /\ [][Next]_<<State>>

\* Theorem: If at any time the system can reach a state where AlwaysTrue holds, 
\* then there must exist a future point after which AlwaysTrue holds permanently.
THEOREM <>[](AlwaysTrue) => <><>[]AlwaysTrue

\* Define AlwaysTrue as an abstract proposition that always evaluates to TRUE
AlwaysTrue == TRUE

=============================================================================