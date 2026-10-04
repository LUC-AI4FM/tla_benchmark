--------------------------- MODULE StateConstraintLivenessPitfall ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS A, B, Done

VARIABLES state, history

vars == <<state, history>>

TypeOK ==
    /\ state \in {A, B, Done}
    /\ history \in Seq({A, B, Done})

Init ==
    /\ state = A
    /\ history = <<A>>

\* The system cycles between A and B, never reaching Done
Next ==
    \/ /\ state = A
       /\ state' = B
       /\ history' = Append(history, B)
    \/ /\ state = B
       /\ state' = A
       /\ history' = Append(history, A)

\* This action would transition to Done, but it's never enabled
\* because the system only cycles between A and B
GotoDone ==
    /\ state = Done
    /\ state' = Done
    /\ history' = history

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* State constraint to bound the history length for tractable model checking
\* When this constraint is active, it cuts off infinite behaviors after
\* the history reaches a certain length
StateConstraint == Len(history) <= 5

\* Liveness property: the system eventually reaches Done
\* This property is FALSE in the actual system (Done is never reached)
\* but will SPURIOUSLY PASS when StateConstraint is active because
\* the constraint eliminates all infinite behaviors that would
\* serve as counterexamples
EventuallyDone == <>(state = Done)

\* This invariant is always true - we never reach Done
NeverDone == state # Done

\* Helper: the system keeps making progress (always true with fairness)
AlwaysProgress == []<>(state = A) /\ []<>(state = B)

=============================================================================