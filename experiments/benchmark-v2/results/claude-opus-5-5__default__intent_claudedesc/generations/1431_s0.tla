---- MODULE StateConstraintLivenessPitfall ----
EXTENDS Naturals, Sequences

CONSTANT MaxHistory

ASSUME MaxHistory \in Nat

VARIABLES state, history

vars == <<state, history>>

States == {"A", "B", "Done"}

TypeOK ==
    /\ state \in States
    /\ history \in Seq(States)

Init ==
    /\ state = "A"
    /\ history = <<>>

GoToB ==
    /\ state = "A"
    /\ state' = "B"
    /\ history' = Append(history, "A")

GoToA ==
    /\ state = "B"
    /\ state' = "A"
    /\ history' = Append(history, "B")

Next == GoToB \/ GoToA

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* State constraint (to be configured as CONSTRAINT in TLC).
\* It bounds the history log so that the state space is finite.
\* Because history grows on every step, every behavior is cut off,
\* so TLC never explores the infinite A->B->A->... cycle that
\* violates EventuallyDone.
HistoryConstraint == Len(history) <= MaxHistory

\* Safety invariant: the system never reaches Done.
NeverDone == state # "Done"

\* Liveness property: the system eventually reaches Done.
\* This is FALSE for Spec, since the system cycles between A and B
\* forever. With HistoryConstraint active, TLC may spuriously report
\* it as satisfied (or give misleading results), because the constraint
\* truncates every infinite behavior that would witness the violation.
EventuallyDone == <>(state = "Done")

\* Liveness property that genuinely holds: the system keeps alternating.
AlwaysEventuallyA == []<>(state = "A")
AlwaysEventuallyB == []<>(state = "B")

====