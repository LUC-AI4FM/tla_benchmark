---------------------------- MODULE AlternatingHistory ----------------------------
EXTENDS Naturals, Sequences

CONSTANT MaxHistoryLen

ASSUME MaxHistoryLen \in Nat

VARIABLES pc, history

vars == <<pc, history>>

TypeOK ==
    /\ pc \in {"A", "B", "Done"}
    /\ history \in Seq({"A", "B", "Done"})

Init ==
    /\ pc = "A"
    /\ history = <<>>

A ==
    /\ pc = "A"
    /\ pc' = "B"
    /\ history' = Append(history, pc)

B ==
    /\ pc = "B"
    /\ pc' = "A"
    /\ UNCHANGED history

Next == A \/ B

Spec ==
    /\ Init
    /\ [][A \/ B]_vars
    /\ WF_vars(A \/ B)

\* State constraint bounding the length of the history sequence
StateConstraint == Len(history) <= MaxHistoryLen

\* Safety: every recorded entry in history is a visit to state "A"
HistoryOnlyA == \A i \in 1..Len(history) : history[i] = "A"

\* Liveness: pc eventually becomes "Done" (unreachable in this model, so it is violated)
EventuallyDone == <>(pc = "Done")

====================================================================================