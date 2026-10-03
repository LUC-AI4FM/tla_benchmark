---- MODULE TwoStateProcess ----
EXTENDS Sequences, TLC

VARIABLES pc, history

vars == <<pc, history>>

TypeOK ==
    /\ pc \in {"A", "B"}
    /\ history \in Seq({"A"})

Init ==
    /\ pc = "A"
    /\ history = <<>>

A ==
    /\ pc = "A"
    /\ pc' = "B"
    /\ history' = Append(history, "A")

B ==
    /\ pc = "B"
    /\ pc' = "A"
    /\ UNCHANGED history

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A \/ B)

\* A state constraint limiting the history length.
\* A concrete value like 10 could be used in a model checking configuration file.
CONSTANTS MaxHistoryLength
ASSUME MaxHistoryLength \in Nat

HistoryLengthLimit == Len(history) <= MaxHistoryLength

\* A liveness property asserting that pc eventually becomes "Done".
\* This property is expected to be violated as "Done" is an unreachable state.
EventuallyDone == <> (pc = "Done")

=============================================================================