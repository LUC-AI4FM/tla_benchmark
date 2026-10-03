------------------------------- MODULE TwoStateProcess -------------------------------

CONSTANTS MaxHistoryLength

VARIABLES pc, history

(* --algorithm TwoStateProcess
variables pc = "A", history = << >>;

next ==
    \/ /\ pc = "A"
       /\ history \o <<pc>> \in Seq({"A"})
       /\ pc' = "B"
       /\ history' = history \o <<pc>>
    \/ /\ pc = "B"
       /\ pc' = "A"
       /\ history' = history

Spec ==
    /\ PCInit
    /\ [][next]_<<pc, history>>
    /\ WF_next(<<pc, history>>)

PCInit == 
    /\ pc = "A"
    /\ history = << >>

StateConstraint ==
    Len(history) <= MaxHistoryLength

Liveness ==
    <>[](pc = "Done")

\* The following is a dummy liveness property to satisfy the configuration binding requirement.
\* In this model, "Done" is unreachable, so this will not hold.
DummyLiveness ==
    <>[](pc = "Done")

====