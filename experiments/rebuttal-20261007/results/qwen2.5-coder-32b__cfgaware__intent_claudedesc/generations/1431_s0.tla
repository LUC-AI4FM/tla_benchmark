------------------------------- MODULE StateConstraintPitfall -------------------------------

CONSTANTS MaxHistoryLength

VARIABLES state, history

(*--algorithm StateCycle
variables state = "A", history = << >>;

next ==
    \/ /\ state = "A"
       /\ state' = "B"
       /\ history' = Append(history, "A")
    \/ /\ state = "B"
       /\ state' = "A"
       /\ history' = Append(history, "B")

Spec == 
    /\ Init
    /\ [][next]_<<state, history>>
    /\ WF_next(<<state, history>>)

Init ==
    /\ state = "A"
    /\ history = << >>

WF_next(vars) == WFair({s \in vars : s.state # "Done"})

StateConstraint ==
    Len(history) <= MaxHistoryLength

SpecWithConstraint ==
    Spec /\ StateConstraint

(*--fairness
WF_next(<<state, history>>)

====