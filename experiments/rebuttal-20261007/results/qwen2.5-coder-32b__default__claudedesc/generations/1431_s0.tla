------------------------------- MODULE TwoStateSystem -------------------------------
EXTENDS TLC, Sequences

CONSTANTS 
    MaxHistorySize

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = << >>

Next ==
    \/  /\ pc = "A"
        /\ pc' = "B"
        /\ history' = Append(history, "A")
    \/  /\ pc = "B"
        /\ pc' = "A"
        /\ history' = history

Constraint == Len(history) < MaxHistorySize

Spec == Init /\ [][Next]_<<pc, history>> /\ WF_[Next]_<<pc, history>>

Prop == <>[](pc = "Done")

=============================================================================