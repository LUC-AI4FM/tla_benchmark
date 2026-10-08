------------------------------- MODULE TwoStateSystem -------------------------------

CONSTANTS pc, history

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = << >>

A == /\ pc = "A"
     /\ pc' = "B"
     /\ history' = Append(history, pc)

B == /\ pc = "B"
     /\ pc' = "A"
     /\ history' = history

Next == A \/ B

Spec == Init /\ [][Next]_<<pc, history>> /\ WF_next(Next)

Constraint == Len(history) < 3

Prop == <>[](pc = "Done")

WF_next(action) == << \E s \in S: action >>_s

=============================================================================