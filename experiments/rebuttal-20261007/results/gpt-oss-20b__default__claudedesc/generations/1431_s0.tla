MODULE TwoStateHistory

EXTENDS Sequences

VARIABLES pc, history

Init == /\ pc = "A"
        /\ history = <<>>

ActionA == /\ pc = "A"
           /\ pc' = "B"
           /\ history' = Append(history, pc)

ActionB == /\ pc = "B"
           /\ pc' = "A"
           /\ UNCHANGED history

Next == ActionA \/ ActionB

Spec == Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

Constraint == Len(history) < 3

Prop == <> (pc = "Done")