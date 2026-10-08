---- MODULE SmallAlgorithm ----

EXTENDS TLC, Sequences, FiniteSets

CONSTANTS vars

VARIABLES x, y, pc

Init == 
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ x' = x \cup {"c"}
       /\ y' = <<y[1], 4>> @@ y[3..Len(y)]
       /\ pc' = "Done"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<x, y>>
       /\ pc' = "Done"

Spec ==
    Init /\ [][Next]_<<x, y, pc>>

Terminating ==
    <>[](pc = "Done")

====