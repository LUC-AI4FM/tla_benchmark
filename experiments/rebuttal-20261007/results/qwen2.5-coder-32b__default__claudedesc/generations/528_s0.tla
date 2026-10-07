------------------------------- MODULE SimpleAlgorithm -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    \* No constants defined in the description

VARIABLES x, y, pc

Init == /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
             /\ x' = x \cup {"c"}
             /\ y' = [y EXCEPT ![1] = 4]
             /\ pc' = "Done"
             /\ PrintT(x')
             /\ PrintT(y')
          \/ /\ pc = "Done"
             /\ UNCHANGED <<x, y>>
             /\ pc' = "Done"

Spec == Init /\ [][Next]_<<x, y, pc>>

Termination == <>(pc = "Done")

=============================================================================