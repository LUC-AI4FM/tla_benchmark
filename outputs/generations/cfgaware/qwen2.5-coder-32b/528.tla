------------------------------- MODULE SmallSpec -------------------------------

CONSTANTS vars

VARIABLES x, y, pc

Init == /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
            /\ x' = x \cup {"c"}
            /\ y' = <<y[1], 4, y[3]>>
            /\ pc' = "Done"
          \/ Terminating

Terminating == /\ pc = "Done"
               /\ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_<<x, y, pc>>

=============================================================================