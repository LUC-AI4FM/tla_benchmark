------------------------------ MODULE Tutorial ------------------------------
EXTENDS Naturals, Sequences

VARIABLES x, y, pc

vars == {x, y, pc}

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "Start"

Lbl_1 ==
    /\ pc = "Start"
    /\ x' = PrintT(x \cup {"c"})
    /\ y' = PrintT([j \in 1..Len(y) |-> IF j=2 THEN 4 ELSE y[j]])
    /\ pc' = "Done"

Stutter ==
    /\ pc = "Done"
    /\ x' = x
    /\ y' = y
    /\ pc' = pc

Next == Lbl_1 \/ Stutter

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")

===============================================================================