MODULE PlusCalSpec
EXTENDS Naturals, Sequences

VARIABLES x, y, pc

vars == <<x, y, pc>>

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "Init"

Step ==
    /\ pc = "Init"
    /\ x' = x ∪ { "c" }
    /\ y' = << y[1], 4, y[3] >>
    /\ pc' = "Done"
    /\ Print(x)
    /\ Print(y)

TerminateStutter ==
    /\ pc = "Done"
    /\ x' = x
    /\ y' = y
    /\ pc' = pc

Next == Step \/ TerminateStutter

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")