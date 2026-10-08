```
------------------------------ MODULE SmallPlusCal ------------------------------
EXTENDS Sequences

VARIABLES x, y, pc

Init == /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Init"

DoStep ==
    /\ pc = "Init"
    /\ x' = x \cup {"c"}
    /\ y' = [y EXCEPT ![2] = 4]
    /\ pc' = "Done"

TerminateStutter ==
    /\ pc = "Done"
    /\ x' = x
    /\ y' = y
    /\ pc' = pc

Next == DoStep \/ TerminateStutter

vars == <<x, y, pc>>

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")

THEOREM SpecImpliesTermination : Spec => Termination
```