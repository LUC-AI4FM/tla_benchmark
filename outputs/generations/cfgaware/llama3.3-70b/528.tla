```
MODULE PlusCalAlgorithm
VARIABLES x, y, pc

Init == (x = {"a", "b"}) /\ (y = <<1, 2, 3>>) /\ (pc = "Start")
Next == IF pc = "Start"
        THEN (x' = x \cup {"c"}) /\ (y' = <<y[1], 4, y[3]]) /\ (pc' = "Done") /\ PrintT(x) /\ PrintT(y)
        ELSE (x' = x) /\ (y' = y) /\ (pc' = pc)

Terminating == (pc' = pc) /\ (x' = x) /\ (y' = y)

Spec == Init /\ [][Next]_<<x, y, pc>> /\ WF_Terminating(<<x, y, pc>>)
```
Note: The `WF_Terminating` operator is used to ensure that the `Terminating` action is taken infinitely often, which models the termination property. Also, note that in TLA+, we use `_` instead of `\` for the stuttering variable list in the `[Next]_vars` formula. 

However, since you want a temporal behavior given by `Spec == Init /\ [][Next]_vars`, I will modify it to match your request.

```
MODULE PlusCalAlgorithm
VARIABLES x, y, pc

Init == (x = {"a", "b"}) /\ (y = <<1, 2, 3>>) /\ (pc = "Start")
Next == IF pc = "Start"
        THEN (x' = x \cup {"c"}) /\ (y' = <<y[1], 4, y[3]]) /\ (pc' = "Done") /\ PrintT(x) /\ PrintT(y)
        ELSE (x' = x) /\ (y' = y) /\ (pc' = pc)

Terminating == (pc = "Done") /\ (pc' = pc) /\ (x' = x) /\ (y' = y)

Spec == Init /\ [][Next]_<<x, y, pc>> 
```