```
MODULE SimpleAlgorithm
VARIABLES x, y, pc

Init == (x = {"a", "b"}) /\ (y = <<1, 2, 3>>) /\ (pc = "Start")
Next == IF pc = "Start" THEN
            Lbl_1 == (x' = x \cup {"c"}) /\ (y' = <<y[1], 4, y[3]>>) /\ (pc' = "Done") /\ PrintT("Added c to x: ", x') /\ PrintT("Updated y: ", y')
          ELSE
            Terminating == (x' = x) /\ (y' = y) /\ (pc' = pc)

Spec == Init /\ [][Next]_<<x, y, pc>>
Termination == <>(pc = "Done")
```
Note that the `PrintT` operator is used to print intermediate results as per the problem description. The `Terminating` action allows the system to stutter indefinitely after reaching the `"Done"` state, preventing deadlock on termination.