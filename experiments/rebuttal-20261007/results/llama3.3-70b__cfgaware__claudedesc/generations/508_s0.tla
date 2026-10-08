```
MODULE SimpleArithmeticAssertion
VARIABLES x, pc

Init == (x \in 1..10) /\ (pc = "Lbl_1")

Next == Lbl_1 \/ Terminating

Lbl_1 == (pc = "Lbl_1") /\ (x^2 <= 100) /\ (pc' = "Done") /\ (x' = x)

Terminating == (pc = "Done") /\ (pc' = "Done") /\ (x' = x)

Spec == Init /\ [][Next]_<<x, pc>>

THEOREM Spec => <>[]pc = "Done"
```
Note: The `THEOREM` statement is included to define the liveness property `Termination`, but it will not be checked in this configuration.