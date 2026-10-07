```
MODULE SimpleArithmeticAssertion
EXTENDS Integers

CONSTANTS 

VARIABLES x, pc

Init == (x \in 1..10) /\ (pc = "Lbl_1")

Next == 
  \/ (pc = "Lbl_1") /\ (x^2 <= 100) /\ (pc' = "Done") /\ (x' = x)
  \/ (pc = "Done") /\ (pc' = "Done") /\ (x' = x)

Spec == Init /\ [][Next]_<<x, pc>>
Termination == <>[]<>(pc = "Done")

THEOREM Spec => []Termination
```