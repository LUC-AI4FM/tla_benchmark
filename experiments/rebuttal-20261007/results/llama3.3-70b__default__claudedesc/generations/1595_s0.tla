```
MODULE Counter
EXTENDS Integers

CONSTANTS 

VARIABLES x, pc

Init == (x = 0) ∧ (pc = "Lbl_1")

Next == IF pc = "Lbl_1" THEN
            IF x < 10 THEN
              x' = x + 1
              ∧ pc' = "Lbl_1"
            ELSE
              pc' = "Done"
              ∧ x' = x
            END
         ELSE 
           (pc = "Done") ∧ (x' = x) ∧ (pc' = "Done")

Terminating == (pc = "Done") ∧ (x' = x) ∧ (pc' = "Done")

Spec == Init ∧ □[Next]_pc ∧ WF_pc(Next)

AtFive == (x = 5)
FinishLoop == (x = 9)

Termination == <> (pc = "Done")

THEOREM Spec => []<> (pc = "Done")
THEOREM Spec => Termination

PossibleCounts == 
  LET CountAtFive == {t \in 0..100 : AtFive[pc <- pc[t], x <- x[t]]}
      CountFinishLoop == {t \in 0..100 : FinishLoop[pc <- pc[t], x <- x[t]]}
  IN Cardinality(CountAtFive) = 1 ∧ Cardinality(CountFinishLoop) = 1
```