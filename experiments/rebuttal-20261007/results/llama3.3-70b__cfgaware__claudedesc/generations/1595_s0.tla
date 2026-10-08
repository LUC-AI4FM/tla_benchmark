---------------------------- MODULE Counter --------------------------------
EXTENDS Integers

CONSTANTS Done

VARIABLES x, pc

Init == (x = 0) ∧ (pc = "Lbl_1")

Next == IF pc = "Lbl_1" THEN
            IF x < 10 THEN
              x' = x + 1
            ELSE
              pc' = Done
            END
         ELSE
           Terminating
         END

Terminating == pc' = pc ∧ x' = x

Spec == Init ∧ [][Next]_<<x, pc>> ∧ WF_<<x, pc>>(Next)

Termination == <>[]pc = Done

AtFive == x = 5

FinishLoop == (x = 9) ∧ (x' = 10)

PossibleCounts == 
  LET CountAtFive == {t \in 0..(Len(TLC.StateStack)) : AtFive[[TLC.StateStack[t]]]}
      CountFinishLoop == {t \in 0..(Len(TLC.StateStack)) : FinishLoop[[TLC.StateStack[t]]]}
  IN Cardinality(CountAtFive) = 1 ∧ Cardinality(CountFinishLoop) = 1
=============================================================================