---------------------------- MODULE Counter ----------------------------
EXTENDS Integers

CONSTANT Done

VARIABLE pc, x

Init == (pc = "Start") ∧ (x = 0)

Next == IF pc = "Start" THEN
           pc' = "Loop" ∧ x' = 0
         ELSE IF pc = "Loop" THEN
                  IF x < 10 THEN
                    pc' = "Loop" ∧ x' = x + 1
                  ELSE
                    pc' = "Done" ∧ x' = x
                  END
               ELSE
                 FALSE
               END
       END

Spec == Init ∧ [][Next]_<<pc, x>>
Termination == <>[]pc = Done

AtFive == (x = 5)
FinishLoop == (pc = "Loop") ∧ (x >= 10)

PossibleCounts == 
  LET Counts == {<<"Start", 1>, <"Loop", 10>, <"Done", 1>>}
  IN Counts = [s \in {"Start", "Loop", "Done"} |-> 
               IF s = "Start" THEN 1
               ELSEIF s = "Loop" THEN 10
               ELSE 1]

THEOREM Spec => Termination
=============================================================================