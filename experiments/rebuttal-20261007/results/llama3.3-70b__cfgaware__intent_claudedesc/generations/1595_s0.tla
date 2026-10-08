---------------------------- MODULE FairCounter ----------------------------
EXTENDS Integers

CONSTANT MaxValue

VARIABLE counter, pc

Init == (counter = 0) ∧ (pc = "Start")

Next == IF pc = "Start" THEN
           IF counter < MaxValue THEN
             counter' = counter + 1
             ∧ pc' = "Increment"
           ELSE
             pc' = "Done"
             ∧ UNCHANGED counter
           END
         ELSE IF pc = "Increment" THEN
                 pc' = "Start"
                 ∧ UNCHANGED counter
              END

Spec == Init ∧ [][Next]_<<counter, pc>>
      ∧ WF_vars(<<Next>>, <<counter, pc>>)

Termination == <>[]((pc = "Done") ∧ (counter = MaxValue))

THEOREM Spec => Termination

=============================================================================