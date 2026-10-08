---------------------------- MODULE CounterLoop ----------------------------
EXTENDS Integers

CONSTANT UpperBound
VARIABLE counter, terminated

Init == (counter = 0) /\ (terminated = FALSE)

Next == IF ~terminated THEN
           IF counter < UpperBound THEN
             (* Increment the counter *)
             counter' = counter + 1
           ELSE
             (* Terminate and remain idle *)
             counter' = counter
             terminated' = TRUE
           END
         ELSE
           (* Remain in terminated state *)
           UNCHANGED <<counter, terminated>>
         END

Spec == Init /\ [][Next]_<<counter, terminated>>

Termination == <>[]terminated

THEOREM Spec => []~(counter < 0)
THEOREM Spec => [](counter' = counter + 1) \/ (counter' = counter)
THEOREM Spec => Termination
THEOREM Spec => <><<counter = 5>>_counter
THEOREM Spec => <><<counter = 9>>_counter /\ <<counter' = 10>>_counter

=============================================================================