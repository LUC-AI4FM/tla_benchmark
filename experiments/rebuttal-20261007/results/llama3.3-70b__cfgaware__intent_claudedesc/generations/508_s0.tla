---------------------------- MODULE Spec ----------------------------
EXTENDS Integers

VARIABLE x, done

Init == (x \in 1..10) /\ done = FALSE

Next == done => UNCHANGED <<x, done>> 
       \/ ~done /\ (x \in 1..10) /\ (x * x <= 100) /\ done' = TRUE 

Spec == Init /\ [][Next]_<<x, done>>

THEOREM Spec => [](~done => <>done)
====================================================================