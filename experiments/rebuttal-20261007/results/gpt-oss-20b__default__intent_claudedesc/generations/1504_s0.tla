MODULE TrivialStationary
EXTENDS TLC

VARIABLE v

Init == v = TRUE

Next == /\ v' = v

Spec == Init /\ [][Next]_v

Safety == \Box (\E v': Next)

THEOREM Spec => Safety

===============================================================================