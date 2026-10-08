MODULE NonTrivialInit
EXTENDS Integers

VARIABLES x

Init ==
    /\ x \in 0..1
    /\ x < 1

Next ==
    /\ x' = x

Inv == x < 1

Spec == Init /\ [][Next]_<<x>>

THEOREM Inv_Holds : Spec => []Inv