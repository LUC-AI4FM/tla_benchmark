------------------------------- MODULE ConstantState -------------------------------

CONSTANTS State

VARIABLES value

Init == value = 0

Next == TRUE \* No state changes are possible

Spec == Init /\ [][Next]_<<value>>

TypeOK == value \in Int

Inv == value = 0

THEOREM Spec => []Inv

=============================================================================