------------------------------ MODULE MinimalTautology ------------------------------

EXTENDS Naturals, TemporalOperators

VARIABLES x

Init == x = 0

Next == (x' = x)

Spec == Init /\ [][Next]_<<x>>

AlwaysTrue == <>TRUE => <>[]TRUE

===============================================================================