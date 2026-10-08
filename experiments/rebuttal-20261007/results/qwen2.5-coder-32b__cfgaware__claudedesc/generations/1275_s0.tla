------------------------------- MODULE NegInitTest -------------------------------

VARIABLE s

CONSTANTS var

Init(var) == \E v \in {0, 1} : var = v /\ v < 1

Next == TRUE

Spec == Init(s) /\ [][Next]_<<s>>

Inv == s < 1

=============================================================================