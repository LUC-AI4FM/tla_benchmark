---------------------------- MODULE Specification ----------------------------

VARIABLE flag

Init == flag = TRUE

Next == flag' = flag

Spec == Init /\ [][Next]_flag /\ WF_flag(Next)

Prop == flag = TRUE

Liveness == []ENABLED(Next)

=============================================================================