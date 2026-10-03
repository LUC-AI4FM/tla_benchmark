---- MODULE OneVarBoolean ----
EXTENDS TLC

VARIABLES x

vars == <<x>>

Init == x = TRUE

XIsTrue == x = TRUE
XIsFalse == x = FALSE

Next == x' = ~x

Spec == Init /\ [][Next]_vars

Prop == []<>XIsTrue
============================