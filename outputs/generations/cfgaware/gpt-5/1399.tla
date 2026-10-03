----------------------------- MODULE OneVarBool -----------------------------

VARIABLES x

Init == x = TRUE

Next == x' = ~x

IsTrue == x = TRUE
IsFalse == x = FALSE

Prop == IsTrue \/ IsFalse

Spec == Init /\ [][Next]_x

=============================================================================