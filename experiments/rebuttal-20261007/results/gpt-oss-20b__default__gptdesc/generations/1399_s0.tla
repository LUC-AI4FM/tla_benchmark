------------------------------ MODULE OneVarBool ------------------------------
VARIABLES x

Init == x = TRUE

Next == x' = ~x

Stutter == x' = x

Spec == Init /\ [] (Next \/ Stutter)

IsTrue == x = TRUE
IsFalse == x = FALSE
=============================================================================