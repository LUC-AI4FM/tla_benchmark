MODULE BooleanFlip
EXTENDS BOOLEAN

VARIABLE x

Init == x = TRUE

Next == (x' = !x)

IsTrue  == (x = TRUE)
IsFalse == (x = FALSE)

Spec == Init /\ [] [][Next]_x

=============================================================================