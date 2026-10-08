MODULE BoolFlip

VARIABLE x

Init == x = TRUE

Next == (x' = ~x)

Stutter == (x' = x)

IsTrue == (x = TRUE)
IsFalse == (x = FALSE)

Spec == Init /\ [][ Next \/ Stutter ]_x

===============================================================================