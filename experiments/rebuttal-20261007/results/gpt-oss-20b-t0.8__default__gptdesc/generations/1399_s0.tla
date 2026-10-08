MODULE BoolFlip
VARIABLE x

Init  == x = TRUE

Next  == x' = ~x

Stutter == x' = x

Spec == Init /\ [][Next \/ Stutter]_x

XTrue  == x = TRUE
XFalse == x = FALSE