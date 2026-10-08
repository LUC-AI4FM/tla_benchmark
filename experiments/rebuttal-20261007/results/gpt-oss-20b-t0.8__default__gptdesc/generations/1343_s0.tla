MODULE TrivialStutter

VARIABLES x, y

Init == (x = 0) /\ (y = 0)

Next == (x' = x) /\ (y' = y)

Spec == Init /\ [][Next]_<<x,y>>