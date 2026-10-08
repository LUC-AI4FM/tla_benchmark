MODULE EvenRange
VARIABLES x

Init == x = 0

Next == \/ (x' \in {0,2,4,6,8})

Spec == Init /\ [][Next]_x