MODULE TrivialSystem
EXTENDS TLC

VARIABLE x

Init == x = 0

Next == (x' = x)

Spec == Init /\ [][Next]_{<<x>>}