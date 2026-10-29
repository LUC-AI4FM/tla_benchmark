---- MODULE Counter ----
EXTENDS Naturals, TLC

ASSUME PrintT("IOUtilsTests!C!b!Counter")

CONSTANT UpperBound

VARIABLE x

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_x

Constraint == x < UpperBound

Inv == x < UpperBound

====