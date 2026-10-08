---- MODULE Github790 ----
EXTENDS Naturals

CONSTANTS a

VARIABLES x

Init == x = 0

Next == x' = x

Spec == Init /\ [][Next]_x

AlwaysTrue == <>TRUE => <>[]TRUE

====