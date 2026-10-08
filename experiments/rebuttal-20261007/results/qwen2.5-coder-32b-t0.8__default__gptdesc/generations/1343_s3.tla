---- MODULE TrivialSystem ----

EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES x, y

Init == (x = 0) /\ (y = 0) /\ (x = y)

Next == [](x' = x) /\ [](y' = y)

Spec == Init /\ []Next

====