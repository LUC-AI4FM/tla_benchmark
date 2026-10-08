MODULE CounterDemo
EXTENDS Naturals

CONSTANT Bound

VARIABLE counter

Init == counter = 0

Next ==
    /\ counter' = IF counter < Bound THEN counter + 1 ELSE counter

Spec == Init /\ []Next

===============================================================================