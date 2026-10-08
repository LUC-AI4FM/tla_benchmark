---- MODULE D ----

VARIABLE x

(*--algorithm D
variables x = 0;

define fact(n) == 
    IF n = 1 THEN 1
    ELSE n * fact(n - 1)
end define;

Next ==
    \/ x' = fact(3)
    \/ x' = fact(9)

Spec ==
    /\ x = 0
    /\ [](x' = x \/ Next)
end algorithm*)
====