---- MODULE FactorialStateMachine ----

VARIABLES x

(*--algorithm FactorialStateMachine
variables x \in 0..12;

begin
    Init:
        x := 0;
    while TRUE do
        if x = 0 then
            x := Fact(5)
        else
            x := Fact(3);
end algorithm;*)

\* Recursive definition of factorial
RECURSIVE Fact(_)
Fact(n) == IF n <= 1 THEN 1 ELSE n * Fact(n - 1)

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' = Fact(5)
    \/ /\ x # 0
       /\ x' = Fact(3)

Spec == Init /\ [][Next]_<<x>>

====