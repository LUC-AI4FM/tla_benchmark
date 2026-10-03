------------------------------- MODULE FactorialStateMachine -------------------------------

VARIABLES x

(*--algorithm FactorialStateMachine
variables x \in Nat;
begin
    A: x := fact(3);
    B: x := fact(9);
end algorithm*)

fact(n) == IF n = 0 THEN 1 ELSE n * fact(n - 1)

Init == x = 0

Next == \/ x' = fact(3)
        \/ x' = fact(9)

Spec == Init /\ [][Next]_<<x>>

=============================================================================