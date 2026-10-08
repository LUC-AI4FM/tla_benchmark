----------------------------- MODULE FactorialStateMachine -----------------------------

EXTENDS Naturals

CONSTANTS fact

VARIABLES x

Init == x = 0

Next == \/ (x' = fact(3)) 
        \/ (x' = fact(9))

Spec == Init /\ [][<<x>> \in {s \in Nat : s = x} \/ Next]_<<x>>

=============================================================================