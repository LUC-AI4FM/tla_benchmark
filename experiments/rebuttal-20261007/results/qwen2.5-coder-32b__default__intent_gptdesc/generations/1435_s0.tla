------------------------------- MODULE ConstantState -------------------------------

EXTENDS Integers, TLC

CONSTANTS State

VARIABLES value

Init == value = 0

Next == TRUE

Spec == Init /\ [][Next]_<<value>>

Inv == value = 0

TypeOK == value \in Integers

SpecWithInvariants == Spec /\ Inv

=============================================================================