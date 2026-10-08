------------------------------- MODULE SimpleSystem -------------------------------
EXTENDS Integers

CONSTANTS 
    \* No constants needed for this specification

VARIABLES x, y

Init == /\ x = 0
        /\ y = 0
        /\ x = y

Next == \/ /\ x' = x
             /\ y' = y
           \/ /\ x' = x
              /\ y' = y

Spec == Init /\ [][Next]_<<x, y>>

Inv1 == x = y

TypeOK == /\ x \in Integers
          /\ y \in Integers

SpecInit == Init

SpecStable == [](x = x')
            /\ [](y = y')

=============================================================================