------------------------------- MODULE ConjunctiveInit -------------------------------
EXTENDS Integers

CONSTANTS 

VARIABLES x, y

Init == /\ y = 0 
        /\ x = 0 
        /\ y = x

Next == TRUE

Spec == Init /\ [][Next]_<<x, y>>

Invariant == /\ x = 0
             /\ y = 0

TypeOK == /\ x \in Integers
          /\ y \in Integers

=============================================================================