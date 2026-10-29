---------------------------- MODULE ExtendsIntegers ----------------------------
EXTENDS Naturals, Integers

VARIABLE x

vars == << x >>

Init == x = -1

Next == IF x = -3
          THEN UNCHANGED x
          ELSE x' = x - 1

Spec == Init /\ [][Next]_vars

TypeOK == x \in Int

Inv == TRUE

=============================================================================