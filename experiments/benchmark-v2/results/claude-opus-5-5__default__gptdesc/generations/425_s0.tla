---------------------------- MODULE ExtendsIntegerCounter ----------------------------
EXTENDS Naturals, Integers

VARIABLES x

vars == << x >>

Init == x = -1

Next == x' = IF x = -3 THEN x ELSE x - 1

Spec == Init /\ [][Next]_vars

TypeOK == x \in Int

Inv == TRUE

=====================================================================================