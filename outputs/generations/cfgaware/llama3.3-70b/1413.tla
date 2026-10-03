--------------------------- MODULE Github790 ---------------------------
EXTENDS Integers

CONSTANT 

VARIABLE a

Init == (a = 0)

Next == (a' = a)

Spec == Init /\ [][Next]_a

AlwaysTrue == <>TRUE => <>[]TRUE

======================================================================