------------ MODULE Github702 ------------
EXTENDS Integers

CONSTANT fizzbuzz

VARIABLE y, z

fizzbuzz == 1

Init == (y \in {1,2,3}) /\ (z \in {1,2,3})

Next == y' = y + 1 /\ z' = z

Spec == Init /\ [][Next]_<<y, z>>

=========================================