---------------------------- MODULE MC_Session3 ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS minValue, Tuples

VARIABLE result

vars == << result >>

Init == result = minValue

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

ConstMinValue == -100

ConstTuples == [i \in 1..3 |-> -i]

=============================================================================