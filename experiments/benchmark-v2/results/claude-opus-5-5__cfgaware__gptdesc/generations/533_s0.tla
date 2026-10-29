---------------------------- MODULE MC ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

VARIABLE x

ConstMinValue == -1000

ConstTuples == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

=============================================================================