------------------------------ MODULE RandomFunctionSampler ------------------------------

EXTENDS Naturals, Integers, FiniteSets

INSTANCE TLC

CONSTANT S

ASSUME /\ S \subseteq Int
       /\ Cardinality(S) = 9

T == 1..10

FS == [ S -> T ]

RandomSubset(k, A) == TLC!RandomSubset(A)

VARIABLES x

Init == x \in RandomSubset(1000, FS)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == TRUE

========================================================================================