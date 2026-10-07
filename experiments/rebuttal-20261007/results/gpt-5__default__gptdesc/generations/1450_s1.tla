------------------------------ MODULE RandomFunctionSampler ------------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS S

ASSUME /\ S \subseteq Int
       /\ Cardinality(S) = 9

T == 1..10

VARIABLES x

Min(a, b) == IF a <= b THEN a ELSE b

RandomSubset(k, U) ==
  CHOOSE RS \in SUBSET U : Cardinality(RS) = Min(k, Cardinality(U))

Init ==
  LET RS == RandomSubset(1000, [S -> T])
  IN x \in RS

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == TRUE

=============================================================================